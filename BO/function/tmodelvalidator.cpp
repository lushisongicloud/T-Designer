#include "BO/function/tmodelvalidator.h"
#include "BO/function/tmodelparser.h"

#include <QMap>
#include <QRegularExpression>
#include <QStringList>

namespace {

QString portKey(const PortInfo &info)
{
    // 新规范：变量定义不再包含功能子块名，只使用端号本身。
    // 若历史数据 functionBlock 不为空且端号未包含该前缀，不在此添加，保持与生成声明格式一致。
    QString port = info.connNum.trimmed();
    return port; // 直接返回端号
}

QString normalizePortToken(const QString &rawPath)
{
    QString normalized = rawPath.trimmed();
    if (normalized.startsWith(QLatin1Char('.')))
        normalized.remove(0, 1);
    if (normalized.endsWith(QLatin1Char('.')))
        normalized.chop(1);
    return normalized;
}

QString normalizeDirection(const QString &suffix)
{
    const QString trimmed = suffix.trimmed();
    if (trimmed.compare(QStringLiteral("F"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("F");
    if (trimmed.compare(QStringLiteral("I"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("i");
    if (trimmed.compare(QStringLiteral("U"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("u");
    if (trimmed.compare(QStringLiteral("P"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("p");
    if (trimmed.compare(QStringLiteral("Q"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("q");
    if (trimmed.compare(QStringLiteral("V"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("v");
    if (trimmed.compare(QStringLiteral("N"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("n");
    if (trimmed.compare(QStringLiteral("X"), Qt::CaseInsensitive) == 0)
        return QStringLiteral("x");
    return trimmed;
}

struct ExpectedDirectionSpec
{
    QSet<QString> required;
    QSet<QString> optionalAnyOf;
    QString optionalLabel;
    QStringList displayOrder;
};

ExpectedDirectionSpec expectedSpecForPort(const PortInfo &info)
{
    ExpectedDirectionSpec spec;
    QStringList configured = info.variableNames;
    for (QString &entry : configured)
        entry = entry.trimmed();
    configured.removeAll(QString());

    if (!configured.isEmpty()) {
        for (const QString &var : configured) {
            const QString normalized = normalizeDirection(var);
            if (!normalized.isEmpty()) {
                spec.required.insert(normalized);
                spec.displayOrder.append(var.trimmed());
            }
        }
        return spec;
    }

    const QString type = info.portType.trimmed().toLower();
    if (type == QStringLiteral("hydraulic")) {
        spec.required.insert(QStringLiteral("p"));
        spec.required.insert(QStringLiteral("q"));
        spec.displayOrder = QStringList{QStringLiteral("p"), QStringLiteral("q")};
        return spec;
    }

    if (type == QStringLiteral("mechanical")) {
        spec.required.insert(QStringLiteral("F"));
        spec.optionalAnyOf = QSet<QString>{
            QStringLiteral("v"),
            QStringLiteral("n"),
            QStringLiteral("x")
        };
        spec.optionalLabel = QStringLiteral("v/n/x");
        spec.displayOrder = QStringList{QStringLiteral("F"), QStringLiteral("v")};
        return spec;
    }

    if (type == QStringLiteral("other")) {
        return spec;
    }

    // default: electric
    spec.required.insert(QStringLiteral("i"));
    spec.required.insert(QStringLiteral("u"));
    spec.displayOrder = QStringList{QStringLiteral("i"), QStringLiteral("u")};
    return spec;
}

QString formatPortVariableName(const QString &portName, const QString &direction)
{
    if (direction.isEmpty())
        return portName;
    return QString("%1.%2").arg(portName, direction);
}

bool directionMatchesOptionalGroup(const QSet<QString> &optionalGroup, const QString &direction)
{
    if (optionalGroup.isEmpty())
        return false;
    return optionalGroup.contains(direction);
}

bool isDirectionAllowed(const PortVariableBinding &binding, const QString &direction)
{
    if (binding.expectedDirections.contains(direction))
        return true;
    if (directionMatchesOptionalGroup(binding.alternativeDirections, direction))
        return true;
    if (binding.expectedDirections.isEmpty() && binding.alternativeDirections.isEmpty())
        return true;
    return false;
}

}

TModelValidationResult TModelValidator::validate(const QString &tmodelText,
                                                const QList<PortInfo> &ports,
                                                const TModelValidationContext &context) const
{
    TModelValidationResult result;
    
    // 1. 检查器件名称占位符
    if (!context.componentName.isEmpty()) {
        // 检查是否使用了%Name%占位符
        QRegularExpression namePattern(QStringLiteral("%Name%"));
        if (!namePattern.match(tmodelText).hasMatch()) {
            result.formatErrors << QString("T语言模型中应使用 %Name% 作为器件名称占位符");
        }
        
        // 检查是否错误地使用了具体器件名称而非占位符
        if (!context.componentName.isEmpty() && context.componentName != "COMPONENT") {
            QRegularExpression concreteNamePattern(
                QString("\\b%1\\.").arg(QRegularExpression::escape(context.componentName)));
            if (concreteNamePattern.match(tmodelText).hasMatch()) {
                result.formatErrors << QString("T语言模型中不应直接使用具体器件名称 \"%1\"，请使用 %Name% 占位符")
                    .arg(context.componentName);
            }
        }
    }
    
    // 2. 检查常量定义
    if (!context.constants.isEmpty()) {
        // 从T语言模型中提取所有常量占位符
        QStringList usedConstants = TModelParser::extractConstants(tmodelText);
        
        for (const QString &constantName : usedConstants) {
            if (!context.constants.contains(constantName)) {
                result.formatErrors << QString("常量 \"%1\" 在T语言模型中使用但未在常量表格中定义")
                    .arg(constantName);
            }
        }
    }
    
    // 4. 检查模型结构完整性
    TModelParser parser;
    if (!parser.parse(tmodelText)) {
        result.formatErrors << QString("T语言模型结构解析失败，无法识别必需的部分标记");
    } else {
        // 检查是否有端口变量定义部分
        QString portVars = parser.getPortVariables();
        if (portVars.trimmed().isEmpty() && !ports.isEmpty()) {
            result.warnings << QString("缺少 \";;端口变量定义\" 部分或该部分为空");
        }
        
        // 检查是否有正常模式
        QString normalMode = parser.getNormalMode();
        if (normalMode.trimmed().isEmpty()) {
            result.warnings << QString("缺少 \";;正常模式\" 部分或该部分为空");
        }
        
        // 可选：检查是否有故障模式部分的标记
        QList<TModelParser::FailureMode> failureModes = parser.getFailureModes();
        // 故障模式是可选的，所以只是统计
        if (!failureModes.isEmpty()) {
            result.hints << QString("检测到 %1 个故障模式").arg(failureModes.size());
        }
    }
    
    // 5. 检查故障模式概率定义
    if (!context.faultModeProbabilities.isEmpty()) {
        TModelParser parser2;
        if (parser2.parse(tmodelText)) {
            QList<TModelParser::FailureMode> failureModes = parser2.getFailureModes();
            for (const TModelParser::FailureMode &fm : failureModes) {
                if (!fm.name.isEmpty() && !context.faultModeProbabilities.contains(fm.name)) {
                    result.warnings << QString("故障模式 \"%1\" 的概率未在维修信息表格中定义")
                        .arg(fm.name);
                }
            }
        }
    }
    
    // 3. 端口变量一致性检查（保留原有逻辑）
    if (ports.isEmpty()) {
        result.formatErrors << QString("未检测到任何端号，无法执行端口映射校验");
        return result;
    }

    QMap<QString, PortVariableBinding> bindingMap;
    for (const PortInfo &info : ports) {
        if (info.connNum.trimmed().isEmpty())
            continue;
        const QString key = portKey(info);
        if (key.isEmpty())
            continue;
        PortVariableBinding binding;
        binding.port = info;
        const ExpectedDirectionSpec spec = expectedSpecForPort(info);
        binding.expectedDirections = spec.required;
        binding.alternativeDirections = spec.optionalAnyOf;
        binding.alternativeLabel = spec.optionalLabel;
        binding.expectedDisplayOrder = spec.displayOrder;
        bindingMap.insert(key, binding);
    }

    if (bindingMap.isEmpty()) {
        result.formatErrors << QString("端号字段全部为空，无法生成映射");
        return result;
    }

    const QString normalized = tmodelText;

    QRegularExpression varPattern(
        QString("(?:%[A-Za-z0-9_]+%|[A-Za-z0-9_]+)\\.((?:[A-Za-z0-9_\\-]+\\.)*[A-Za-z0-9_\\-]+)\\.([A-Za-z0-9_\\-]+)\\b"));
    auto varMatchIter = varPattern.globalMatch(normalized);
    while (varMatchIter.hasNext()) {
        const QRegularExpressionMatch match = varMatchIter.next();
        const QString portPath = normalizePortToken(match.captured(1));
        const QString direction = normalizeDirection(match.captured(2));
        const QString token = match.captured(0);

        if (bindingMap.contains(portPath)) {
            PortVariableBinding &binding = bindingMap[portPath];
            if (isDirectionAllowed(binding, direction)) {
                binding.referencedDirections.insert(direction);
                binding.tokens.insert(token);
            } else {
                result.undefinedVariables.append(token);
            }
        } else {
            result.undefinedVariables.append(token);
        }
    }

    QRegularExpression declPattern(
        QString("\\(\\s*declare-fun\\s+(?:%[A-Za-z0-9_]+%|[A-Za-z0-9_]+)"
                       "\\.((?:[A-Za-z0-9_\\-]+\\.)*[A-Za-z0-9_\\-]+)\\.([A-Za-z0-9_\\-]+)\\s*\\("));
    auto declIter = declPattern.globalMatch(normalized);
    while (declIter.hasNext()) {
        const QRegularExpressionMatch match = declIter.next();
        const QString portPath = normalizePortToken(match.captured(1));
        const QString direction = normalizeDirection(match.captured(2));
        const QString token = match.captured(0);

        if (bindingMap.contains(portPath)) {
            PortVariableBinding &binding = bindingMap[portPath];
            if (isDirectionAllowed(binding, direction)) {
                binding.declaredDirections.insert(direction);
                binding.tokens.insert(token);
            } else {
                result.undefinedVariables.append(token);
            }
        } else {
            result.undefinedVariables.append(token);
        }
    }

    for (auto it = bindingMap.begin(); it != bindingMap.end(); ++it) {
        const QString portName = it.key();
        PortVariableBinding binding = it.value();

        for (const QString &direction : binding.expectedDirections) {
            if (!binding.declaredDirections.contains(direction)) {
                result.missingDeclarations.append(
                    formatPortVariableName(portName, direction));
            }
        }

        if (!binding.alternativeDirections.isEmpty()) {
            bool satisfied = false;
            for (const QString &direction : binding.alternativeDirections) {
                if (binding.declaredDirections.contains(direction)) {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) {
                const QString label = binding.alternativeLabel.isEmpty()
                        ? binding.alternativeDirections.values().join(QStringLiteral("/"))
                        : binding.alternativeLabel;
                result.missingDeclarations.append(
                    formatPortVariableName(portName, label));
            }
        }

        if (binding.referencedDirections.isEmpty()) {
            result.unusedPorts.append(portName);
        }

        result.bindings.append(binding);
    }

    result.undefinedVariables.removeDuplicates();
    result.missingDeclarations.removeDuplicates();
    result.unusedPorts.removeDuplicates();

    if (!result.unusedPorts.isEmpty()) {
        result.hints.append(QString("以下端号未在T语言中引用：%1")
                                .arg(result.unusedPorts.join(QString(", "))));
    }

    return result;
}
