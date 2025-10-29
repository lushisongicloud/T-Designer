#include "BO/function/tmodelvalidator.h"

#include <QMap>
#include <QRegularExpression>

namespace {

QString portKey(const PortInfo &info)
{
    return info.connNum.trimmed();
}

}

TModelValidationResult TModelValidator::validate(const QString &tmodelText,
                                                const QList<PortInfo> &ports) const
{
    TModelValidationResult result;
    if (ports.isEmpty()) {
        result.formatErrors << QString("未检测到任何端号，无法执行端口映射校验。");
        return result;
    }

    QMap<QString, PortVariableBinding> bindingMap;
    for (const PortInfo &info : ports) {
        if (info.connNum.trimmed().isEmpty())
            continue;
        PortVariableBinding binding;
        binding.port = info;
        bindingMap.insert(portKey(info), binding);
    }

    if (bindingMap.isEmpty()) {
        result.formatErrors << QString("端号字段全部为空，无法生成映射。");
        return result;
    }

    const QString normalized = tmodelText;

    QRegularExpression varPattern(
        QString("(?:%[A-Za-z0-9_]+%|[A-Za-z0-9_]+)\\.([A-Za-z0-9_\\-]+)\\.(i|u)\\b"));
    auto varMatchIter = varPattern.globalMatch(normalized);
    while (varMatchIter.hasNext()) {
        const QRegularExpressionMatch match = varMatchIter.next();
        const QString portName = match.captured(1);
        const QString direction = match.captured(2);
        const QString token = match.captured(0);

        if (bindingMap.contains(portName)) {
            PortVariableBinding &binding = bindingMap[portName];
            binding.referencedDirections.insert(direction);
            binding.tokens.insert(token);
        } else {
            result.undefinedVariables.append(token);
        }
    }

    QRegularExpression declPattern(
        QString("\\(\\s*declare-fun\\s+(?:%[A-Za-z0-9_]+%|[A-Za-z0-9_]+)"
                       "\\.([A-Za-z0-9_\\-]+)\\.(i|u)\\s*\\("));
    auto declIter = declPattern.globalMatch(normalized);
    while (declIter.hasNext()) {
        const QRegularExpressionMatch match = declIter.next();
        const QString portName = match.captured(1);
        const QString direction = match.captured(2);
        const QString token = match.captured(0);

        if (bindingMap.contains(portName)) {
            PortVariableBinding &binding = bindingMap[portName];
            binding.declaredDirections.insert(direction);
            binding.tokens.insert(token);
        } else {
            result.undefinedVariables.append(token);
        }
    }

    static const QStringList requiredDirections{QString("u"), QString("i")};
    for (auto it = bindingMap.begin(); it != bindingMap.end(); ++it) {
        const QString portName = it.key();
        PortVariableBinding binding = it.value();

        for (const QString &direction : requiredDirections) {
            if (!binding.declaredDirections.contains(direction)) {
                result.missingDeclarations.append(
                    QString("%1.%2").arg(portName, direction));
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

