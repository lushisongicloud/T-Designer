#include "function_catalog.h"

#include <QDomDocument>
#include <QDomElement>
#include <QRegularExpression>
#include <QSet>
#include <QtCore/Qt>
#include <QDebug>

#include "BO/componententity.h"
#include "BO/function/function_variable_config.h"

namespace testability {

namespace {

QString componentNameFromVariable(const QString &variable)
{
    if (variable.startsWith('.')) {
        return {};
    }
    const int dotIndex = variable.indexOf('.');
    if (dotIndex == -1) {
        return variable;
    }
    return variable.left(dotIndex);
}

TestItem buildTestItem(const QDomElement &constraintElement)
{
    TestItem item;
    item.variable = constraintElement.firstChildElement(QString("variable")).text().trimmed();
    item.value = constraintElement.firstChildElement(QString("value")).text().trimmed();
    item.confidence = constraintElement.firstChildElement(QString("confidence")).text().trimmed().toDouble();
    item.testType = constraintElement.firstChildElement(QString("type")).text().simplified();
    item.checkState = item.testType.contains(QString("执行器")) ? Qt::Checked : Qt::Unchecked;
    return item;
}

QStringList parseComponentList(const QString &text)
{
    QString normalized = text;
    normalized.replace('\n', ',');
    normalized.replace('\r', ',');
    const QStringList rawParts = normalized.split(QLatin1Char(','), QString::SkipEmptyParts);

    QSet<QString> seen;
    QStringList result;
    for (const QString &part : rawParts) {
        const QString trimmed = part.trimmed();
        if (trimmed.isEmpty()) {
            continue;
        }
        if (!seen.contains(trimmed)) {
            result.append(trimmed);
            seen.insert(trimmed);
        }
    }
    return result;
}

} // namespace

QMap<QString, FunctionInfo> FunctionCatalog::parse(const QString &functionDescriptionXml)
{
    QMap<QString, FunctionInfo> functionMap;
    if (functionDescriptionXml.trimmed().isEmpty()) {
        return functionMap;
    }

    QDomDocument doc;
    if (!doc.setContent(functionDescriptionXml)) {
        return functionMap;
    }

    const QDomNodeList functionNodes = doc.elementsByTagName(QString("functiondefine"));
    for (int i = 0; i < functionNodes.size(); ++i) {
        const QDomElement functionElement = functionNodes.at(i).toElement();
        FunctionInfo info;
        info.functionName = functionElement.firstChildElement(QString("name")).text().trimmed();
        info.link = functionElement.firstChildElement(QString("link")).text().trimmed();
        info.linkElements.clear();
        const QStringList linkTokens = info.link.split(',', QString::SkipEmptyParts);
        for (const QString &token : linkTokens) {
            const QString trimmed = token.trimmed();
            if (!trimmed.isEmpty()) {
                info.linkElements.append(trimmed);
            }
        }

        QDomElement dependency = functionElement.firstChildElement(QString("dependency"));
        if (!dependency.isNull()) {
            info.componentDependency = dependency.firstChildElement(QString("component")).text().trimmed();
            info.allRelatedComponent = dependency.firstChildElement(QString("allComponent")).text().trimmed();
            info.functionDependency = dependency.firstChildElement(QString("function")).text().trimmed();
            info.allComponentList = parseComponentList(info.allRelatedComponent);
            if (info.allComponentList.isEmpty()) {
                info.allComponentList = parseComponentList(info.componentDependency);
            }
            qDebug().noquote() << "[FunctionCatalog] allComponent raw for" << info.functionName
                               << ":" << info.allRelatedComponent;
            qDebug().noquote() << "[FunctionCatalog] allComponent list for" << info.functionName
                               << ":" << info.allComponentList;
        }

        const QString attribute = functionElement.firstChildElement(QString("attribute")).text().trimmed();
        const QStringList attributeParts = attribute.split(',', QString::SkipEmptyParts);
        if (attributeParts.size() >= 2) {
            info.persistent = attributeParts.at(0).trimmed() != QString("NotPersistent");
            info.faultProbability = attributeParts.at(1).trimmed().toDouble();
        }

        info.constraintIntegrity = functionElement.firstChildElement(QString("constraintIntegrity")).text().trimmed();
        info.variableConfigXml.clear();
        const QDomElement variableConfigElement = functionElement.firstChildElement(QString("variableValueConfig"));
        if (!variableConfigElement.isNull()) {
            QDomDocument fragment;
            QDomElement root = fragment.createElement(QString("root"));
            fragment.appendChild(root);
            root.appendChild(variableConfigElement.cloneNode(true));
            info.variableConfigXml = fragment.toString();
            info.variableConfig = functionvalues::FunctionVariableConfig::fromXml(variableConfigElement);
        }

        info.offlineResults.clear();
        const QDomNodeList offlineNodes = functionElement.elementsByTagName(QString("offlineSolveResult"));
        for (int nodeIndex = 0; nodeIndex < offlineNodes.size(); ++nodeIndex) {
            const QDomElement offlineElement = offlineNodes.at(nodeIndex).toElement();
            FunctionOfflineResult entry;
            const QString componentText = offlineElement.firstChildElement(QString("componentNames")).text();
            const QString failureText = offlineElement.firstChildElement(QString("failureModes")).text();
            const QString probabilityText = offlineElement.firstChildElement(QString("probability")).text();

            const QStringList componentParts = componentText.split(',', QString::SkipEmptyParts);
            for (const QString &componentPart : componentParts) {
                const QString trimmed = componentPart.trimmed();
                if (!trimmed.isEmpty()) {
                    entry.componentNames.append(trimmed);
                }
            }
            const QStringList failureParts = failureText.split(',', QString::SkipEmptyParts);
            for (const QString &failurePart : failureParts) {
                const QString trimmed = failurePart.trimmed();
                if (!trimmed.isEmpty()) {
                    entry.failureModes.append(trimmed);
                }
            }
            bool okProbability = false;
            entry.probability = probabilityText.trimmed().toDouble(&okProbability);
            if (!okProbability) {
                entry.probability = 0.0;
            }
            if (!entry.componentNames.isEmpty() || !entry.failureModes.isEmpty()) {
                info.offlineResults.append(entry);
            }
        }

        QList<TestItem> items;
        const QString actuatorKeyword = QString("执行器");
        bool actuatorSelected = false;
        bool hasFallbackCandidate = false;
        TestItem fallbackCandidate;
        QDomElement constraintElement = functionElement.firstChildElement(QString("constraint"));
        while (!constraintElement.isNull()) {
            TestItem item = buildTestItem(constraintElement);
            qDebug().noquote() << "[FunctionCatalog] constraint parsed for" << info.functionName
                               << "variable=" << item.variable
                               << "type=" << item.testType
                               << "value=" << item.value
                               << "len=" << item.testType.length();
            items.append(item);

            const bool matchesTypeKeyword = item.testType.contains(actuatorKeyword);

            if (!actuatorSelected && matchesTypeKeyword) {
                info.actuatorConstraint = item;
                info.actuatorName = componentNameFromVariable(item.variable);
                actuatorSelected = true;
                qDebug().noquote() << "[FunctionCatalog] selected actuator by direct match for"
                                   << info.functionName << ":" << item.variable;
            }

            if (!hasFallbackCandidate) {
                fallbackCandidate = item;
                hasFallbackCandidate = true;
            }
            constraintElement = constraintElement.nextSiblingElement(QString("constraint"));
        }
        info.constraintList = items;

        if (!actuatorSelected && hasFallbackCandidate) {
            info.actuatorConstraint = fallbackCandidate;
            info.actuatorName = componentNameFromVariable(fallbackCandidate.variable);
            actuatorSelected = true;
            qDebug().noquote() << "[FunctionCatalog] fallback actuator (first constraint) for"
                               << info.functionName << ":" << fallbackCandidate.variable;
        }

        if (info.actuatorConstraint.testType.isEmpty()) {
            qDebug().noquote() << "[FunctionCatalog] WARN no actuator constraint detected for"
                               << info.functionName;
        } else {
            qDebug().noquote() << "[FunctionCatalog] actuator for" << info.functionName
                               << ":" << info.actuatorConstraint.variable
                               << "value=" << info.actuatorConstraint.value
                               << "type=" << info.actuatorConstraint.testType;
        }

        if (info.allComponentList.isEmpty()) {
            info.allComponentList = info.linkElements;
        }

        functionMap.insert(info.functionName, info);
    }

    return functionMap;
}

} // namespace testability
