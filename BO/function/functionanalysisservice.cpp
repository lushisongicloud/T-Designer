#include "BO/function/functionanalysisservice.h"

#include <QSqlQuery>
#include <QSqlError>
#include <QObject>
#include <QSet>

#include "common.h"

FunctionAnalysisService::FunctionAnalysisService(const QSqlDatabase &db)
    : m_db(db)
{
}

FunctionModelResult FunctionAnalysisService::analyzeSymbol(int symbolId, const QString &functionNameHint) const
{
    FunctionModelResult result;
    if (!m_db.isValid() || !m_db.isOpen() || symbolId <= 0) {
        result.warnings.append(QObject::tr("数据库未就绪或符号无效"));
        return result;
    }

    QSqlQuery symbolQuery(m_db);
    symbolQuery.prepare(QStringLiteral("SELECT Symbol_ID, Show_DT, Equipment_ID FROM Symbol WHERE Symbol_ID = :sid"));
    symbolQuery.bindValue(QStringLiteral(":sid"), symbolId);
    if (!symbolQuery.exec() || !symbolQuery.next()) {
        result.warnings.append(QObject::tr("未找到符号 %1").arg(symbolId));
        return result;
    }

    const QString symbolDisplay = symbolQuery.value(1).toString().trimmed();
    const QString componentName = GetComponentDTBySymbolID(QString::number(symbolId), 0);

    result.record.symbolId = symbolId;
    result.record.symbolName = symbolDisplay.isEmpty() ? componentName : symbolDisplay;
    result.record.name = defaultFunctionName(result.record.symbolName, componentName, functionNameHint);

    QStringList execs;
    QSqlQuery portQuery(m_db);
    portQuery.prepare(QStringLiteral("SELECT ConnNum FROM Symb2TermInfo WHERE Symbol_ID = :sid ORDER BY Symb2TermInfo_ID"));
    portQuery.bindValue(QStringLiteral(":sid"), symbolId);
    if (portQuery.exec()) {
        while (portQuery.next()) {
            const QString port = portQuery.value(0).toString().trimmed();
            if (port.isEmpty()) continue;
            if (!componentName.isEmpty())
                execs.append(QStringLiteral("%1.%2").arg(componentName, port));
            else
                execs.append(port);
        }
    } else {
        result.warnings.append(QObject::tr("读取符号端口失败: %1").arg(portQuery.lastError().text()));
    }

    if (execs.isEmpty()) {
        if (!componentName.isEmpty())
            execs.append(componentName);
        else if (!result.record.symbolName.isEmpty())
            execs.append(result.record.symbolName);
    }
    result.record.execsList = execs.join(',');

    const QString linkRoad = GetLinkRoadBySymbol(symbolId);
    QStringList components = extractComponentNames(linkRoad);
    if (!componentName.isEmpty() && !components.contains(componentName))
        components.prepend(componentName);
    if (components.isEmpty() && !componentName.isEmpty())
        components.append(componentName);

    result.record.link = components.join(',');
    result.record.componentDependency = result.record.link;
    result.record.allComponents = result.record.link;
    result.record.functionDependency.clear();
    result.record.persistent = true;
    result.record.faultProbability = 0.0;
    result.record.remark.clear();
    result.record.cmdValList.clear();

    result.linkSequence = components;
    if (linkRoad.trimmed().isEmpty())
        result.warnings.append(QObject::tr("未能分析出链路信息，已使用默认器件集合。"));

    return result;
}

QStringList FunctionAnalysisService::extractComponentNames(const QString &linkRoad) const
{
    QStringList components;
    QSet<QString> seen;
    int position = 0;
    while (position >= 0) {
        int left = linkRoad.indexOf('[', position);
        if (left < 0) break;
        int right = linkRoad.indexOf(']', left + 1);
        if (right < 0) break;

        const QString segment = linkRoad.mid(left + 1, right - left - 1);
        const QStringList nodes = segment.split(';', QString::SkipEmptyParts);
        for (const QString &node : nodes) {
            const QStringList parts = node.split(',', QString::SkipEmptyParts);
            if (parts.size() < 2) continue;
            bool ok = false;
            const int type = parts.at(1).toInt(&ok);
            if (!ok || type != 0) continue;
            const QString comp = GetComponentDTBySymbolID(parts.at(0), type);
            if (comp.isEmpty()) continue;
            if (!seen.contains(comp)) {
                seen.insert(comp);
                components.append(comp);
            }
        }
        position = right + 1;
    }
    return components;
}

QString FunctionAnalysisService::defaultFunctionName(const QString &symbolName, const QString &componentName, const QString &hint) const
{
    if (!hint.trimmed().isEmpty()) return hint.trimmed();
    if (!symbolName.trimmed().isEmpty()) return symbolName.trimmed();
    if (!componentName.trimmed().isEmpty()) return componentName.trimmed();
    return QObject::tr("新功能");
}
