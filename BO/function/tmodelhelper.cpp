#include "tmodelhelper.h"
#include "tmodelparser.h"
#include <QTableWidgetItem>
#include <QDebug>
#include <QRegularExpression>

QString TModelHelper::generatePortVariablesFromTable(QTableWidget *tableTerm, const QString &componentName)
{
    if (!tableTerm) {
        return QString();
    }

    QString result;
    QSet<QString> generatedVars;  // 避免重复声明

    for (int row = 0; row < tableTerm->rowCount(); ++row) {
        // 列：子块代号(0)、端号(1)、描述(2)、变量(3)、测试代价(4)、已标注(5)、图片路径(6)
        QString portNum = tableTerm->item(row, 1) ? tableTerm->item(row, 1)->text().trimmed() : QString();
        QString variables = tableTerm->item(row, 3) ? tableTerm->item(row, 3)->text().trimmed() : QString();

        if (portNum.isEmpty() || variables.isEmpty()) {
            continue; // 端号或变量集为空则跳过
        }

        // 变量可能是多个，用逗号或分号分隔
        QStringList varList = variables.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);

        // 去掉可能的多余空白和重复变量
        for (QString &v : varList) v = v.trimmed();
        varList.removeAll(QString());
        varList.removeDuplicates();

        // 端号本身可能带层次，如 Cmd.A1；按照新规范不再插入功能子块列，只使用端号的原始分段
        QString fullPath = portNum; // 直接使用端号字段

        for (const QString &var : varList) {
            QString fullVarName = QString("%1.%2.%3").arg(componentName, fullPath, var);
            if (!generatedVars.contains(fullVarName)) {
                result += QString("(declare-fun %1 () Real)\n").arg(fullVarName);
                generatedVars.insert(fullVarName);
            }
        }
    }

    return result.trimmed();
}

QStringList TModelHelper::extractFaultModesFromTModel(const QString &tmodelText)
{
    TModelParser parser;
    if (!parser.parse(tmodelText)) {
        return QStringList();
    }
    
    const QList<TModelParser::FailureMode> &failureModes = parser.getFailureModes();
    QStringList faultNames;
    
    for (const TModelParser::FailureMode &fm : failureModes) {
        if (!fm.name.isEmpty()) {
            faultNames.append(fm.name);
        }
    }
    
    return faultNames;
}

QString TModelHelper::updatePortVariablesInTModel(const QString &tmodelText, const QString &newPortVariables)
{
    QStringList lines = tmodelText.split('\n');
    QString result;
    bool inPortSection = false;
    bool portSectionFound = false;
    
    for (const QString &line : lines) {
        QString trimmed = line.trimmed();
        
        if (trimmed == ";;端口变量定义") {
            portSectionFound = true;
            inPortSection = true;
            result += line + "\n";
            result += newPortVariables;
            if (!newPortVariables.isEmpty() && !newPortVariables.endsWith('\n')) {
                result += "\n";
            }
            continue;
        }
        
        // 检测其他部分的开始标记
        if (inPortSection && trimmed.startsWith(";;") && 
            (trimmed == ";;内部变量定义" || trimmed == ";;正常模式" || 
             trimmed == ";;故障模式" || trimmed == ";;公共开始" || trimmed.startsWith(";;故障模式名"))) {
            inPortSection = false;
        }
        
        // 如果不在端口部分，追加原始行
        if (!inPortSection) {
            result += line + "\n";
        }
    }
    
    // 如果没有找到端口变量定义部分，在开头添加
    if (!portSectionFound) {
        QString header = ";;端口变量定义\n" + newPortVariables;
        if (!newPortVariables.isEmpty() && !newPortVariables.endsWith('\n')) {
            header += "\n";
        }
        header += "\n";
        result = header + result;
    }
    
    return result;
}

QMap<QString, QStringList> TModelHelper::parseRepairInfo(const QString &repairInfoStr)
{
    QMap<QString, QStringList> faultMap;
    
    if (repairInfoStr.isEmpty()) {
        qDebug() << "[TModelHelper::parseRepairInfo] 输入为空";
        return faultMap;
    }
    
    // 新格式：JSON数组 [{"fault":"故障模式","prob":"概率","solution":"方案","resource":"资源"}, ...]
    QJsonParseError parseError;
    QJsonDocument doc = QJsonDocument::fromJson(repairInfoStr.toUtf8(), &parseError);
    
    if (parseError.error != QJsonParseError::NoError) {
        qDebug() << "[TModelHelper::parseRepairInfo] JSON解析失败:" << parseError.errorString();
        qDebug() << "[TModelHelper::parseRepairInfo] 检测到旧格式数据，将被清空";
        // 返回空映射，后续保存时会清空数据库中的旧数据
        return faultMap;
    }
    
    if (!doc.isArray()) {
        qDebug() << "[TModelHelper::parseRepairInfo] JSON格式错误：不是数组";
        return faultMap;
    }
    
    QJsonArray array = doc.array();
    qDebug() << "[TModelHelper::parseRepairInfo] 成功解析JSON数组，包含" << array.size() << "条记录";
    
    for (int i = 0; i < array.size(); ++i) {
        if (!array[i].isObject()) {
            qDebug() << "[TModelHelper::parseRepairInfo] 警告：记录" << i << "不是对象，跳过";
            continue;
        }
        
        QJsonObject obj = array[i].toObject();
        QString faultMode = obj.value("fault").toString().trimmed();
        QString probability = obj.value("prob").toString().trimmed();
        QString solution = obj.value("solution").toString().trimmed();
        QString resource = obj.value("resource").toString().trimmed();
        
        qDebug() << "[TModelHelper::parseRepairInfo] 记录" << i << ": 故障模式=" << faultMode;
        
        if (!faultMode.isEmpty()) {
            QStringList info;
            info << probability << solution << resource;
            faultMap[faultMode] = info;
        } else {
            qDebug() << "[TModelHelper::parseRepairInfo] 警告：记录" << i << "故障模式为空，跳过";
        }
    }
    
    qDebug() << "[TModelHelper::parseRepairInfo] 最终解析出" << faultMap.size() << "条有效记录";
    return faultMap;
}

QString TModelHelper::serializeRepairInfo(const QMap<QString, QStringList> &faultMap)
{
    // 新格式：JSON数组 [{"fault":"故障模式","prob":"概率","solution":"方案","resource":"资源"}, ...]
    QJsonArray array;
    
    for (auto it = faultMap.begin(); it != faultMap.end(); ++it) {
        QString faultMode = it.key();
        const QStringList &info = it.value();
        
        QString probability = info.count() > 0 ? info[0] : "";
        QString solution = info.count() > 1 ? info[1] : "";
        QString resource = info.count() > 2 ? info[2] : "";
        
        QJsonObject obj;
        obj["fault"] = faultMode;
        obj["prob"] = probability;
        obj["solution"] = solution;
        obj["resource"] = resource;
        
        array.append(obj);
    }
    
    QJsonDocument doc(array);
    // 使用紧凑格式，不使用缩进，减小数据量
    QString result = QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
    
    qDebug() << "[TModelHelper::serializeRepairInfo] 序列化" << faultMap.size() << "条记录，结果长度:" << result.length();
    
    return result;
}

void TModelHelper::loadRepairInfoToTable(QTableWidget *tableRepairInfo, const QString &repairInfoStr)
{
    if (!tableRepairInfo) {
        qDebug() << "[TModelHelper::loadRepairInfoToTable] tableRepairInfo is null";
        return;
    }
    
    qDebug() << "[TModelHelper::loadRepairInfoToTable] RepairInfo长度:" << repairInfoStr.length();
    qDebug() << "[TModelHelper::loadRepairInfoToTable] RepairInfo内容:" << repairInfoStr;
    
    tableRepairInfo->setRowCount(0);
    
    QMap<QString, QStringList> faultMap = parseRepairInfo(repairInfoStr);
    
    qDebug() << "[TModelHelper::loadRepairInfoToTable] 解析出" << faultMap.size() << "条故障记录";
    
    int row = 0;
    for (auto it = faultMap.begin(); it != faultMap.end(); ++it) {
        tableRepairInfo->insertRow(row);
        
        // 列：故障模式(0)、故障概率(1)、解决方案(2)、所需资源(3)
        QTableWidgetItem *item0 = new QTableWidgetItem(it.key());
        tableRepairInfo->setItem(row, 0, item0);
        
        const QStringList &info = it.value();
        QTableWidgetItem *item1 = new QTableWidgetItem(info.count() > 0 ? info[0] : "");
        tableRepairInfo->setItem(row, 1, item1);
        
        QTableWidgetItem *item2 = new QTableWidgetItem(info.count() > 1 ? info[1] : "");
        tableRepairInfo->setItem(row, 2, item2);
        
        QTableWidgetItem *item3 = new QTableWidgetItem(info.count() > 2 ? info[2] : "");
        tableRepairInfo->setItem(row, 3, item3);
        
        qDebug() << "[TModelHelper::loadRepairInfoToTable] 加载行" << row << ": 故障模式=" << it.key();
        
        row++;
    }
}

QString TModelHelper::saveRepairInfoFromTable(QTableWidget *tableRepairInfo)
{
    if (!tableRepairInfo) {
        qDebug() << "[TModelHelper::saveRepairInfoFromTable] tableRepairInfo is null";
        return QString();
    }
    
    qDebug() << "[TModelHelper::saveRepairInfoFromTable] 表格行数:" << tableRepairInfo->rowCount();
    
    QMap<QString, QStringList> faultMap;
    
    for (int row = 0; row < tableRepairInfo->rowCount(); ++row) {
        QString faultMode = tableRepairInfo->item(row, 0) ? tableRepairInfo->item(row, 0)->text().trimmed() : "";
        QString probability = tableRepairInfo->item(row, 1) ? tableRepairInfo->item(row, 1)->text().trimmed() : "";
        QString solution = tableRepairInfo->item(row, 2) ? tableRepairInfo->item(row, 2)->text().trimmed() : "";
        QString resource = tableRepairInfo->item(row, 3) ? tableRepairInfo->item(row, 3)->text().trimmed() : "";
        
        qDebug() << "[TModelHelper::saveRepairInfoFromTable] 行" << row << ": 故障模式=" << faultMode 
                 << ", 概率=" << probability << ", 方案=" << solution << ", 资源=" << resource;
        
        if (!faultMode.isEmpty()) {
            QStringList info;
            info << probability << solution << resource;
            faultMap[faultMode] = info;
        }
    }
    
    QString result = TModelHelper::serializeRepairInfo(faultMap);
    qDebug() << "[TModelHelper::saveRepairInfoFromTable] 序列化结果长度:" << result.length();
    qDebug() << "[TModelHelper::saveRepairInfoFromTable] 序列化结果:" << result;
    
    return result;
}

int TModelHelper::autoFillFaultModesFromTModel(QTableWidget *tableRepairInfo, const QString &tmodelText)
{
    if (!tableRepairInfo) {
        return 0;
    }
    
    // 提取T语言模型中的故障模式
    QStringList tmodelFaultModes = extractFaultModesFromTModel(tmodelText);
    
    // 获取表格中已有的故障模式
    QSet<QString> existingFaultModes;
    for (int row = 0; row < tableRepairInfo->rowCount(); ++row) {
        QString faultMode = tableRepairInfo->item(row, 0) ? tableRepairInfo->item(row, 0)->text().trimmed() : "";
        if (!faultMode.isEmpty()) {
            existingFaultModes.insert(faultMode);
        }
    }
    
    // 添加表格中没有的故障模式
    int addedCount = 0;
    for (const QString &faultMode : tmodelFaultModes) {
        if (!existingFaultModes.contains(faultMode)) {
            int row = tableRepairInfo->rowCount();
            tableRepairInfo->insertRow(row);
            
            QTableWidgetItem *item0 = new QTableWidgetItem(faultMode);
            tableRepairInfo->setItem(row, 0, item0);
            
            QTableWidgetItem *item1 = new QTableWidgetItem("");  // 故障概率
            tableRepairInfo->setItem(row, 1, item1);
            
            QTableWidgetItem *item2 = new QTableWidgetItem("");  // 解决方案
            tableRepairInfo->setItem(row, 2, item2);
            
            QTableWidgetItem *item3 = new QTableWidgetItem("");  // 所需资源
            tableRepairInfo->setItem(row, 3, item3);
            
            addedCount++;
        }
    }
    
    return addedCount;
}
