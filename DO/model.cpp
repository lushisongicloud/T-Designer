#include "model.h"
#include <QDebug>

model::model()
{

}

void model::setConnectNodes(QList<QStringList>& list)
{
    connectNodesList = list;
    connectNodes.clear();

    int length = list.count();
    for(int i=0; i<length; i++)
    {
        int length2 = list.at(i).count();
        for(int j=0; j<length2; j++)
        {
            connectNodes.append(list.at(i).at(j));
            connectNodes.append("$");
        }
        connectNodes.append("%");
    }
}

void model::setConnectNodes(const QString& nodes)
{
    connectNodes = nodes;
    connectNodesList.clear();

    QStringList list2 = nodes.split('%', QString::SkipEmptyParts);

    int length = list2.count();

    for(int i=0; i<length; i++)
    {
        QStringList temp_list = list2.at(i).split('$',QString::SkipEmptyParts);
        connectNodesList.append(temp_list);
    }
}

// ************************************** SystemDescriptionStructure 部分*********************************************************** //
SystemStructure::SystemStructure(const QString& systemDescription, const QString& linkTextforCrop)
{
    systemConsistenct = true;
    this->inputSystemDescription = systemDescription;
    this->inputLinkTextforCrop = linkTextforCrop;

    //qDebug().noquote()<<"Input of cropSystemDescription  linkText:"<<localLinkTextforCrop<<"  modelDescription:"<<localSystemDescription;

    // 将系统描述拆分为两部分：器件描述和连接描述
    QList<QString> qlist = inputSystemDescription.split("END", QString::SkipEmptyParts);
    if(qlist.size() != 2) {
        qDebug() << "Error: Invalid model description";
        systemConsistenct = false;
    }
    QString deviceDescription = qlist[0].remove("DEF").remove("BEGIN").remove("END").trimmed();
    QString connectionDescription = qlist[1].remove("DEF").remove("BEGIN").remove("END").trimmed();

    // 将器件描述和连接描述分别拆分为各行
    deviceLineList = deviceDescription.split("\n");
    connectionLineList = connectionDescription.split("\n");

    if(linkTextforCrop == "")
    {
        croppedSystemDescription = inputSystemDescription;
        // 从每一个连接描述行中提取所有设备名称
        for (const QString &connectionLine : connectionLineList) {
            QStringList devices = connectionLine.split("(")[1].split(")")[0].split(",");
            portListInConnectionList.append(devices);
            for (QString &device : devices) {
                device = device.split(".")[0].trimmed();
                componentSetInConnection.insert(device);
            }
        }
        // 遍历器件定义的每一行，提取器件名称
        for (const QString &line : deviceLineList) {
            QString trimmedLine = line.trimmed();
            QStringList parts = trimmedLine.split(" ");
            if (parts.size() < 2) continue;
            QString deviceName = parts[1].split("(")[0].trimmed();
            deviceSetInDefinition.insert(deviceName);
        }
    }
    else
    {
        // 将功能链路相关器件放到一个容器中，方便查询
        linkComponentSet = QSet<QString>::fromList(inputLinkTextforCrop.split(","));

        // 用来存储新的连接描述
        QStringList newConnectionLines;

        for (const QString &line : connectionLineList) {
            QStringList componentListInConnection = getDeviceNamesInConnection(line);
            for (const QString &componentInConnection : componentListInConnection) {
                if (isDeviceInSet(componentInConnection, linkComponentSet)) {
                    newConnectionLines.append(line);
                    break;  // 一旦找到元件在功能链路中，就跳过剩余元件
                }
            }
        }

        // 从newConnectionLines中提取所有设备名称
        for (const QString &connectionLine : newConnectionLines) {
            QStringList devices = connectionLine.split("(")[1].split(")")[0].split(",");
            portListInConnectionList.append(devices);
            for (QString &device : devices) {
                device = device.split(".")[0].trimmed();
                componentSetInConnection.insert(device);
            }
        }
        //qDebug()<<"deviceNamesInConnection:"<<deviceNamesInConnection;

        // 用来存储新的器件描述
        QStringList newComponentLines;

        // 遍历器件描述的每一行，如果在新的连接描述中存在该器件，则保留
        for (const QString &line : deviceLineList) {
            QString trimmedLine = line.trimmed();
            QStringList parts = trimmedLine.split(" ");
            if (parts.size() < 2) continue;
            QString deviceName = parts[1].split("(")[0].trimmed();
            if (componentSetInConnection.contains(deviceName)) {
                deviceSetInDefinition.insert(deviceName);
                newComponentLines.append(line);
            }
        }

        // 拼接新的系统描述
        croppedSystemDescription = QString("DEF BEGIN\n%1\nDEF END\n%2").arg(newComponentLines.join("\n"), newConnectionLines.join("\n"));
        //qDebug().noquote()<<"croppedSystemDescription:\n"<<croppedSystemDescription;

        // 存储边界条件设备
        for (const QString &connectionLine : newConnectionLines) {
            QStringList devicesInConnection = getDeviceNamesInConnection(connectionLine);
            for (const QString &deviceInConnection : devicesInConnection) {
                if (!isDeviceInSet(deviceInConnection,linkComponentSet)) {
                    boundaryComponentList.append(deviceInConnection);
                }
            }
        }
        deviceLineList = newComponentLines;
        connectionLineList = newConnectionLines;
    }
    //判断连接中的器件是否都包含在器件定义中的器件集中
    // 将功能链路相关器件放到一个容器中，方便查询
    linkComponentSet = QSet<QString>::fromList(inputLinkTextforCrop.split(","));

    // 判断功能链路中的器件是否都包含在器件定义中的器件集中
    if(systemConsistenct)
    {
        for (const QString &componentInLink : linkComponentSet) {
            if (!isDeviceInSet(componentInLink, deviceSetInDefinition)) {
                systemConsistenct = false;
                qDebug() << "Error: The component " << componentInLink << " is in the function link but not in the device definition.";
                break;
            }
        }
    }
    // 判断连接中的器件是否都包含在器件定义中的器件集中
    if(systemConsistenct)
    {
        for (const QString &componentInConnection : componentSetInConnection) {
            if (!isDeviceInSet(componentInConnection, deviceSetInDefinition)) {
                systemConsistenct = false;
                qDebug() << "Error: The component " << componentInConnection << " is in the connection description but not in the device definition.";
                break;
            }
        }
    }

}
// 确定设备名是否被包含在设备集合中
bool SystemStructure::isDeviceInSet(const QString &component, const QSet<QString> &componentSet) {
    for (const QString &deviceInSet : componentSet) {
        if (component == deviceInSet || component.startsWith(deviceInSet + ".")) {
            return true;
        }
    }
    return false;
}

// 获取连接行中的器件名
QStringList SystemStructure::getDeviceNamesInConnection(const QString &line) {
    // 创建一个正则表达式，该表达式用于寻找所有以"("开始并以")"结束的子字符串
    // 这个正则表达式的意思是："寻找任意的、以'('开始并以')'结束的、'('和')'中间可以有任何字符的子字符串"
    QRegExp rx("\\(([^)]*)\\)");
    QStringList devices;  // 创建一个空的QStringList，用于存储找到的器件名
    int pos = 0;  // pos变量是用于指示当前处理位置的指针，初始设置为0，也就是从字符串的开始位置进行处理
    // 开始一个while循环，条件是当正则表达式在目标字符串中找不到匹配的子字符串时结束
    while ((pos = rx.indexIn(line, pos)) != -1) {
        // 在每次循环中，正则表达式都会从当前pos的位置开始搜索，找到与正则表达式匹配的子字符串
        // 如果找到了，那么rx.indexIn(line, pos)就会返回这个子字符串在目标字符串中的起始位置，然后赋值给pos
        // 然后，使用rx.cap(1)获取这个匹配的子字符串（注意这里的1是因为正则表达式中的括号形成了一个捕获组，对应的就是cap(1)）
        // 然后，调用split(",")方法将这个子字符串（器件名列表）按照","进行分割，得到一个QStringList，然后添加到devices这个QStringList中
        devices << rx.cap(1).split(",");
        // pos的值增加匹配到的字符串长度，即rx.matchedLength()，为下一次匹配做准备
        pos += rx.matchedLength();
    }
    // 最后，返回包含所有找到的设备名的QStringList
    return devices;
}
/*
QStringList SelectFunctionDialog::findBoundaryConditions(const QString &linkText, const QString &modelDescription)
{
    // 将链路信息拆分成单个的器件或器件端口
    QSet<QString> functionDevices = QSet<QString>::fromList(linkText.split(",", QString::SkipEmptyParts));

    // 拆分模型描述为器件描述和连接描述
    QList<QString> qlist = modelDescription.split("END");
    if(qlist.size() != 2) {
        qDebug() << "Error: Invalid model description";
        return QStringList();
    }

    QString connectionDescription = qlist[1].remove("DEF").remove("BEGIN").remove("END");
    QStringList connectionLines = connectionDescription.split("\n");
    QStringList newConnectionLines;

    // 找出链路信息包含的连接描述
    for (const QString &line : connectionLines) {
        QStringList devicesInLine = getDeviceNamesInConnection(line);
        if (isDeviceMatched(devicesInLine, functionDevices)) {
            newConnectionLines.append(line);
        }
    }

    // 存储边界条件设备
    QStringList boundaryDeviceList;
    for (const QString &connectionLine : newConnectionLines) {
        QStringList devicesInConnection = getDeviceNamesInConnection(connectionLine);
        for (const QString &deviceInConnection : devicesInConnection) {
            if (!isDeviceCoveredInLink(deviceInConnection,functionDevices)) {
                boundaryDeviceList.append(deviceInConnection);
            }
        }
    }
    return boundaryDeviceList;
}
// 获取连接行中的器件名
QStringList SelectFunctionDialog::getDeviceNamesInConnection(const QString &line) {
    // 创建一个正则表达式，该表达式用于寻找所有以"("开始并以")"结束的子字符串
    // 这个正则表达式的意思是："寻找任意的、以'('开始并以')'结束的、'('和')'中间可以有任何字符的子字符串"
    QRegExp rx("\\(([^)]*)\\)");
    QStringList devices;  // 创建一个空的QStringList，用于存储找到的器件名
    int pos = 0;  // pos变量是用于指示当前处理位置的指针，初始设置为0，也就是从字符串的开始位置进行处理
    // 开始一个while循环，条件是当正则表达式在目标字符串中找不到匹配的子字符串时结束
    while ((pos = rx.indexIn(line, pos)) != -1) {
        // 在每次循环中，正则表达式都会从当前pos的位置开始搜索，找到与正则表达式匹配的子字符串
        // 如果找到了，那么rx.indexIn(line, pos)就会返回这个子字符串在目标字符串中的起始位置，然后赋值给pos
        // 然后，使用rx.cap(1)获取这个匹配的子字符串（注意这里的1是因为正则表达式中的括号形成了一个捕获组，对应的就是cap(1)）
        // 然后，调用split(",")方法将这个子字符串（器件名列表）按照","进行分割，得到一个QStringList，然后添加到devices这个QStringList中
        devices << rx.cap(1).split(",");
        // pos的值增加匹配到的字符串长度，即rx.matchedLength()，为下一次匹配做准备
        pos += rx.matchedLength();
    }
    // 最后，返回包含所有找到的设备名的QStringList
    return devices;
}

// 确定是否匹配设备名：功能链路中的器件如果包含连接描述中的器件端口，则认为匹配
bool SelectFunctionDialog::isDeviceMatched(const QStringList &devicesInConnection, const QSet<QString> &functionLink) {
    for (const QString &deviceInConnection : devicesInConnection) {
        //qDebug()<<"deviceInLine:"<<deviceInLine;
        for (const QString &deviceInLink : functionLink) {
            //新的写法
            if (deviceInConnection == deviceInLink || deviceInConnection.startsWith(deviceInLink + ".")) {
                return true;
            }
        }
    }
    return false;
}
//====================构建根据功能链路裁剪的新的系统描述===============================
QString SelectFunctionDialog::cropSystemDescription(const QString &linkText, const QString modelDescription)
{
    //qDebug().noquote()<<"Input of cropSystemDescription  linkText:"<<linkText<<"  modelDescription:"<<modelDescription;
    QString functionLink = linkText;
    QString systemDescription = modelDescription;

    // 将功能链路相关器件放到一个容器中，方便查询
    QSet<QString> functionDevices = QSet<QString>::fromList(functionLink.split(","));

    // 将系统描述拆分为两部分：器件描述和连接描述
    QList<QString> qlist = modelDescription.split("END", QString::SkipEmptyParts);
    if(qlist.size() != 2) {
        qDebug() << "Error: Invalid model description";
        return "";
    }
    QString deviceDescription = qlist[0].remove("DEF").remove("BEGIN").remove("END").trimmed();
    QString connectionDescription = qlist[1].remove("DEF").remove("BEGIN").remove("END").trimmed();

    // 将器件描述和连接描述分别拆分为各行
    QStringList deviceLines = deviceDescription.split("\n");
    QStringList connectionLines = connectionDescription.split("\n");

    // 用来存储新的连接描述
    QStringList newConnectionLines;

    for (const QString &line : connectionLines) {
        QStringList devicesInLine = getDeviceNamesInConnection(line);
        //
        if (isDeviceMatched(devicesInLine, functionDevices)) {
            newConnectionLines.append(line);
        }
    }

    // 从newConnectionLines中提取所有设备名称
    QSet<QString> deviceNamesInConnection;
    for (const QString &connectionLine : newConnectionLines) {
        QStringList devices = connectionLine.split("(")[1].split(")")[0].split(",");
        for (QString &device : devices) {
            device = device.split(".")[0].trimmed();
            deviceNamesInConnection.insert(device);
        }
    }
    //qDebug()<<"deviceNamesInConnection:"<<deviceNamesInConnection;

    // 用来存储新的器件描述
    QStringList newDeviceLines;

    // 遍历器件描述的每一行，如果在新的连接描述中存在该器件，则保留
    for (const QString &line : deviceLines) {
        QString trimmedLine = line.trimmed();
        QStringList parts = trimmedLine.split(" ");
        if (parts.size() < 2) continue;
        QString deviceName = parts[1].split("(")[0].trimmed();
        if (deviceNamesInConnection.contains(deviceName)) {
            newDeviceLines.append(line);
        }
    }

    // 拼接新的系统描述
    QString croppedSystemDescription = "DEF BEGIN\n" + newDeviceLines.join("\n") + "\nDEF END\n" + newConnectionLines.join("\n");
    qDebug().noquote()<<"croppedSystemDescription:\n"<<croppedSystemDescription;
    return croppedSystemDescription;
}

// 确定是否匹配设备名
bool isDeviceCoveredInLink(const QString &deviceInConnection, const QSet<QString> &functionLinkDevices) {
    // 新的写法：
    for (const QString &deviceInLink : functionLinkDevices) {
        if(deviceInConnection == deviceInLink || deviceInConnection.startsWith(deviceInLink + ".")) return true;
    }
    return false;
}
*/
