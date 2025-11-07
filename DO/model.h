#ifndef MODEL_H
#define MODEL_H

#include <QString>
#include <QList>
#include <QStringList>

//从系统的QString字符串描述（由器件定义与连接描述构成）以及链路信息字符串（可为""），建立系统的结构化描述
class SystemStructure
{
public:
    SystemStructure(const QString& systemDescription, const QString& linkTextforCrop);

    bool isSystemConsistent() const { return systemConsistenct; }    // 判断systemDescription是否自洽的方法
    QStringList getDeviceLineList() const { return deviceLineList; }
    QStringList getConnectionLineList() const { return connectionLineList; }
    QSet<QString> getDeviceSetInDefinition() const { return deviceSetInDefinition; }
    QSet<QString> getComponentSetInConnection() const { return componentSetInConnection; }
    QStringList getBoundaryComponentList() const { return boundaryComponentList; }
    QString getCroppedSystemDescription() const { return croppedSystemDescription; }
    QList<QStringList> getPortListInConnectionList() const {return portListInConnectionList;}

private:
    QString inputSystemDescription;
    QString inputLinkTextforCrop;
    QStringList deviceLineList;  // 器件定义行列表
    QStringList connectionLineList;  // 连接描述行列表
    QList<QStringList> portListInConnectionList; //联接端口列表列表
    QSet<QString> deviceSetInDefinition;  // 在器件定义中的器件集
    QSet<QString> componentSetInConnection;  // 在连接描述中的器件集
    QStringList boundaryComponentList;  // 边界设备列表
    QString croppedSystemDescription;  // 裁剪后的系统描述
    QSet<QString> linkComponentSet; // 链路中的器件集
    bool systemConsistenct; //系统实例化后的结构信息是否自洽

    QStringList getDeviceNamesInConnection(const QString &line);  // 从连接行中获取设备名称
    bool isDeviceInSet(const QString &component, const QSet<QString> &componentSet);  // 判断器件是否包含在器件集合中中
};

class model
{
public:
    model();

    int getId(){return id;}
    void setId(int id){this->id =id;}

    QString getName(){return name;}
    void setName(QString name){this->name = name;}

    QString getSystemDescription(){return systemDescription;}
    void setSystemDescription(QString systemDescription){this->systemDescription = systemDescription;}

    QString getTestDiscription(){return testDiscription;}
    void setTestDiscription(QString testDiscription){this->testDiscription = testDiscription;}

    QString getFunctionDiscription(){return functionDescription;}
    void setFunctionDiscription(QString functionDescription){this->functionDescription = functionDescription;}

    QString getConnectNodes(){return connectNodes;}
    QList<QStringList> getConnectNodesList(){return connectNodesList;}
    void setConnectNodes(QList<QStringList>& list);     //每个stringlist之间用%分割，stringlist内部用$分割
    void setConnectNodes(const QString& nodes);
    bool haveConnectNodes(){return !connectNodesList.isEmpty();}

private:
    int id;
    QString name;
    QString systemDescription;
    QString testDiscription;
    QString connectNodes;
    QList<QStringList> connectNodesList;
    QString functionDescription;
};

#endif // MODEL_H
