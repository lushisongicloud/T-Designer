#ifndef COMPONENTENTITY_H
#define COMPONENTENTITY_H

#include <QString>
#include <QDebug>
#include <QStringList>
#include <QHash>
#include "./DO/component.h"

struct TestItem {
    QString variable;//变量名称
    QString value;//约束描述
    double confidence;//置信度
    int level=0;
    QString testType; //观测类型:一般变量/功能执行器/边界条件/依赖功能/参照功能
    Qt::CheckState checkState;//是否已实际执行
    friend QDebug operator<<(QDebug dbg, const TestItem& item);
};

class resultEntity {
public:
    resultEntity() {}

    void setResult(const QString& componentName, const QString& failureMode, double failureProbability) {
        componentNames.append(componentName);
        failureModes.insert(componentName, failureMode);
        failureProbabilities.insert(componentName, failureProbability);
        probability *= failureProbability;
    }

    QString getComponentNames(const QString& start = "") const {
        QStringList filteredNames;

        if (start.isEmpty()) {
            filteredNames = componentNames;
        } else {
            if (start.startsWith("!")) {
                QString adjustedStart = start.mid(1); // remove "!" from the start
                for (const auto& name : componentNames) {
                    if (!name.startsWith(adjustedStart)) {
                        filteredNames.append(name);
                    }
                }
            } else {
                for (const auto& name : componentNames) {
                    if (name.startsWith(start)) {
                        filteredNames.append(name);
                    }
                }
            }
        }

        return filteredNames.join(",");
    }

    QString getFailureModes() const {
        QStringList modes;
        for (const auto& componentName : componentNames) {
            modes.append(failureModes[componentName]);
        }
        return modes.join(",");
    }

    double getProbability() const { return probability; }

    double getFailureProbability(const QString& componentName) const { return failureProbabilities[componentName]; }

    QString getFailureMode(const QString& componentName) const { return failureModes[componentName]; }

    int getComponentCount(const QString& start = "") const {
        if (start.isEmpty()) {
            return componentNames.size();
        }
        int count = 0;
        for (const auto& name : componentNames) {
            if (name.startsWith(start)) {
                ++count;
            }
        }

        return count;
    }

    bool containsComponent(const QString& componentName) const { return componentNames.contains(componentName); }

    void setProbability(double probability) {
        this->probability = probability; // 更新整体故障概率
    }

    void setFailureProbability(const QString& componentName, double failureProbability) {
        if (componentNames.contains(componentName)) {
            failureProbabilities[componentName] = failureProbability; // 更新指定组件的故障概率
        } else {
            qDebug()<<"resultEntity: componentName Not exists:"<<componentName;
        }
    }

private:
    QStringList componentNames; // 用于保存组件名称的列表
    QHash<QString, QString> failureModes; // 将组件名称映射到对应的故障模式
    double probability = 1.0; // 故障概率
    QHash<QString, double> failureProbabilities; // 将组件名称映射到对应的故障概率
};

class obsEntity
{
public:
    obsEntity() {}

    const QString getName() const {return name;}
    void setName(QString name){this->name = name;}

    const QString getVariable() const {return variable;}
    void setVariable(QString variable){this->variable = variable;}

    const QString getDescription() const{return description;}
    void setDescription(QString description){this->description = description;}

    double getConfidence() const{return confidence;}
    void setConfidence(double confidence){this->confidence = confidence;}

    double getFailureProbability() const{return failureProbability;}
    void setFailureProbability(double failureProbability){this->failureProbability = failureProbability;}

private:
    QString name;
    QString variable;
    QString description;
    double confidence;
    double failureProbability;
public:
    QString obsType;
};

class ComponentEntity
{
public:
    ComponentEntity();

    const QString getName() const {return name;}
    void setName(QString name){this->name = name;}

    const QString getVariable() const {return variable;}
    void setVariable(QString variable){this->variable = variable;}

    const QString getDescription() const{return description;}
    void setDescription(QString description){this->description = description;}

    const QList<FailureMode> getFailMode() const{return ListFailureMode;}
    void setFailMode(QList<FailureMode> ListFailMode){this->ListFailureMode = ListFailMode;}

    double getFailureProbability() const{return failureProbability;}
    void setFailureProbability(double failureProbability){this->failureProbability = failureProbability;}

    void addPort(const QString& port_temp){port.push_back(port_temp);}
    void deletePort(int i){if(i>=0&&i<port.length()) port.removeAt(i);}
    void deletePort(const QString& port_temp);
    const QString getPort(int i) const {if(i>=0&&i<port.length()) return port.at(i);}
    int  findPort(const QString& port_temp) const;    //返回端口在port中的位置，未找到返回-1

    bool operator==(const ComponentEntity &c){return this->name==c.name;}

private:
    QString name;
    QString variable;
    QString description;
    QList<FailureMode> ListFailureMode;
    QStringList port;
    double failureProbability;
};

#endif // COMPONENTENTITY_H
