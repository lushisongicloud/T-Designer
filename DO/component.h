#ifndef COMPONENT_H
#define COMPONENT_H

#include <QString>
#include <QStringList>
#include <QList>

class FailureMode {
public:
    QString name;
    QString describe;
    double probability;
    struct ModeOverride {
        QString componentName;
        QStringList assertions;
        bool replaceNormal = true;
    };
    QList<ModeOverride> overrides;

    FailureMode(QString n, QString d, double p) : name(n), describe(d), probability(p) {}
    FailureMode(double p) : name(""), describe(""), probability(p) {}  // 用于unknownfault
    FailureMode() : name(""), describe(""), probability(0.0) {}

    QString getName() const { return name; }
    QString getDescribe() const { return describe; }
    double getProbability() const { return probability; }
};

class component
{
private:
    int id;
    QString type;
    QString mark;
    QString variable;
    QString parameter;
    QString description;
    //QStringList ListFailureMode;
    QList<FailureMode> ListFailureMode;
    double failureProbability;
public:
    component();

    int getId(){return id;}
    void setId(int id){this->id = id;}

    QString getType(){return type;}
    void setType(QString type){this->type = type;}

    QString getMark(){return mark;}
    void setMark(QString mark){this->mark = mark;}

    QString getVariable(){return variable;}
    void setVariable(QString variable){this->variable = variable;}

    QString getParameter(){return parameter;}
    void setParameter(QString parameter){this->parameter = parameter;}

    QString getDescription(){return description;}
    void setDescription(QString description){this->description = description;}

    QList<FailureMode> getFailureMode(){return ListFailureMode;}
    void setFailureMode(QString strFailureMode);

    double getFailureProbability(){return failureProbability;}
    void setFailureProbability(QList<FailureMode> ListFailureMode);
};

#endif // COMPONENT_H
