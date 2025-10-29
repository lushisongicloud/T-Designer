#ifndef PARAMETER_H
#define PARAMETER_H

#include <QString>

class parameter
{
public:
    parameter();

    int getId(){return id;}
    void setId(int id){this->id = id;}

    int getComponentId(){return componentId;}
    void setComponentId(int componentId){this->componentId = componentId;}

    QString getName(){return name;}
    void setName(QString name){this->name = name;}

    QString getDefaultValue(){return defaultValue;}
    void setDefaultValue(QString defaultValue){this->defaultValue = defaultValue;}
private:
    int id;
    int componentId;
    QString name;
    QString defaultValue;
};

#endif // PARAMETER_H
