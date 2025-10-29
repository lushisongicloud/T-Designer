#ifndef FUNCTIONINFO_H
#define FUNCTIONINFO_H

#include <QString>
#include <QList>
#include "BO/componententity.h"

struct FunctionInfo {
    QString functionName; // 功能名称
    QString actuatorName; // 执行器名称
    TestItem actuatorConstraint; // 执行器约束
    QList<TestItem> constraintList; // 输入/约束列表
    QString link; // 链路描述
    QString componentDependency; // 依赖的器件集合
    QString allRelatedComponent; // 所有关联器件集合
    QString functionDependency; // 功能依赖关系
    bool persistent = true; // 故障是否可保持
    double faultProbability = 0.0; // 失效概率
};

#endif // FUNCTIONINFO_H
