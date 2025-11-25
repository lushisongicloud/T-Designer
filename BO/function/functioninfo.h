#ifndef FUNCTIONINFO_H
#define FUNCTIONINFO_H

#include <QString>
#include <QStringList>
#include <QList>
#include <QVector>
#include "BO/componententity.h"
#include "function_variable_config.h"

struct FunctionOfflineResult {
    QStringList componentNames;
    QStringList failureModes;
    double probability = 0.0;
};

struct FunctionInfo {
    QString functionName; // 功能名称
    QString description; // 功能描述
    QString actuatorName; // 执行器名称
    TestItem actuatorConstraint; // 执行器约束
    QList<TestItem> constraintList; // 输入/约束列表
    QString link; // 链路描述
    QStringList linkElements; // 链路拆解后的器件序列
    QString componentDependency; // 依赖的器件集合
    QString allRelatedComponent; // 所有关联器件集合
    QStringList allComponentList; // 所有关联器件列表
    QString functionDependency; // 功能依赖关系
    bool persistent = true; // 故障是否可保持
    double faultProbability = 0.0; // 失效概率
    QString constraintIntegrity; // 约束完整性状态
    QVector<FunctionOfflineResult> offlineResults; // 离线求解结果
    QString variableConfigXml; // 变量取值范围配置片段（XML）
    functionvalues::FunctionVariableConfig variableConfig; // 变量取值范围配置对象
};

#endif // FUNCTIONINFO_H
