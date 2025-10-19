#ifndef FUNCTIONDEPENDENCYRESOLVER_H
#define FUNCTIONDEPENDENCYRESOLVER_H

#include <QMap>
#include <QSet>
#include <QStringList>

#include "BO/function/functioninfo.h"

class FunctionDependencyResolver
{
public:
    struct ResolvedFunction {
        QString functionName;
        QSet<QString> requiredInputs;
        QSet<QString> actuatorVariables;
        QSet<QString> dependencyFunctions;
        QStringList evaluationOrder;
        QStringList warnings;
    };

    FunctionDependencyResolver();
    explicit FunctionDependencyResolver(const QMap<QString, FunctionInfo> &definitions);

    void setDefinitions(const QMap<QString, FunctionInfo> &definitions);

    ResolvedFunction resolve(const QString &functionName) const;
    QSet<QString> dependencyClosure(const QString &functionName) const;

private:
    QMap<QString, FunctionInfo> m_definitions;

    QStringList parseDependencyFunctions(const FunctionInfo &info) const;
    QStringList extractInputVariables(const FunctionInfo &info) const;
    QString normalizeVariable(const QString &variable) const;
};

#endif // FUNCTIONDEPENDENCYRESOLVER_H
