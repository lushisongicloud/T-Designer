#include "BO/function/functiondependencyresolver.h"

#include <functional>
#include <QVector>

FunctionDependencyResolver::FunctionDependencyResolver() = default;

FunctionDependencyResolver::FunctionDependencyResolver(const QMap<QString, FunctionInfo> &definitions)
    : m_definitions(definitions)
{
}

void FunctionDependencyResolver::setDefinitions(const QMap<QString, FunctionInfo> &definitions)
{
    m_definitions = definitions;
}

FunctionDependencyResolver::ResolvedFunction FunctionDependencyResolver::resolve(const QString &functionName) const
{
    ResolvedFunction result;
    result.functionName = functionName;

    if (!m_definitions.contains(functionName)) {
        result.warnings.append(QString("未找到功能定义: %1").arg(functionName));
        return result;
    }

    QSet<QString> visited;
    QSet<QString> recursionStack;
    QSet<QString> dependencySet;
    QSet<QString> inputSet;
    QSet<QString> actuatorSet;
    QStringList order;
    QStringList warnings;

    std::function<void(const QString &, bool)> dfs = [&](const QString &name, bool collectActuator) {
        if (!m_definitions.contains(name)) {
            warnings.append(QString("未找到功能定义: %1").arg(name));
            return;
        }
        if (recursionStack.contains(name)) {
            warnings.append(QString("检测到功能依赖循环: %1").arg(name));
            return;
        }
        if (visited.contains(name)) return;

        recursionStack.insert(name);

        const FunctionInfo &info = m_definitions.value(name);
        const QStringList deps = parseDependencyFunctions(info);
        for (const QString &dep : deps) {
            if (dep.isEmpty()) continue;
            dependencySet.insert(dep);
            dfs(dep, false);
        }

        for (const QString &input : extractInputVariables(info))
            inputSet.insert(input);

        if (collectActuator) {
            const QString actuator = normalizeVariable(info.actuatorConstraint.variable);
            if (!actuator.isEmpty()) actuatorSet.insert(actuator);
        }

        recursionStack.remove(name);
        visited.insert(name);
        order.append(name);
    };

    dfs(functionName, true);

    dependencySet.remove(functionName);

    result.requiredInputs = inputSet;
    result.actuatorVariables = actuatorSet;
    result.dependencyFunctions = dependencySet;
    result.evaluationOrder = order;
    result.warnings = warnings;

    return result;
}

QSet<QString> FunctionDependencyResolver::dependencyClosure(const QString &functionName) const
{
    QSet<QString> closure;
    if (!m_definitions.contains(functionName)) return closure;

    QVector<QString> stack;
    stack.append(functionName);
    while (!stack.isEmpty()) {
        const QString current = stack.takeLast();
        if (!m_definitions.contains(current)) continue;
        const QStringList deps = parseDependencyFunctions(m_definitions.value(current));
        for (const QString &dep : deps) {
            if (dep.isEmpty() || dep == functionName) continue;
            if (closure.contains(dep)) continue;
            closure.insert(dep);
            stack.append(dep);
        }
    }
    closure.remove(functionName);
    return closure;
}

QStringList FunctionDependencyResolver::parseDependencyFunctions(const FunctionInfo &info) const
{
    QStringList dependencies;
    const QString text = info.functionDependency;
    if (text.trimmed().isEmpty()) return dependencies;

    const QStringList entries = text.split(';', QString::SkipEmptyParts);
    for (const QString &entry : entries) {
        const QStringList parts = entry.split(',', QString::KeepEmptyParts);
        if (parts.size() < 2) continue;
        const QString depFunction = parts.at(1).trimmed();
        if (!depFunction.isEmpty()) dependencies.append(depFunction);
    }
    return dependencies;
}

QStringList FunctionDependencyResolver::extractInputVariables(const FunctionInfo &info) const
{
    static const QSet<QString> kExcludedTypes = {
        QString("功能执行器"),
        QString("依赖功能"),
        QString("参照功能")
    };

    QStringList inputs;
    for (const TestItem &item : info.constraintList) {
        const QString type = item.testType.trimmed();
        if (kExcludedTypes.contains(type)) continue;
        const QString variable = normalizeVariable(item.variable);
        if (!variable.isEmpty()) inputs.append(variable);
    }
    return inputs;
}

QString FunctionDependencyResolver::normalizeVariable(const QString &variable) const
{
    return variable.trimmed();
}
