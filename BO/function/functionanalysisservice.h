#ifndef FUNCTIONANALYSISSERVICE_H
#define FUNCTIONANALYSISSERVICE_H

#include <QStringList>
#include <QSqlDatabase>

#include "BO/function/functionrepository.h"

struct FunctionModelResult
{
    FunctionRecord record;
    QStringList linkSequence;
    QStringList warnings;
};

class FunctionAnalysisService
{
public:
    explicit FunctionAnalysisService(const QSqlDatabase &db = QSqlDatabase::database());

    FunctionModelResult analyzeSymbol(int symbolId, const QString &functionNameHint = QString()) const;

private:
    QSqlDatabase m_db;

    QStringList extractComponentNames(const QString &linkRoad) const;
    QString defaultFunctionName(const QString &symbolName, const QString &componentName, const QString &hint) const;
};

#endif // FUNCTIONANALYSISSERVICE_H
