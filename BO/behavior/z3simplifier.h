#ifndef Z3SIMPLIFIER_H
#define Z3SIMPLIFIER_H

#include <QString>
#include <QStringList>

struct Z3SimplificationResult
{
    bool success = false;
    QString simplifiedExpression;
    QStringList eliminatedSymbols;
    QString log;
};

class Z3Simplifier
{
public:
    Z3Simplifier();

    Z3SimplificationResult simplifyConjunction(const QStringList &expressions,
                                               const QStringList &eliminateSymbols = {}) const;

    bool isUnsat(const QStringList &assertions) const;

private:
    QString sanitizeExpression(const QString &expression) const;
    QString buildScriptFromExpressions(const QStringList &expressions) const;
};

#endif // Z3SIMPLIFIER_H
