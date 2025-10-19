#ifndef TMODELVALIDATOR_H
#define TMODELVALIDATOR_H

#include <QList>
#include <QSet>
#include <QString>
#include <QStringList>
#include <QVector>

struct PortInfo
{
    QString connNum;
    QString symbolId;
    QString symb2TermInfoId;
    QString description;
};

struct PortVariableBinding
{
    PortInfo port;
    QSet<QString> declaredDirections;
    QSet<QString> referencedDirections;
    QSet<QString> tokens;
};

struct TModelValidationResult
{
    QVector<PortVariableBinding> bindings;
    QStringList missingDeclarations;
    QStringList undefinedVariables;
    QStringList unusedPorts;
    QStringList formatErrors;
    QStringList hints;

    bool isValid() const
    {
        return missingDeclarations.isEmpty()
                && undefinedVariables.isEmpty()
                && formatErrors.isEmpty();
    }
};

class TModelValidator
{
public:
    TModelValidationResult validate(const QString &tmodelText,
                                    const QList<PortInfo> &ports) const;
};

#endif // TMODELVALIDATOR_H

