#ifndef FUNCTION_VARIABLE_CONFIG_H
#define FUNCTION_VARIABLE_CONFIG_H

#include <QDomDocument>
#include <QMap>
#include <QString>
#include <QStringList>

namespace functionvalues {

struct VariableEntry
{
    QString type;
    QString constraintValue;
    QString typicalValues;
    QString valueRange;
    QStringList satSamples;

    bool isEmpty() const;
};

class FunctionVariableConfig
{
public:
    void clear();
    bool isEmpty() const;

    QStringList variableNames() const;
    bool contains(const QString &variable) const;

    VariableEntry entry(const QString &variable) const;
    void setEntry(const QString &variable, const VariableEntry &entry);
    void removeEntry(const QString &variable);

    void ensureVariable(const QString &variable);

    QString type(const QString &variable) const;
    void setType(const QString &variable, const QString &type);

    QString constraintValue(const QString &variable) const;
    void setConstraintValue(const QString &variable, const QString &value);

    QString typicalValues(const QString &variable) const;
    void setTypicalValues(const QString &variable, const QString &values);

    QString valueRange(const QString &variable) const;
    void setValueRange(const QString &variable, const QString &range);

    QStringList satSamples(const QString &variable) const;
    void setSatSamples(const QString &variable, const QStringList &samples);
    void addSatSample(const QString &variable, const QString &sample);

    static FunctionVariableConfig fromXml(const QDomElement &element);
    QDomElement toXml(QDomDocument &document) const;

private:
    static QStringList sanitizedSamples(const QStringList &samples);

private:
    QMap<QString, VariableEntry> entries;
};

} // namespace functionvalues

#endif // FUNCTION_VARIABLE_CONFIG_H

