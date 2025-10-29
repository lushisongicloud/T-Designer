#ifndef VARIABLE_RANGE_CONFIG_H
#define VARIABLE_RANGE_CONFIG_H

#include <QDomDocument>
#include <QMap>
#include <QString>
#include <QStringList>

namespace rangeconfig {

struct RangeValue
{
    double lower = -10000.0;
    double upper = 10000.0;
    bool hasExplicit = false;

    bool isValid() const { return lower <= upper; }
};

class VariableRangeConfig
{
public:
    struct TypeEntry
    {
        RangeValue defaultRange;
        QMap<QString, RangeValue> variableRanges;

        bool isEmpty() const
        {
            return !defaultRange.hasExplicit && variableRanges.isEmpty();
        }
    };

    void clear();

    bool isEmpty() const;

    QStringList typeKeys() const;

    RangeValue typeRange(const QString &type) const;
    void setTypeRange(const QString &type, const RangeValue &range);
    void clearTypeRange(const QString &type);

    RangeValue variableRange(const QString &type, const QString &variable) const;
    RangeValue effectiveRange(const QString &type, const QString &variable) const;
    void setVariableRange(const QString &type, const QString &variable, const RangeValue &range);
    void clearVariableRange(const QString &type, const QString &variable);

    const QMap<QString, TypeEntry> &entriesMap() const { return entries; }

    static VariableRangeConfig fromXml(const QDomElement &element);
    QDomElement toXml(QDomDocument &document) const;

    static RangeValue defaultRange();

    static QString inferTypeKey(const QString &variableName, const QString &declType);
    static QString typeDisplayName(const QString &typeKey);

private:
    TypeEntry *ensureEntry(const QString &type);
    const TypeEntry *findEntry(const QString &type) const;

    QMap<QString, TypeEntry> entries;
};

} // namespace rangeconfig

#endif // VARIABLE_RANGE_CONFIG_H
