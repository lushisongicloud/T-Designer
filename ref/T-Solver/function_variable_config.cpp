#include "function_variable_config.h"

#include <QSet>

namespace functionvalues {

namespace {

QString normalizeSample(const QString &sample)
{
    QString trimmed = sample.trimmed();
    if (trimmed == QStringLiteral("-0")) {
        trimmed = QStringLiteral("0");
    }
    return trimmed;
}

QStringList uniqueOrdered(const QStringList &samples)
{
    QSet<QString> seen;
    QStringList ordered;
    for (const QString &sample : samples) {
        const QString normalized = normalizeSample(sample);
        if (normalized.isEmpty()) {
            continue;
        }
        if (!seen.contains(normalized)) {
            ordered.append(normalized);
            seen.insert(normalized);
        }
    }
    return ordered;
}

} // namespace

bool VariableEntry::isEmpty() const
{
    return type.trimmed().isEmpty()
            && constraintValue.trimmed().isEmpty()
            && typicalValues.trimmed().isEmpty()
            && valueRange.trimmed().isEmpty()
            && satSamples.isEmpty();
}

void FunctionVariableConfig::clear()
{
    entries.clear();
}

bool FunctionVariableConfig::isEmpty() const
{
    return entries.isEmpty();
}

QStringList FunctionVariableConfig::variableNames() const
{
    return entries.keys();
}

bool FunctionVariableConfig::contains(const QString &variable) const
{
    return entries.contains(variable);
}

VariableEntry FunctionVariableConfig::entry(const QString &variable) const
{
    return entries.value(variable);
}

void FunctionVariableConfig::setEntry(const QString &variable, const VariableEntry &entry)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    if (entry.isEmpty()) {
        entries.remove(variable);
    } else {
        VariableEntry sanitized = entry;
        sanitized.satSamples = sanitizedSamples(sanitized.satSamples);
        entries.insert(variable, sanitized);
    }
}

void FunctionVariableConfig::removeEntry(const QString &variable)
{
    entries.remove(variable);
}

void FunctionVariableConfig::ensureVariable(const QString &variable)
{
    if (!entries.contains(variable)) {
        entries.insert(variable, VariableEntry());
    }
}

QString FunctionVariableConfig::type(const QString &variable) const
{
    return entries.value(variable).type;
}

void FunctionVariableConfig::setType(const QString &variable, const QString &type)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    entry.type = type.trimmed();
    setEntry(variable, entry);
}

QString FunctionVariableConfig::constraintValue(const QString &variable) const
{
    return entries.value(variable).constraintValue;
}

void FunctionVariableConfig::setConstraintValue(const QString &variable, const QString &value)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    entry.constraintValue = value.trimmed();
    setEntry(variable, entry);
}

QString FunctionVariableConfig::typicalValues(const QString &variable) const
{
    return entries.value(variable).typicalValues;
}

void FunctionVariableConfig::setTypicalValues(const QString &variable, const QString &values)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    entry.typicalValues = values.trimmed();
    setEntry(variable, entry);
}

QString FunctionVariableConfig::valueRange(const QString &variable) const
{
    return entries.value(variable).valueRange;
}

void FunctionVariableConfig::setValueRange(const QString &variable, const QString &range)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    entry.valueRange = range.trimmed();
    setEntry(variable, entry);
}

QStringList FunctionVariableConfig::satSamples(const QString &variable) const
{
    return entries.value(variable).satSamples;
}

void FunctionVariableConfig::setSatSamples(const QString &variable, const QStringList &samples)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    entry.satSamples = sanitizedSamples(samples);
    setEntry(variable, entry);
}

void FunctionVariableConfig::addSatSample(const QString &variable, const QString &sample)
{
    if (variable.trimmed().isEmpty()) {
        return;
    }
    QString normalized = normalizeSample(sample);
    if (normalized.isEmpty()) {
        return;
    }
    VariableEntry entry = entries.value(variable);
    if (!entry.satSamples.contains(normalized)) {
        entry.satSamples.append(normalized);
        setEntry(variable, entry);
    }
}

FunctionVariableConfig FunctionVariableConfig::fromXml(const QDomElement &element)
{
    FunctionVariableConfig config;
    if (element.isNull()) {
        return config;
    }

    QDomElement variableElement = element.firstChildElement(QStringLiteral("variable"));
    while (!variableElement.isNull()) {
        const QString variableName = variableElement.attribute(QStringLiteral("name")).trimmed();
        if (!variableName.isEmpty()) {
            VariableEntry entry;
            entry.type = variableElement.firstChildElement(QStringLiteral("type")).text().trimmed();
            entry.typicalValues = variableElement.firstChildElement(QStringLiteral("typical")).text().trimmed();
            entry.valueRange = variableElement.firstChildElement(QStringLiteral("range")).text().trimmed();
            const QString samplesText = variableElement.firstChildElement(QStringLiteral("satSamples")).text().trimmed();
            if (!samplesText.isEmpty()) {
                entry.satSamples = sanitizedSamples(samplesText.split(QStringLiteral(";")));
            }
            config.setEntry(variableName, entry);
        }
        variableElement = variableElement.nextSiblingElement(QStringLiteral("variable"));
    }
    return config;
}

QDomElement FunctionVariableConfig::toXml(QDomDocument &document) const
{
    QDomElement root = document.createElement(QStringLiteral("variableValueConfig"));
    for (auto it = entries.constBegin(); it != entries.constEnd(); ++it) {
        const QString variable = it.key();
        const VariableEntry &entry = it.value();
        if (entry.isEmpty()) {
            continue;
        }
        QDomElement variableElement = document.createElement(QStringLiteral("variable"));
        variableElement.setAttribute(QStringLiteral("name"), variable);
        bool hasChild = false;

        if (!entry.type.trimmed().isEmpty()) {
            QDomElement typeElement = document.createElement(QStringLiteral("type"));
            typeElement.appendChild(document.createTextNode(entry.type));
            variableElement.appendChild(typeElement);
            hasChild = true;
        }

        if (!entry.typicalValues.trimmed().isEmpty()) {
            QDomElement typicalElement = document.createElement(QStringLiteral("typical"));
            typicalElement.appendChild(document.createTextNode(entry.typicalValues));
            variableElement.appendChild(typicalElement);
            hasChild = true;
        }

        if (!entry.valueRange.trimmed().isEmpty()) {
            QDomElement rangeElement = document.createElement(QStringLiteral("range"));
            rangeElement.appendChild(document.createTextNode(entry.valueRange));
            variableElement.appendChild(rangeElement);
            hasChild = true;
        }

        if (!entry.satSamples.isEmpty()) {
            QDomElement samplesElement = document.createElement(QStringLiteral("satSamples"));
            samplesElement.appendChild(document.createTextNode(sanitizedSamples(entry.satSamples).join(QStringLiteral(";"))));
            variableElement.appendChild(samplesElement);
            hasChild = true;
        }

        if (hasChild) {
            root.appendChild(variableElement);
        }
    }
    return root;
}

QStringList FunctionVariableConfig::sanitizedSamples(const QStringList &samples)
{
    return uniqueOrdered(samples);
}

} // namespace functionvalues
