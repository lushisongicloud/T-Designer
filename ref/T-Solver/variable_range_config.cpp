#include "variable_range_config.h"

#include <QtGlobal>

#include <algorithm>
#include <cmath>

namespace rangeconfig {

namespace {

QString formatDouble(double value)
{
    if (std::fabs(value) < 1e-12) {
        value = 0.0;
    }
    QString text = QString::number(value, 'f', 12);
    if (text.contains(QLatin1Char('.'))) {
        while (text.endsWith(QLatin1Char('0'))) {
            text.chop(1);
        }
        if (text.endsWith(QLatin1Char('.'))) {
            text.chop(1);
        }
    }
    if (text == QLatin1String("-0")) {
        text = QString("0");
    }
    if (text.isEmpty()) {
        text = QString("0");
    }
    return text;
}

bool parseBound(const QDomElement &element, const QString &attr, double *value)
{
    if (!value) {
        return false;
    }
    bool ok = false;
    const QString raw = element.attribute(attr);
    if (raw.isEmpty()) {
        return false;
    }
    double parsed = raw.toDouble(&ok);
    if (!ok || std::isnan(parsed) || std::isinf(parsed)) {
        return false;
    }
    *value = parsed;
    return true;
}

} // namespace

void VariableRangeConfig::clear()
{
    entries.clear();
}

bool VariableRangeConfig::isEmpty() const
{
    return entries.isEmpty();
}

QStringList VariableRangeConfig::typeKeys() const
{
    return entries.keys();
}

RangeValue VariableRangeConfig::typeRange(const QString &type) const
{
    const TypeEntry *entry = findEntry(type);
    if (entry && entry->defaultRange.hasExplicit && entry->defaultRange.isValid()) {
        return entry->defaultRange;
    }
    return defaultRange();
}

void VariableRangeConfig::setTypeRange(const QString &type, const RangeValue &range)
{
    if (type.trimmed().isEmpty()) {
        return;
    }
    RangeValue sanitized = range;
    if (sanitized.lower > sanitized.upper) {
        std::swap(sanitized.lower, sanitized.upper);
    }
    sanitized.hasExplicit = true;
    TypeEntry *entry = ensureEntry(type);
    entry->defaultRange = sanitized;
}

void VariableRangeConfig::clearTypeRange(const QString &type)
{
    TypeEntry *entry = ensureEntry(type);
    entry->defaultRange = defaultRange();
    entry->defaultRange.hasExplicit = false;
    if (entry->isEmpty()) {
        entries.remove(type);
    }
}

RangeValue VariableRangeConfig::variableRange(const QString &type, const QString &variable) const
{
    const TypeEntry *entry = findEntry(type);
    if (!entry) {
        return RangeValue();
    }
    const auto it = entry->variableRanges.find(variable);
    if (it == entry->variableRanges.end()) {
        return RangeValue();
    }
    return it.value();
}

RangeValue VariableRangeConfig::effectiveRange(const QString &type, const QString &variable) const
{
    const TypeEntry *entry = findEntry(type);
    if (entry) {
        const auto it = entry->variableRanges.constFind(variable);
        if (it != entry->variableRanges.constEnd() && it.value().hasExplicit && it.value().isValid()) {
            return it.value();
        }
    }
    return typeRange(type);
}

void VariableRangeConfig::setVariableRange(const QString &type,
                                           const QString &variable,
                                           const RangeValue &range)
{
    if (type.trimmed().isEmpty() || variable.trimmed().isEmpty()) {
        return;
    }
    RangeValue sanitized = range;
    if (sanitized.lower > sanitized.upper) {
        std::swap(sanitized.lower, sanitized.upper);
    }
    sanitized.hasExplicit = true;
    TypeEntry *entry = ensureEntry(type);
    entry->variableRanges.insert(variable, sanitized);
}

void VariableRangeConfig::clearVariableRange(const QString &type, const QString &variable)
{
    TypeEntry *entry = ensureEntry(type);
    entry->variableRanges.remove(variable);
    if (entry->isEmpty()) {
        entries.remove(type);
    }
}

VariableRangeConfig::TypeEntry *VariableRangeConfig::ensureEntry(const QString &type)
{
    return &entries[type];
}

const VariableRangeConfig::TypeEntry *VariableRangeConfig::findEntry(const QString &type) const
{
    const auto it = entries.constFind(type);
    if (it == entries.constEnd()) {
        return nullptr;
    }
    return &it.value();
}

VariableRangeConfig VariableRangeConfig::fromXml(const QDomElement &element)
{
    VariableRangeConfig config;
    if (element.isNull()) {
        return config;
    }

    QDomNode node = element.firstChild();
    while (!node.isNull()) {
        QDomElement typeElement = node.toElement();
        node = node.nextSibling();
        if (typeElement.isNull() || typeElement.tagName() != QString("type")) {
            continue;
        }
        const QString typeKey = typeElement.attribute(QString("name")).trimmed();
        if (typeKey.isEmpty()) {
            continue;
        }
        TypeEntry entry;

        QDomElement defaultElement = typeElement.firstChildElement(QString("default"));
        if (!defaultElement.isNull()) {
            RangeValue def = defaultRange();
            bool lowerOk = parseBound(defaultElement, QString("min"), &def.lower);
            bool upperOk = parseBound(defaultElement, QString("max"), &def.upper);
            if (lowerOk && upperOk && def.lower <= def.upper) {
                def.hasExplicit = true;
                entry.defaultRange = def;
            }
        }

        QDomElement variableElement = typeElement.firstChildElement(QString("variable"));
        while (!variableElement.isNull()) {
            const QString variableName = variableElement.attribute(QString("name")).trimmed();
            RangeValue value = defaultRange();
            bool lowerOk = parseBound(variableElement, QString("min"), &value.lower);
            bool upperOk = parseBound(variableElement, QString("max"), &value.upper);
            if (!variableName.isEmpty() && lowerOk && upperOk && value.lower <= value.upper) {
                value.hasExplicit = true;
                entry.variableRanges.insert(variableName, value);
            }
            variableElement = variableElement.nextSiblingElement(QString("variable"));
        }

        if (!entry.isEmpty()) {
            config.entries.insert(typeKey, entry);
        }
    }

    return config;
}

QDomElement VariableRangeConfig::toXml(QDomDocument &document) const
{
    QDomElement root = document.createElement(QString("variableRangeConfig"));
    for (auto it = entries.constBegin(); it != entries.constEnd(); ++it) {
        const QString typeKey = it.key();
        const TypeEntry &entry = it.value();
        if (entry.isEmpty()) {
            continue;
        }
        QDomElement typeElement = document.createElement(QString("type"));
        typeElement.setAttribute(QString("name"), typeKey);

        if (entry.defaultRange.hasExplicit && entry.defaultRange.isValid()) {
            QDomElement defaultElement = document.createElement(QString("default"));
            defaultElement.setAttribute(QString("min"), formatDouble(entry.defaultRange.lower));
            defaultElement.setAttribute(QString("max"), formatDouble(entry.defaultRange.upper));
            typeElement.appendChild(defaultElement);
        }

        for (auto vit = entry.variableRanges.constBegin(); vit != entry.variableRanges.constEnd(); ++vit) {
            if (!vit.value().hasExplicit || !vit.value().isValid()) {
                continue;
            }
            QDomElement variableElement = document.createElement(QString("variable"));
            variableElement.setAttribute(QString("name"), vit.key());
            variableElement.setAttribute(QString("min"), formatDouble(vit.value().lower));
            variableElement.setAttribute(QString("max"), formatDouble(vit.value().upper));
            typeElement.appendChild(variableElement);
        }

        root.appendChild(typeElement);
    }
    return root;
}

RangeValue VariableRangeConfig::defaultRange()
{
    RangeValue value;
    value.lower = -10000.0;
    value.upper = 10000.0;
    value.hasExplicit = false;
    return value;
}

QString VariableRangeConfig::inferTypeKey(const QString &variableName, const QString &declType)
{
    const QString trimmedName = variableName.trimmed();
    if (trimmedName.isEmpty()) {
        return QString();
    }
    if (!declType.contains(QString("Real"))) {
        return QString();
    }
    int dotIndex = trimmedName.lastIndexOf('.');
    QString suffix = dotIndex >= 0 ? trimmedName.mid(dotIndex + 1) : trimmedName;
    if (suffix.isEmpty()) {
        return QString();
    }

    if (suffix.compare(QString("u"), Qt::CaseInsensitive) == 0) {
        return QString("u");
    }
    if (suffix.compare(QString("i"), Qt::CaseInsensitive) == 0) {
        return QString("i");
    }
    if (suffix == QString("p") || suffix == QString("P")) {
        return QString("p");
    }
    if (suffix == QString("f")) {
        return QString("f");
    }
    if (suffix == QString("F")) {
        return QString("F");
    }
    if (suffix == QString("R")) {
        return QString("R");
    }
    if (suffix == QString("M")) {
        return QString("M");
    }
    if (suffix == QString("DeltaPressure")) {
        return QString("DeltaPressure");
    }
    if (suffix == QString("WorkPressure")) {
        return QString("WorkPressure");
    }
    if (suffix == QString("SetPressure")) {
        return QString("SetPressure");
    }
    if (suffix == QString("SetFlow")) {
        return QString("SetFlow");
    }
    if (suffix == QString("PressureLossCoef")) {
        return QString("PressureLossCoef");
    }
    if (suffix == QString("LeakageCoef")) {
        return QString("LeakageCoef");
    }
    if (suffix == QString("FrictionTorque")) {
        return QString("FrictionTorque");
    }
    if (suffix == QString("KineticTorque")) {
        return QString("KineticTorque");
    }
    if (suffix == QString("LoadTorque")) {
        return QString("LoadTorque");
    }
    if (suffix == QString("StartingTorque")) {
        return QString("StartingTorque");
    }
    if (suffix == QString("EQp")) {
        return QString("EQp");
    }
    if (suffix == QString("ControlPercent")) {
        return QString("ControlPercent");
    }
    if (suffix == QString("light")) {
        return QString("light");
    }

    return suffix;
}

QString VariableRangeConfig::typeDisplayName(const QString &typeKey)
{
    static const QMap<QString, QString> mapping = {
        {QString("u"), QString("电压")},
        {QString("i"), QString("电流")},
        {QString("p"), QString("压力")},
        {QString("f"), QString("流量")},
        {QString("R"), QString("电阻")},
        {QString("F"), QString("力")},
        {QString("M"), QString("力矩")},
        {QString("DeltaPressure"), QString("压差")},
        {QString("WorkPressure"), QString("工作压力")},
        {QString("SetPressure"), QString("设定压力")},
        {QString("SetFlow"), QString("设定流量")},
        {QString("PressureLossCoef"), QString("压损系数")},
        {QString("LeakageCoef"), QString("泄漏系数")},
        {QString("FrictionTorque"), QString("摩擦力矩")},
        {QString("KineticTorque"), QString("动量矩")},
        {QString("LoadTorque"), QString("负载力矩")},
        {QString("StartingTorque"), QString("起动转矩")},
        {QString("EQp"), QString("等效压力")},
        {QString("ControlPercent"), QString("控制百分比")},
        {QString("light"), QString("指示灯状态")}
    };
    return mapping.value(typeKey, typeKey);
}

} // namespace rangeconfig
