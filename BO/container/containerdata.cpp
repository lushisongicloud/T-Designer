#include "BO/container/containerdata.h"

#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonParseError>
#include <QJsonValue>

namespace {
const QString kDirectionInput = QString("input");
const QString kDirectionOutput = QString("output");
const QString kDirectionInOut = QString("inout");
const QString kDirectionInternal = QString("internal");
}

QString portDirectionToString(PortDirection direction)
{
    switch (direction) {
    case PortDirection::Input: return kDirectionInput;
    case PortDirection::Output: return kDirectionOutput;
    case PortDirection::Bidirectional: return kDirectionInOut;
    case PortDirection::Internal: return kDirectionInternal;
    case PortDirection::Undefined: default: return QString();
    }
}

PortDirection portDirectionFromString(const QString &directionText)
{
    const QString normalized = directionText.trimmed().toLower();
    if (normalized == kDirectionInput) return PortDirection::Input;
    if (normalized == kDirectionOutput) return PortDirection::Output;
    if (normalized == kDirectionInOut || normalized == QString("bidirectional"))
        return PortDirection::Bidirectional;
    if (normalized == kDirectionInternal) return PortDirection::Internal;
    return PortDirection::Undefined;
}

bool ContainerPort::isValid() const
{
    return !name.trimmed().isEmpty();
}

QJsonObject ContainerPort::toJson() const
{
    QJsonObject obj;
    if (!id.isEmpty()) obj.insert(QString("id"), id);
    if (!name.isEmpty()) obj.insert(QString("name"), name);
    if (!category.isEmpty()) obj.insert(QString("category"), category);
    if (!quantity.isEmpty()) obj.insert(QString("quantity"), quantity);
    if (direction != PortDirection::Undefined)
        obj.insert(QString("direction"), portDirectionToString(direction));
    if (!unit.isEmpty()) obj.insert(QString("unit"), unit);
    if (!bounds.isEmpty()) obj.insert(QString("bounds"), QJsonObject::fromVariantMap(bounds));
    if (!signalId.isEmpty()) obj.insert(QString("signalId"), signalId);
    if (!mappedSymbol.isEmpty()) obj.insert(QString("mappedSymbol"), mappedSymbol);
    if (sourceContainerId != 0) obj.insert(QString("sourceContainerId"), sourceContainerId);
    if (optional) obj.insert(QString("optional"), optional);
    if (!description.isEmpty()) obj.insert(QString("description"), description);
    if (!alias.isEmpty()) obj.insert(QString("alias"), alias);
    return obj;
}

ContainerPort ContainerPort::fromJson(const QJsonObject &object)
{
    ContainerPort port;
    port.id = object.value(QString("id")).toString();
    port.name = object.value(QString("name")).toString();
    port.category = object.value(QString("category")).toString();
    port.quantity = object.value(QString("quantity")).toString();
    port.direction = portDirectionFromString(object.value(QString("direction")).toString());
    port.unit = object.value(QString("unit")).toString();
    if (object.contains(QString("bounds")))
        port.bounds = object.value(QString("bounds")).toObject().toVariantMap();
    port.signalId = object.value(QString("signalId")).toString();
    port.mappedSymbol = object.value(QString("mappedSymbol")).toString();
    port.sourceContainerId = object.value(QString("sourceContainerId")).toInt();
    port.optional = object.value(QString("optional")).toBool(false);
    port.description = object.value(QString("description")).toString();
    port.alias = object.value(QString("alias")).toString();
    return port;
}

QString behaviorModeTypeToString(BehaviorModeType type)
{
    switch (type) {
    case BehaviorModeType::Normal: return QString("normal");
    case BehaviorModeType::Fault: return QString("fault");
    case BehaviorModeType::CommonFault: return QString("commonFault");
    case BehaviorModeType::DerivedFault: return QString("derivedFault");
    default: return QString("fault");
    }
}

BehaviorModeType behaviorModeTypeFromString(const QString &text)
{
    const QString normalized = text.trimmed().toLower();
    if (normalized == QString("normal")) return BehaviorModeType::Normal;
    if (normalized == QString("commonfault")) return BehaviorModeType::CommonFault;
    if (normalized == QString("derivedfault")) return BehaviorModeType::DerivedFault;
    return BehaviorModeType::Fault;
}

QJsonObject BehaviorMode::toJson() const
{
    QJsonObject obj;
    if (!modeId.isEmpty()) obj.insert(QString("id"), modeId);
    if (!displayName.isEmpty()) obj.insert(QString("name"), displayName);
    obj.insert(QString("type"), behaviorModeTypeToString(modeType));
    obj.insert(QString("probability"), probability);
    QJsonArray constraintArray;
    for (const QString &constraint : constraints)
        constraintArray.append(constraint);
    if (!constraintArray.isEmpty()) obj.insert(QString("constraints"), constraintArray);
    if (!sourceContainers.isEmpty()) {
        QJsonArray sources;
        for (int id : sourceContainers) sources.append(id);
        obj.insert(QString("sources"), sources);
    }
    if (!z3StateSymbol.isEmpty()) obj.insert(QString("stateSymbol"), z3StateSymbol);
    if (!annotations.isEmpty()) obj.insert(QString("annotations"), QJsonObject::fromVariantMap(annotations));
    return obj;
}

BehaviorMode BehaviorMode::fromJson(const QJsonObject &object)
{
    BehaviorMode mode;
    mode.modeId = object.value(QString("id")).toString();
    mode.displayName = object.value(QString("name")).toString();
    mode.modeType = behaviorModeTypeFromString(object.value(QString("type")).toString());
    mode.probability = object.value(QString("probability")).toDouble();
    const QJsonArray constraintArray = object.value(QString("constraints")).toArray();
    for (const QJsonValue &value : constraintArray)
        mode.constraints.append(value.toString());
    const QJsonArray sources = object.value(QString("sources")).toArray();
    for (const QJsonValue &value : sources)
        mode.sourceContainers.append(value.toInt());
    mode.z3StateSymbol = object.value(QString("stateSymbol")).toString();
    if (object.contains(QString("annotations")))
        mode.annotations = object.value(QString("annotations")).toObject().toVariantMap();
    return mode;
}

QJsonObject BehaviorSpec::toJson() const
{
    QJsonObject obj;
    obj.insert(QString("normal"), normalMode.toJson());
    QJsonArray faults;
    for (const BehaviorMode &fault : faultModes)
        faults.append(fault.toJson());
    obj.insert(QString("faults"), faults);
    if (!rationale.isEmpty()) obj.insert(QString("rationale"), rationale);
    return obj;
}

BehaviorSpec BehaviorSpec::fromJson(const QJsonObject &object)
{
    BehaviorSpec spec;
    if (object.contains(QString("normal")))
        spec.normalMode = BehaviorMode::fromJson(object.value(QString("normal")).toObject());
    const QJsonValue faultsValue = object.value(QString("faults"));
    if (faultsValue.isArray()) {
        const QJsonArray faults = faultsValue.toArray();
        for (const QJsonValue &value : faults)
            spec.faultModes.append(BehaviorMode::fromJson(value.toObject()));
    }
    spec.rationale = object.value(QString("rationale")).toString();
    return spec;
}

bool BehaviorSpec::isEmpty() const
{
    return normalMode.modeId.isEmpty() && faultModes.isEmpty();
}

ContainerData::ContainerData()
    : m_entity()
{
    readPortsFromEntity();
    readBehaviorFromEntity();
    readTestsFromEntity();
    readAnalysisFromEntity();
    m_behaviorSmt = m_entity.behaviorSmt();
}

ContainerData::ContainerData(const ContainerEntity &entity)
    : m_entity(entity)
{
    readPortsFromEntity();
    readBehaviorFromEntity();
    readTestsFromEntity();
    readAnalysisFromEntity();
    m_behaviorSmt = m_entity.behaviorSmt();
}

const ContainerEntity &ContainerData::entity() const
{
    return m_entity;
}

ContainerEntity &ContainerData::entity()
{
    return m_entity;
}

const QVector<ContainerPort> &ContainerData::ports() const
{
    return m_ports;
}

void ContainerData::setPorts(const QVector<ContainerPort> &ports)
{
    m_ports = ports;
    writePortsToEntity();
}

const BehaviorSpec &ContainerData::behavior() const
{
    return m_behavior;
}

void ContainerData::setBehavior(const BehaviorSpec &behavior)
{
    m_behavior = behavior;
    writeBehaviorToEntity();
}

QString ContainerData::behaviorSmt() const
{
    return m_behaviorSmt;
}

void ContainerData::setBehaviorSmt(const QString &smt)
{
    m_behaviorSmt = smt;
    m_entity.setBehaviorSmt(smt);
}

const QVector<GeneratedTest> &ContainerData::tests() const
{
    return m_tests;
}

void ContainerData::setTests(const QVector<GeneratedTest> &tests)
{
    m_tests = tests;
    writeTestsToEntity();
}

int ContainerData::analysisDepth() const
{
    return m_entity.analysisDepth();
}

void ContainerData::setAnalysisDepth(int depth)
{
    m_entity.setAnalysisDepth(depth);
}

QVariantMap ContainerData::analysisData() const
{
    return m_analysisData;
}

void ContainerData::setAnalysisData(const QVariantMap &data)
{
    m_analysisData = data;
    writeAnalysisToEntity();
}

void ContainerData::readPortsFromEntity()
{
    m_ports.clear();
    const QString json = m_entity.interfaceJson();
    if (json.trimmed().isEmpty()) return;

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (error.error != QJsonParseError::NoError || doc.isNull()) return;

    QJsonArray array;
    if (doc.isArray()) {
        array = doc.array();
    } else if (doc.isObject()) {
        const QJsonObject obj = doc.object();
        if (obj.contains(QString("ports")))
            array = obj.value(QString("ports")).toArray();
    }

    for (const QJsonValue &value : array) {
        if (!value.isObject()) continue;
        ContainerPort port = ContainerPort::fromJson(value.toObject());
        if (port.isValid()) m_ports.append(port);
    }
}

void ContainerData::readBehaviorFromEntity()
{
    m_behavior = BehaviorSpec{};
    const QString json = m_entity.faultModesJson();
    if (json.trimmed().isEmpty()) return;

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (error.error != QJsonParseError::NoError || doc.isNull()) return;

    if (doc.isObject()) {
        m_behavior = BehaviorSpec::fromJson(doc.object());
    } else if (doc.isArray()) {
        QJsonObject wrapper;
        wrapper.insert(QString("faults"), doc.array());
        m_behavior = BehaviorSpec::fromJson(wrapper);
    }
}

void ContainerData::readTestsFromEntity()
{
    m_tests.clear();
    const QString json = m_entity.testsJson();
    if (json.trimmed().isEmpty()) return;

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (error.error != QJsonParseError::NoError || doc.isNull()) return;

    QJsonArray array;
    if (doc.isArray())
        array = doc.array();
    else if (doc.isObject())
        array = doc.object().value(QString("tests")).toArray();

    for (const QJsonValue &value : array) {
        if (!value.isObject()) continue;
        m_tests.append(GeneratedTest::fromJson(value.toObject()));
    }
}

void ContainerData::readAnalysisFromEntity()
{
    m_analysisData.clear();
    const QString json = m_entity.analysisJson();
    if (json.trimmed().isEmpty()) return;

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (error.error != QJsonParseError::NoError || !doc.isObject()) return;

    m_analysisData = doc.object().toVariantMap();
}

void ContainerData::writePortsToEntity()
{
    QJsonArray array;
    for (const ContainerPort &port : m_ports) {
        if (!port.isValid()) continue;
        array.append(port.toJson());
    }
    if (array.isEmpty()) {
        m_entity.setInterfaceJson(QString());
    } else {
        const QJsonDocument doc(array);
        m_entity.setInterfaceJson(QString::fromUtf8(doc.toJson(QJsonDocument::Compact)));
    }
}

void ContainerData::writeBehaviorToEntity()
{
    if (m_behavior.isEmpty()) {
        m_entity.setFaultModesJson(QString());
        return;
    }
    const QJsonDocument doc(m_behavior.toJson());
    m_entity.setFaultModesJson(QString::fromUtf8(doc.toJson(QJsonDocument::Compact)));
}

void ContainerData::writeTestsToEntity()
{
    if (m_tests.isEmpty()) {
        m_entity.setTestsJson(QString());
        return;
    }
    QJsonArray array;
    for (const GeneratedTest &test : m_tests)
        array.append(test.toJson());
    const QJsonDocument doc(array);
    m_entity.setTestsJson(QString::fromUtf8(doc.toJson(QJsonDocument::Compact)));
}

void ContainerData::writeAnalysisToEntity()
{
    if (m_analysisData.isEmpty()) {
        m_entity.setAnalysisJson(QString());
        return;
    }
    const QJsonObject obj = QJsonObject::fromVariantMap(m_analysisData);
    const QJsonDocument doc(obj);
    m_entity.setAnalysisJson(QString::fromUtf8(doc.toJson(QJsonDocument::Compact)));
}
