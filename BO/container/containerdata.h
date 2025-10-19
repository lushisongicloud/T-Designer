#ifndef CONTAINERDATA_H
#define CONTAINERDATA_H

#include <QJsonObject>
#include <QString>
#include <QStringList>
#include <QVariantMap>
#include <QVector>

#include "DO/containerentity.h"
#include "BO/test/testdefinition.h"

enum class PortDirection {
    Input,
    Output,
    Bidirectional,
    Internal,
    Undefined
};

QString portDirectionToString(PortDirection direction);
PortDirection portDirectionFromString(const QString &directionText);

struct ContainerPort {
    QString id;
    QString name;
    QString category;
    QString quantity;
    PortDirection direction = PortDirection::Undefined;
    QString unit;
    QVariantMap bounds;
    QString signalId;
    QString mappedSymbol;
    int sourceContainerId = 0;
    bool optional = false;
    QString description;
    QString alias;

    bool isValid() const;
    QJsonObject toJson() const;
    static ContainerPort fromJson(const QJsonObject &object);
};

enum class BehaviorModeType {
    Normal,
    Fault,
    CommonFault,
    DerivedFault
};

QString behaviorModeTypeToString(BehaviorModeType type);
BehaviorModeType behaviorModeTypeFromString(const QString &text);

struct BehaviorMode {
    QString modeId;
    QString displayName;
    BehaviorModeType modeType = BehaviorModeType::Normal;
    double probability = 0.0;
    QStringList constraints;
    QVector<int> sourceContainers;
    QString z3StateSymbol;
    QVariantMap annotations;

    QJsonObject toJson() const;
    static BehaviorMode fromJson(const QJsonObject &object);
};

struct BehaviorSpec {
    BehaviorMode normalMode;
    QVector<BehaviorMode> faultModes;
    QString rationale;

    QJsonObject toJson() const;
    static BehaviorSpec fromJson(const QJsonObject &object);
    bool isEmpty() const;
};

class ContainerData {
public:
    ContainerData();
    explicit ContainerData(const ContainerEntity &entity);

    const ContainerEntity &entity() const;
    ContainerEntity &entity();

    const QVector<ContainerPort> &ports() const;
    void setPorts(const QVector<ContainerPort> &ports);

    const BehaviorSpec &behavior() const;
    void setBehavior(const BehaviorSpec &behavior);

    QString behaviorSmt() const;
    void setBehaviorSmt(const QString &smt);

    const QVector<GeneratedTest> &tests() const;
    void setTests(const QVector<GeneratedTest> &tests);

    int analysisDepth() const;
    void setAnalysisDepth(int depth);

    QVariantMap analysisData() const;
    void setAnalysisData(const QVariantMap &data);

private:
    ContainerEntity m_entity;
    QVector<ContainerPort> m_ports;
    BehaviorSpec m_behavior;
    QVector<GeneratedTest> m_tests;
    QString m_behaviorSmt;
    QVariantMap m_analysisData;

    void readPortsFromEntity();
    void readBehaviorFromEntity();
    void readTestsFromEntity();
    void readAnalysisFromEntity();
    void writePortsToEntity();
    void writeBehaviorToEntity();
    void writeTestsToEntity();
    void writeAnalysisToEntity();
};

#endif // CONTAINERDATA_H
