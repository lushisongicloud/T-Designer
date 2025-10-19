#ifndef CONTAINERENTITY_H
#define CONTAINERENTITY_H

#include <QString>

// System hierarchy levels (top -> bottom)
enum class ContainerType {
    System = 0,
    Subsystem = 1,
    LRU = 2,
    SRU = 3,
    Module = 4,
    Submodule = 5,
    Component = 6
};

class ContainerEntity
{
public:
    ContainerEntity()
        : m_id(0)
        , m_parentId(0)
        , m_type(ContainerType::Component)
        , m_orderIndex(0)
        , m_analysisDepth(0)
        , m_equipmentId(0)
    {}

    int id() const { return m_id; }
    void setId(int id) { m_id = id; }

    int parentId() const { return m_parentId; }
    void setParentId(int parentId) { m_parentId = parentId; }

    QString name() const { return m_name; }
    void setName(const QString &name) { m_name = name; }

    ContainerType type() const { return m_type; }
    void setType(ContainerType type) { m_type = type; }

    int orderIndex() const { return m_orderIndex; }
    void setOrderIndex(int index) { m_orderIndex = index; }

    int analysisDepth() const { return m_analysisDepth; }
    void setAnalysisDepth(int depth) { m_analysisDepth = depth; }

    QString interfaceJson() const { return m_interfaceJson; }
    void setInterfaceJson(const QString &json) { m_interfaceJson = json; }

    QString behaviorSmt() const { return m_behaviorSmt; }
    void setBehaviorSmt(const QString &smt) { m_behaviorSmt = smt; }

    QString faultModesJson() const { return m_faultModesJson; }
    void setFaultModesJson(const QString &json) { m_faultModesJson = json; }

    QString testsJson() const { return m_testsJson; }
    void setTestsJson(const QString &json) { m_testsJson = json; }

    int equipmentId() const { return m_equipmentId; }
    void setEquipmentId(int id) { m_equipmentId = id; }

    QString analysisJson() const { return m_analysisJson; }
    void setAnalysisJson(const QString &json) { m_analysisJson = json; }

    QString equipmentType() const { return m_equipmentType; }
    void setEquipmentType(const QString &type) { m_equipmentType = type; }

    QString equipmentName() const { return m_equipmentName; }
    void setEquipmentName(const QString &name) { m_equipmentName = name; }

private:
    int m_id;
    int m_parentId;
    QString m_name;
    ContainerType m_type;
    int m_orderIndex;
    int m_analysisDepth;
    QString m_interfaceJson;
    QString m_behaviorSmt;
    QString m_faultModesJson;
    QString m_testsJson;
    QString m_analysisJson;
    int m_equipmentId;
    QString m_equipmentType;
    QString m_equipmentName;
};

#endif // CONTAINERENTITY_H
