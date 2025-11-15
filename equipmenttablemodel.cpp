#include "equipmenttablemodel.h"
#include <QIcon>
#include <QColor>
#include "performancetimer.h"

EquipmentTableModel::EquipmentTableModel(QObject *parent)
    : QAbstractTableModel(parent)
{
}

int EquipmentTableModel::rowCount(const QModelIndex &parent) const
{
    Q_UNUSED(parent);
    return m_dataRows.size();
}

int EquipmentTableModel::columnCount(const QModelIndex &parent) const
{
    Q_UNUSED(parent);
    return Column_COUNT;
}

QVariant EquipmentTableModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid() || index.row() >= m_dataRows.size() || index.row() < 0) {
        return QVariant();
    }

    const TableRow &row = m_dataRows[index.row()];

    if (role == Qt::DisplayRole) {
        switch (index.column()) {
        case Column_Sequence:
            return index.row() + 1;
        case Column_UnitTag:
            return row.unitTag;
        case Column_Type:
            return row.type;
        case Column_Name:
            return row.name;
        case Column_Quantity:
            return row.quantity;
        case Column_Factory:
            return row.factory;
        case Column_PartCode:
            return row.partCode;
        case Column_Remark:
            return row.remark;
        default:
            return QVariant();
        }
    } else if (role == Qt::UserRole) {
        // 返回equipmentId，用于双击等操作
        if (index.column() == Column_Sequence) {
            return row.equipmentId;
        }
    } else if (role == Qt::TextAlignmentRole) {
        // 序号和数量右对齐
        if (index.column() == Column_Sequence || index.column() == Column_Quantity) {
            return QVariant(Qt::AlignCenter);
        }
        return QVariant(Qt::AlignLeft | Qt::AlignVCenter);
    }

    return QVariant();
}

QVariant EquipmentTableModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal) {
        if (role == Qt::DisplayRole) {
            if (section >= 0 && section < m_columnNames.size()) {
                return m_columnNames[section];
            }
        }
    }
    return QAbstractTableModel::headerData(section, orientation, role);
}

void EquipmentTableModel::setProjectDataModel(ProjectDataModel *model)
{
    m_projectDataModel = model;
    refresh();
}

void EquipmentTableModel::setAggregatedMode(bool aggregated)
{
    if (m_aggregatedMode != aggregated) {
        m_aggregatedMode = aggregated;
        refresh();
    }
}

void EquipmentTableModel::refresh()
{
    beginResetModel();
    m_dataRows.clear();

    if (m_projectDataModel && m_projectDataModel->isLoaded()) {
        buildModelData();
    }

    endResetModel();
}

void EquipmentTableModel::buildModelData()
{
    if (!m_projectDataModel) {
        return;
    }

    const auto *equipmentMgr = m_projectDataModel->equipmentManager();
    if (!equipmentMgr) {
        return;
    }

    QVector<int> equipmentIds = equipmentMgr->getAllEquipmentIds();

    if (!m_aggregatedMode) {
        // 非聚合模式：每个器件一行
        m_dataRows.reserve(equipmentIds.size());

        for (int equipmentId : equipmentIds) {
            const EquipmentData *equipment = equipmentMgr->getEquipment(equipmentId);
            if (!equipment) {
                continue;
            }

            TableRow row;
            row.equipmentId = equipment->id;
            row.unitTag = buildUnitTag(equipment);
            row.type = equipment->type;
            row.name = equipment->name;
            row.quantity = 1;
            row.factory = equipment->factory;
            row.partCode = equipment->partCode;
            row.remark = equipment->remark;

            m_dataRows.append(row);
        }
    } else {
        // 聚合模式：按partCode聚合
        QMap<QString, TableRow> aggregatedMap;

        for (int equipmentId : equipmentIds) {
            const EquipmentData *equipment = equipmentMgr->getEquipment(equipmentId);
            if (!equipment || equipment->partCode.isEmpty()) {
                continue;
            }

            TableRow &row = aggregatedMap[equipment->partCode];
            if (row.quantity == 0) {
                // 首次插入
                row.equipmentId = equipment->id;
                row.unitTag = buildUnitTag(equipment);
                row.type = equipment->type;
                row.name = equipment->name;
                row.factory = equipment->factory;
                row.partCode = equipment->partCode;
                row.remark = equipment->remark;
            }
            row.quantity += 1;
        }

        m_dataRows = aggregatedMap.values().toVector();
    }
}

QString EquipmentTableModel::buildUnitTag(const EquipmentData *equipment) const
{
    if (!equipment) {
        return QString();
    }

    QString tag = equipment->dt;

    // 如果有结构信息，添加到前面
    if (m_projectDataModel) {
        const auto *structureMgr = m_projectDataModel->structureManager();
        if (structureMgr && equipment->structureId > 0) {
            QString structureTag = structureMgr->getFullPath(equipment->structureId);
            if (!structureTag.isEmpty()) {
                tag = structureTag + "-" + tag;
            }
        }
    }

    return tag;
}

int EquipmentTableModel::getEquipmentIdAt(int row) const
{
    if (row >= 0 && row < m_dataRows.size()) {
        return m_dataRows[row].equipmentId;
    }
    return 0;
}
