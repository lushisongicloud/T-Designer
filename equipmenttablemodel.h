#ifndef EQUIPMENTTABLEMODEL_H
#define EQUIPMENTTABLEMODEL_H

#include <QAbstractTableModel>
#include <QVector>
#include <QString>
#include "projectdatamodel.h"

/**
 * @brief EquipmentTableModel - 器件表格的Model/View实现
 *
 * 替代传统的QTableWidget + setItem模式
 * 基于ProjectDataModel提供高性能的表格显示
 */
class EquipmentTableModel : public QAbstractTableModel
{
    Q_OBJECT

public:
    enum Column {
        Column_Sequence = 0,  // 序号
        Column_UnitTag,       // 项目代号
        Column_Type,          // 型号
        Column_Name,          // 名称
        Column_Quantity,      // 数量
        Column_Factory,       // 厂家
        Column_PartCode,      // 部件编号
        Column_Remark,        // 备注
        Column_COUNT
    };

    explicit EquipmentTableModel(QObject *parent = nullptr);

    // Basic functionality
    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &parent = QModelIndex()) const override;

    QVariant data(const QModelIndex &index, int role = Qt::DisplayRole) const override;
    QVariant headerData(int section, Qt::Orientation orientation, int role = Qt::DisplayRole) const override;

    // 设置数据源
    void setProjectDataModel(ProjectDataModel *model);
    void setAggregatedMode(bool aggregated);
    void refresh();

    // 工具方法
    int getEquipmentIdAt(int row) const;

private:
    void buildModelData();
    QString buildUnitTag(const EquipmentData *equipment) const;

    struct TableRow {
        int equipmentId;
        QString unitTag;
        QString type;
        QString name;
        int quantity;
        QString factory;
        QString partCode;
        QString remark;
    };

    QVector<TableRow> m_dataRows;
    ProjectDataModel *m_projectDataModel = nullptr;
    bool m_aggregatedMode = false;

    // 预计算的显示列
    QStringList m_columnNames = {
        "序号",
        "项目代号",
        "型号",
        "名称",
        "数量",
        "厂家",
        "部件编号",
        "备注"
    };
};

#endif // EQUIPMENTTABLEMODEL_H
