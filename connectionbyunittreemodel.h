#ifndef CONNECTIONBYUNITTREEMODEL_H
#define CONNECTIONBYUNITTREEMODEL_H

#include <QAbstractItemModel>
#include <QVector>
#include <QString>
#include <QHash>
#include "projectdatamodel.h"

class ProjectDataCache;

/**
 * @brief ConnectionByUnitTreeModel - 按单元分组的连线树 Model/View实现
 *
 * 替代传统的 QStandardItemModel + SQL查询模式
 * 结构：项目 → 高层 → 位置 → 元件/端子排 → 连线端点
 */
class ConnectionByUnitTreeModel : public QAbstractItemModel
{
    Q_OBJECT

public:
    enum NodeType {
        Type_Root = 0,           // 项目根节点
        Type_Gaoceng,            // 高层
        Type_Position,           // 位置
        Type_UnitStrip,          // 元件或端子排
        Type_ConnectionEnd       // 连线端点
    };

    explicit ConnectionByUnitTreeModel(QObject *parent = nullptr);

    // Basic functionality
    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex index(int row, int column, const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex parent(const QModelIndex &child) const override;

    QVariant data(const QModelIndex &index, int role = Qt::DisplayRole) const override;
    QVariant headerData(int section, Qt::Orientation orientation, int role = Qt::DisplayRole) const override;

    // 设置数据源
    void setProjectDataModel(ProjectDataModel *model);
    void setProjectDataCache(ProjectDataCache *cache);
    void rebuild();
    void clear();

    // 工具方法
    NodeType getNodeType(const QModelIndex &index) const;
    int getConnectionId(const QModelIndex &index) const;
    int getUnitStripId(const QModelIndex &index) const;
    QString getGaoceng(const QModelIndex &index) const;
    QString getPosition(const QModelIndex &index) const;

private:
    void buildTreeData();
    QString buildUnitStripDisplayText(int unitStripId, const QString &category, const QString &dt) const;
    QString buildConnectionEndText(const ConnectionData *connection, int endpointIndex) const;
    QString getSymbolDisplayText(int symbolId) const;
    QString getTerminalDisplayText(int terminalInstanceId) const;
    QString getEquipmentDisplayText(int equipmentId) const;
    QString getTerminalStripDisplayText(int terminalStripId) const;

    // 节点结构
    struct TreeNode {
        NodeType type;
        QString displayText;
        QString gaoceng;           // 高层名称
        QString position;          // 位置名称
        int structureId = 0;       // 结构ID
        int connectionId = 0;      // 连线ID (JXB_ID)
        int unitStripId = 0;       // 元件或端子排ID
        int endpointIndex = 0;     // 端点索引 (0: Symb1, 1: Symb2)
        QString category;          // 类别 (0:元件, 1:端子排)
        QString symbId;
        QString otherSymbId;
        QString otherCategory;
        QVector<TreeNode*> children;
        TreeNode *parent = nullptr;

        explicit TreeNode(NodeType t) : type(t) {}
        ~TreeNode() { qDeleteAll(children); }
    };

    // 根节点
    TreeNode *m_rootNode = nullptr;
    ProjectDataModel *m_projectDataModel = nullptr;
    ProjectDataCache *m_projectCache = nullptr;

    // 缓存映射：快速查找
    QMap<QString, TreeNode*> m_gaocengKeyToNode;      // "StructureId" -> GaocengNode
    QMap<QString, TreeNode*> m_posKeyToNode;          // "Gaoceng|Position" -> PosNode
    QMap<QString, TreeNode*> m_unitKeyToNode;         // "Gaoceng|Pos|UnitId|Category" -> UnitNode
};

#endif // CONNECTIONBYUNITTREEMODEL_H
