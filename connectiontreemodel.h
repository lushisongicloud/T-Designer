#ifndef CONNECTIONTREEMODEL_H
#define CONNECTIONTREEMODEL_H

#include <QAbstractItemModel>
#include <QVector>
#include <QString>
#include <QHash>
#include "projectdatamodel.h"

/**
 * @brief ConnectionTreeModel - 连线树的Model/View实现
 *
 * 替代传统的QStandardItemModel + SQL查询模式
 * 结构：项目 → 高层 → 位置 → 线号 → 导线
 */
class ConnectionTreeModel : public QAbstractItemModel
{
    Q_OBJECT

public:
    enum NodeType {
        Type_Root = 0,      // 项目根节点
        Type_Gaoceng,       // 高层
        Type_Position,      // 位置
        Type_ConnectionNum, // 线号
        Type_Connection     // 导线
    };

    explicit ConnectionTreeModel(QObject *parent = nullptr);

    // Basic functionality
    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex index(int row, int column, const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex parent(const QModelIndex &child) const override;

    QVariant data(const QModelIndex &index, int role = Qt::DisplayRole) const override;
    QVariant headerData(int section, Qt::Orientation orientation, int role = Qt::DisplayRole) const override;

    // 设置数据源
    void setProjectDataModel(ProjectDataModel *model);
    void rebuild();
    void clear();

    // 工具方法
    NodeType getNodeType(const QModelIndex &index) const;
    int getConnectionId(const QModelIndex &index) const;
    QString getGaoceng(const QModelIndex &index) const;
    QString getPosition(const QModelIndex &index) const;

private:
    void buildTreeData();
    QString buildConnectionText(const ConnectionData *connection) const;
    QString buildTerminalStr(const QString &symbId, const QString &category) const;
    QString getSymbolDisplayText(int symbolId) const;
    QString getTerminalDisplayText(int terminalInstanceId) const;

    // 节点结构
    struct TreeNode {
        NodeType type;
        QString displayText;
        QString gaoceng;      // 高层名称
        QString position;     // 位置名称
        int structureId = 0;  // 结构ID
        int connectionId = 0; // 连线ID (JXB_ID)
        QVector<TreeNode*> children;
        TreeNode *parent = nullptr;

        explicit TreeNode(NodeType t) : type(t) {}
        ~TreeNode() { qDeleteAll(children); }
    };

    // 根节点
    TreeNode *m_rootNode = nullptr;
    ProjectDataModel *m_projectDataModel = nullptr;

    // 缓存映射：快速查找
    QMap<int, TreeNode*> m_structureToGaocengNode;   // structureId -> GaocengNode
    QMap<QString, TreeNode*> m_posKeyToNode;          // "Gaoceng|Position" -> PosNode
    QMap<QString, TreeNode*> m_connNumKeyToNode;      // "Gaoceng|Pos|ConnNum" -> ConnNumNode
};

#endif // CONNECTIONTREEMODEL_H
