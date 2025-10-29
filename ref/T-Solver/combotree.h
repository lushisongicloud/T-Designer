#ifndef COMBOTREE_H
#define COMBOTREE_H

#include <QStringList>
#include <QList>
#include <QDebug>
#include <QTime>


class ComboTree
{

    struct TreeNode
    {
        QString NodeName;

        QList<int> ChileNum;

        QList<QStringList> Combo;
    };


public:
    ComboTree();

    void AddNode(const QString& father, const QString& node, int layer);    //layer从0开始
    void DisplayTree();
    bool IsFinish();        //添加完一层后返回是否已经写入完整

    QList<QStringList> GetComboString();        //得到所有的连接的排列组合

    void ClearTree(){Layer.clear();}

private:
    QList<QList<TreeNode>> Layer;

private:
    int _LocateNodeInLayer(const QString& node, int layer);         //在指定层里面找节点
    int _LocateNodeLayerNum(const QString& node);                   //返回节点在第几层第一次出现

    void _InitNodeCombo();                                          //节点添加好后，把每个节点的组合计算一下
    QList<QStringList> _GetCombination(QString& head, QList<QList<QStringList>>& temp_node_combo);   //将QVector中所有QList<QStringList>*组合，每个QList<QStringList>*中挑一个
    QList<QStringList> _GetCombination(QList<QList<QStringList>>& temp_node_combo);   //将QVector中所有QList<QStringList>*组合，每个QList<QStringList>*中挑一个


    bool _Compare_StringList(QStringList list1, QStringList list2, bool isSort);
                                              //得到分组情况后，对Layer除最后一层外进行剪枝处理，去除互为父子关系的重复的部分
    bool _IsSameGrandFather(int layer, int father1, int father2);
    QList<QStringList> _ProcessLoop();                              //_InitNodeCombo后，在寻找一下有没有循环的部分，处理循环的部分
    void _SortCombo();                                              //对所有的端点的combo中每一个QStringList进行排序

    void _AddStringListToQListQStringList(const QStringList& A, QList<QStringList>& B);
};

#endif // COMBOTREE_H
