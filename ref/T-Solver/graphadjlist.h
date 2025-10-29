#ifndef GRAPHADJLIST_H
#define GRAPHADJLIST_H

#include <QString>
#include <QVector>
#include <QQueue>
#include <QDebug>
#include <QTime>
#include <QSet>
#include "graphlisthead.h"
#include "combotree.h"
#include "cutthread.h"



//	图 种类
enum GraphType
{
    DG,			//有向图，默认 0
    UDG,		//无向图，默认 1
    DN,			//有向网，默认 2
    UDN			//无向网，默认 3
};
class GraphAdjList
{
public:
    GraphAdjList();
    GraphAdjList(int type);				//构造函数：初始化图种类
    ~GraphAdjList();					//析构函数
    void Init(QVector<QString> * vexs, QVector<ArcData> * arcsList);		//初始化顶点、边数据为 图|网
    void InsertArc(ArcData * arcData);			//插入边（含有向/无向操作）
    void DeleteArc(ArcData * arcData);			//删除边（含有向/无向操作）
    void Display();								//显示 图|网
    void Display_DFS_R(QString *vertex);		 	//从指定顶点开始，深度优先 递归 遍历
    void Display_DFS(QString *vertex);			//从指定顶点开始，深度优先 非递归 遍历
    void Display_BFS(QString *vertex);			//从指定顶点开始，广度优先遍历
    void ClearGraph();                          //清空

    QList<QStringList> CandidateConflict();     //返回所有连接的排列组合

    void ShowAllPort();



    static const int _MAX_VERTEX_NUM = 50;		//支持最大顶点数

    VNode vexs[_MAX_VERTEX_NUM];				//顶点表
private:


    int vexs_visited[_MAX_VERTEX_NUM];			//顶点访问标记数组：0|未访问 1|已访问
    int vexs_comb_visited[_MAX_VERTEX_NUM];     //排列组合时用过的标记数组：0|未访问 1|已访问
    int vexNum;			//顶点数
    int arcNum;			//边数
    int type;			//图种类

    void _CreateVexSet(QVector<QString> * vexs);			//创建顶点集合
    void _CreateDG(QVector<ArcData> * arcsList);			//创建有向图
    void _CreateUDG(QVector<ArcData> * arcsList);			//创建无向图
    void _CreateDN(QVector<ArcData> * arcsList);			//创建有向网
    void _CreateUDN(QVector<ArcData> * arcsList);			//创建无向网

    int _Locate(QString& vertex);									//定位顶点元素位置
    void _InsertArc(int tail, int head, int weight);			//插入边（元操作，不分有向/无向）
    void _DeleteArc(int tail, int head);		    //删除边（元操作，不分有向/无向）
    void _DFS_R(int index);										//深度优先遍历 递归
    void _DFS(int index);										//深度优先遍历 非递归

    QList<QStringList> _DFS_Candidate_Confilict(int index);     //深度优先遍历 非递归,返回该点所有连接的情况
    QList<QStringList> _BFS_Candidate_Confilict(int index);     //广度优先遍历 非递归,返回该点所有连接的情况
    QList<QStringList> _DFS_Combination(QList<QStringList> list);             //针对_DFS_Candidate_Confilict提供的原始数据，进行排列组合并剔除重复的

    QList<QStringList> _Get_Circle_Combo(const QStringList& list,QList<QList<QStringList>>& combo, QVector<int>& circle_num);   //遇到循环将list分解成多个部分后，得到相连的排列组合，
    QVector<QVector<int>> _Get_Num_Combo(const QVector<QVector<int>>& totle_num);                    //在确定list不同部分所对应的序号后，将不同部分的字符串组合起来

    bool _Compare_StringList(QStringList& list1, QStringList& list2);
    void _RemoveListSameKeepSequence(QStringList& list);        //去除QStringList中重复项，并且保持顺序
    void _RemoveListSameNoSequence(QStringList& list);          //去除QStringList中重复项，顺序随机

    bool _IsComplete(QList<QStringList> my_list);
    bool _IsAComboConnect(const QVector<int>& num_list);                       //判断一个组合是否是连接在一起的

    void _CalculateOut();                                     //计算每个点的出度
    QList<QStringList> _DeleteTest();                           //通过得到所有组合，然后排除不连接的组合的方式得到结果

    void _RemoveQListIntDuplicates(QList<int>& list);        //删除QList<int>中重复的部分，并且将数据从小到大排列
private:
    ComboTree* MyTree;

};

#endif // GRAPHADJLIST_H
