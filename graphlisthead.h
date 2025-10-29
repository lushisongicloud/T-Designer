#ifndef GRAPHLISTHEAD_H
#define GRAPHLISTHEAD_H

#include <QString>

/*
.	图（邻接表实现） Graph Adjacency List
.	相关术语：
.		顶点 Vertex ； 边 Arc ；权 Weight ；
.		有向图 Digraph ；无向图 Undigraph ；
.		有向网 Directed Network ；无向网 Undirected Network ；
.	存储结构：
.		1.顶点表只能采用顺序结构。（因为若采用链式结构，顶点结点定义与边表结点定义就相互引用，无法定义）
.		2.边表采用链表结构。
*/



struct ArcNode
{
    int adjVex;			//邻接顶点所在表中下标
    int weight;			//边权重
    ArcNode * next;		//下一条边
};
/*
.	顶点表（顺序表）结点
*/
struct VNode
{
    QString name;		//顶点名
    ArcNode * first;	//指向的第一个依附该顶点的顶点边结点

    int out_num;        //出度,注意由于是无向图，出度已经包括了所有连接的端点
};



//	边（弧）数据，注：供外部初始化边数据使用

struct ArcData
{
    QString Tail;	//弧尾
    QString Head;	//弧头
    int Weight;		//权重
};

#endif // GRAPHLISTHEAD_H
