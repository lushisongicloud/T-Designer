#ifndef DIAGNOSISGRAPH_H
#define DIAGNOSISGRAPH_H
#include "BO/componententity.h"
#include "BO/systementity.h"
#include <QMap>
#include <QString>
#include <QStringList>
#include <QDebug>
#include <QRegularExpression>

// 定义节点类型的常量
const short GENERAL_PORT = 0;      // 一般端口
const short SOURCE_PORT = 1;       // 源端口
const short ACTUATOR_PORT = 2;     // 执行器端口

class Node;
class Edge;
class Dependency;
class SubComponent;
class Pathway;

// 定义了一个结构，代表路径元素，可以是SubComponent或Edge
struct PathElement {
    QSharedPointer<SubComponent> subComponent;
    QSharedPointer<Edge> edge;
};

struct RouteItem {
    QSharedPointer<SubComponent> subComponent;
    QSharedPointer<Edge> edge;
    bool isDependencyTarget = false; // 标记是否为Dependency的target
    QString dependencyFunctionName = ""; // 如果需要记录依赖功能名
    bool orLogicType = false; // 逻辑操作类型
    QList<RouteItem> subItems; // 子路径项

    RouteItem(QSharedPointer<Edge> e) : edge(e) {} // 只接收edge的构造函数
    RouteItem(bool orLogic, QList<RouteItem>& i) : orLogicType(orLogic), subItems(i) {}
    RouteItem(QSharedPointer<SubComponent> s) : subComponent(s) {} // 只接收subComponent的构造函数
    RouteItem(QSharedPointer<SubComponent> s,bool idt,QString dfn) : subComponent(s),isDependencyTarget(idt), dependencyFunctionName(dfn) {}
};

// 定义节点，这些节点对应器件的实体端口，在同一个功能中其名称具有唯一性，
// 如果在多条链路中出现了相同name的Node，实际上是唯一的一个Node具有多个边（连接）
// 每个节点都包含于唯一的逻辑支路器件中
class Node {
public:
    //构造函数
    Node(const QString& n, short t = GENERAL_PORT)
        : name(n), type(t)  {}

    QString name; // 器件的实体端口名称，例如KM.1
    short type;  // 节点的类型，默认为一般端口
    QList<QMap<QString, double>> variableValuesMapList;  // 存储与该节点相关的变量和值
    QList<QSharedPointer<Edge>> connectedEdges;
    QList<QSharedPointer<Pathway>> connectedPathways;
    QSharedPointer<SubComponent> containingSubComponent;
};

// 定义 Pathway（器件内部的联接关系），这些路径代表器件实体端口间的内部能量通路或路径。
class Pathway {
public:
    Pathway(QSharedPointer<Node> s, QSharedPointer<Node> t, double fProb) : source(s), target(t),failureProbability(fProb) {}
    QSharedPointer<Node> source;   // 起始节点
    QSharedPointer<Node> target;   // 目标节点
    double failureProbability; //所属器件的整体失效概率
};

//逻辑支路器件
class SubComponent {
public:
    //构造函数
    SubComponent(const QList<QSharedPointer<Node>>& nodeList, double fProb, bool isDependent = true)
        : nodes(nodeList), failureProbability(fProb), isComponentDependency(isDependent) {
        generateName();
    }
    QString name; //逻辑支路器件名称：器件名称.port1_port2_......，例如一逻辑支路器件包含3个Node:KM.1,KM.2,KM.3.A1,则name=KM.1_2_3.A1
    QList<QSharedPointer<Node>> nodes;
    QList<QSharedPointer<Dependency>> connectedDependencies;
    double failureProbability;//该逻辑支路器件所属器件的整体失效概率
    bool isComponentDependency;//该逻辑支路是否在functionComponentDependencyMap当前功能对应的依赖器件中
    // 添加新的Node到nodes列表中
    void addNodeToSubComponent(QSharedPointer<Node> newNode) {nodes.append(newNode);generateName();}
    bool containsNode(const QString& nodeName) {for (const auto& node : nodes) {if (node->name == nodeName) {return true;}} return false;}

    // 根据nodes列表生成逻辑支路器件名称
    void generateName() {
        QStringList nodeNameList;
        for (const auto& node : nodes) nodeNameList.append(node->name.simplified());

        std::sort(nodeNameList.begin(), nodeNameList.end());
        for (int i = 0; i < nodeNameList.size(); ++i) {
            QString& modifiedName = nodeNameList[i];
            if (i == 0) continue; // 对于第一个名称，保留整体
            int dotIndex = modifiedName.indexOf('.');
            if (dotIndex == -1) qDebug() << "Error: Node name does not contain a '.' character: " << modifiedName;
            else modifiedName = modifiedName.mid(dotIndex + 1);
        }
        name = nodeNameList.join('&');
    }
};

// 定义边（器件外部的联接关系），这些边代表器件实体端口间的物理联接（共享变量），此物理连接不考虑失效，联接的两端对应变量相等。
class Edge {
public:
    Edge(QSharedPointer<Node> s, QSharedPointer<Node> t) : source(s), target(t), entropy(0), eValue(0), fValue(0) {name = s->name.simplified()+"&"+t->name.simplified();}
    QSharedPointer<Node> source;
    QSharedPointer<Node> target;
    QString name; //source的名称&target的名称
    QStringList parents;
    double entropy;
    int level=0;
    bool recommended=false;
    double eValue;  // 势变量的值
    double fValue;  // 流变量的值
};
//定义边（器件内部的依赖关系），这些变代码器件实体端口间在器件内部的依赖关系，该依赖关系考虑失效，失效概率等于器件的整体失效概率
//由执行器指向目标subComponent
class Dependency {
public:
    Dependency(const QString& n, QSharedPointer<SubComponent> s, QSharedPointer<SubComponent> t, double fProb) :depFuncName(n), source(s), target(t), failureProbability(fProb) {}
    QString depFuncName;
    QSharedPointer<SubComponent> source;
    QSharedPointer<SubComponent> target;
    double failureProbability;
};

class DiagnosisGraph {
private:

public:
    QMap<QString, QList<RouteItem>> funcNameToRouteMap;
    QList<QSharedPointer<Node>> nodes;// 使用QSharedPointer
    QList<QSharedPointer<SubComponent>> subComponents;
    QList<QSharedPointer<Edge>> edges;
    QList<QSharedPointer<Dependency>> dependencies;
    QList<QSharedPointer<Pathway>> pathways;

    QMap<QString,QMap<QString, QSharedPointer<Node>>> nameToNodeMap;  // 通过功能名与端口名称快速查找节点
    QMap<QString, QSharedPointer<SubComponent>> funcNameToSourceSubComponentMap;  // 通过功能名称快速查找源SubComponent
    QMap<QString, QSharedPointer<SubComponent>> funcNameToActuatorSubComponentMap;  // 通过功能名称快速查找执行器SubComponent

    QString mCurrentfunctionName;//当前被诊断功能名
    QList<QStringList> mPortListInConnectionList; //连接中的端口列表，所有的连接再构成一个列表
    //    QMap<QString, QString> mFunctionLinkMap;//功能名-链路信息
    //    QMap<QString, QString> mFunctionComponentDependencyMap;//功能名-器件依赖关系
    //    QMap<QString, QString> mFunctionDependencyMap;//功能名-功能依赖关系
    QMap<QString, double> mCompFailureProbMap; //器件名称-先验失效概率
    QMap<QString, FunctionInfo> mFunctionInfoMap;

    QStringList mFunctionDependencyChain;

    QSet<QString> processedFunctions;
    QSet<QString> processedFunctionLinks;

    QMap<QString, double> subComponentProbMap;

    void addFunctionDependencies(const QString& functionName,int level);
    void handleLinkNodes(const QStringList& currentLink,const QString& currentFunctionName,int level);
    void handleFunctionDependencies(const QString& depFunc, const QString& currPort);
    void handleEndNodes(const QStringList& currentLink, const QString& currentFunctionName);
    QSharedPointer<Node> getNodeOrCreate(const QString& portName, short type, const QString& funcName);
    QSharedPointer<SubComponent> getOrCreateSubComponent(const QString& port, short portType, const QString& funcName);
public:
    DiagnosisGraph();
    // 添加节点和边的方法
    void addNode(const QString& functionName, QSharedPointer<Node> node);
    void addSubComponent(QSharedPointer<SubComponent> subComponent);
    void addEdge(QSharedPointer<Edge> edge);
    void addDependency(QSharedPointer<Dependency> dependency);
    void addPathway(QSharedPointer<Pathway> pathway);

    // 基于提供的输入数据构建图
    void buildGraph(const QString& currentfunctionName,
                    const QMap<QString, FunctionInfo>& functionInfoMap,
                    const QList<QStringList>& portListInConnectionList,
                    const QMap<QString, double>& compFailureProbMap);

    QMap<QString, double> normalizeFaultProbabilities(QList<resultEntity>& currentResultEntityList);
    QMap<QString, double> calSubComponentFailureProb(QMap<QString, double>& failureModeProbMap);
    double calcTestEntropy(QList<RouteItem>& route, int edgeIndex);
    double calcEquivalentFailureProb(const RouteItem& currentSubComp, QSet<QString>& processedSubComps, bool readOnly=false);
    QList<TestItem> generateTestItemsFromEdges(const QList<QSharedPointer<Edge>>& testEdgeList);
    double calcProbability(const RouteItem& routeItem, QSet<QString>& processedSubComps, QSet<QString>& processedDepFuncs);
    //void addDepToRoute(QList<RouteItem>& route, QSet<QString>& processedRouteItem, int startIndex=0);
    QList<RouteItem> addDepToRoute(const QString functionName, QSet<QString>& processedRouteItem, QSet<QString>& processedFunc);
    QList<QSharedPointer<Edge>> calcRouteEntropy(QList<RouteItem>& route);

    //返回测点推荐列表
    QList<TestItem> getRecommendTestItemList(QString functionName,QList<resultEntity>& currentResultEntityList,bool isPenetrativeSolve);

    //返回测点推荐列表，QString为参照功能(Referential Function)的名称，double为执行参照功能后系统的综合信息熵
    QList<QMap<QString,double>> getRecommendFunction(QList<resultEntity>& currentResultEntityList);
};

// 重载QDebug输出操作符，方便调试
QDebug operator<<(QDebug dbg, const Node& node);
QDebug operator<<(QDebug dbg, const SubComponent& subComponent);
QDebug operator<<(QDebug dbg, const Edge& edge);
QDebug operator<<(QDebug dbg, const Dependency& dependency);
QDebug operator<<(QDebug dbg, const Pathway& pathway);
QDebug operator<<(QDebug dbg, const DiagnosisGraph& diagnosisGraph);
QDebug operator<<(QDebug debug, const RouteItem& item);
#endif // DIAGNOSISGRAPH_H
