#ifndef SYSTEMENTITY_H
#define SYSTEMENTITY_H

#include <QList>
#include "BO/componententity.h"
#include "BO/function/functioninfo.h"
#include "sqlitedatabase.h"
#include <z3++.h>
#include "DO/component.h"
#include "DO/parameter.h"
#include "DO/model.h"
#include <QTime>
#include <QThread>
#include <QtConcurrent>
#include <QFuture>
#include <queue>
#include "BO/worker.h"
#include "mythread.h"
#include "z3solverthread.h"
#include "graphadjlist.h"
#include "solverrunnable.h"

struct FailureEntity {
    double failureProbability;
    int index;
    bool isObservation;

    FailureEntity(double prob, int idx, bool isObs) : failureProbability(prob), index(idx), isObservation(isObs) {}

    bool operator<(const FailureEntity &rhs) const {
        return failureProbability > rhs.failureProbability; // greater probability comes first
    }
};

struct FailurePair {
    FailureEntity entity1;
    FailureEntity entity2;
    double probability;

    FailurePair(const FailureEntity& e1, const FailureEntity& e2) : entity1(e1), entity2(e2) {
        probability = e1.failureProbability * e2.failureProbability;
    }

    // This is for sorting in priority queue
    bool operator<(const FailurePair& other) const {
        return probability < other.probability;
    }
};

class MainWindow;

class SystemEntity: public QObject
{
    Q_OBJECT

public:
    SystemEntity(SQliteDatabase *database);

    void updateObsVarsMap(const QList<ComponentEntity>& componentEntityList);
    QList<ComponentEntity> prepareModel(const QString& modelDescription);
    void solveConflictSets(const QString& modelDescription ,const QList<TestItem>& testItemList);
    void solveConflictSets(const QString& modelDescription, const QString& testDescription, QList<QStringList>& list);

    void setMainWindow(MainWindow* window);
    void setCurrentModel(model* mo){currentModel = mo;}
    void setFunctionInfoMap(QMap<QString,FunctionInfo>& funcMap){functionInfoMap = funcMap;}
    QMap<QString, double> solveOutlierObs(QList<obsEntity>& obsEntityList,QList<resultEntity>& resultEntityList) const;
    QList<TestItem> RecommendObs(QString currentfunctionName, QList<QStringList> portListInConnectionList, QMap<QString, QString> functionLinkMap, QMap<QString, QString> functionComponentDependencyMap, QMap<QString, QString> functionDependencyMap, QMap<QString, double> componentFailureProbability, QList<resultEntity> currentResultEntityList);


    QString Ans;

    void SetType(int i){SoveType = i;}  //求解的模式，0是原始全排列的模式，1是利用邻接表的模式
    int Type(){return SoveType;}

    QMap<QString, QString> obsVarsMap;//观测变量-类型对
    QStringList obsVarsList;//观测变量列表
    QStringList componentNameList;//器件名称列表
    QList<resultEntity> resultEntityList;//诊断结果列表
    QMap<QString, double> componentFailureProbability; //器件名称-先验失效概率
    QMap<QString,FunctionInfo> functionInfoMap;
 private:

    int num = 0;

    double firstFailurePairProbability = 0.0;

    SQliteDatabase *database = nullptr;

    MainWindow* mainWindow;

    QList<ComponentEntity> creatComponentEntity(const QString& modelDescription);

    QString creatSystemLinkCode(const QString& systemLinkDescription);

    QString creatVariablesCode(const QList<ComponentEntity>& componentEntityList);

    QString creatTestsCode(const QString& testString);

    QList<obsEntity> creatObsEntity(const QList<TestItem>& testString);

    void solve(const QList<ComponentEntity>& componentEntityList);

    void solve(const QList<QStringList>& list, const QList<ComponentEntity>& componentEntityList);

    QList<QList<ComponentEntity>> creatCandidateConflict(const QList<ComponentEntity>& componentEntityList);

    QList<QList<ComponentEntity>> AnlysisSystemLink(const QString& systemLinkDescription,QList<ComponentEntity>& originalComponent);  //解析连接关系

    QList<QList<ComponentEntity>> creatCandidateConflictWithGraph(const QList<ComponentEntity>& componentEntityList);

    QTime timeSlove;

    int SoveType = 0;   //求解的模式，0是原始全排列的模式，1是利用邻接表的模式

    model* currentModel = nullptr;

    QList<ComponentEntity> componentEntityList;
    QList<obsEntity> obsEntityList;
    QString systemLinkCode;
    QString unchangingCode;
    QString allComponentCode;

    QString GetAns();
    bool singleFailureSolve(const FailureEntity& entity, const QString& testCode, QStringList& ans,  QList<resultEntity>& resultEntityList);
    bool doubleFailureSolve(const FailureEntity& entity1, const FailureEntity& entity2, const QString& testCode, QStringList& ans,  QList<resultEntity>& resultEntityList);

public slots:
    QList<resultEntity> completeSolve(const QString& modelDescription, const QList<TestItem>& testItemList, int truncateMode = 1, bool includeObs = true);
    void incrementalSolve(const QString& modelDescription, const QList<TestItem>& testItemList, QList<resultEntity>& currentResultEntityList,QList<resultEntity>& excludedResults);
    bool satisfiabilitySolve(const QString& modelDescription, const QList<TestItem>& testItemList);
private slots:
    void onCommandThreadEnd();

signals:
    void ProgressEnd(QStringList ans);
    void updateResultTable(const QString& FailureComponentName, const QString& FailureName, const double& pFailure);
    void updateOutlierObsTable(const QMap<QString, double>& outlierObs);

    void solvingStarted();
    void solvingFinished(QStringList ans);
    void progressUpdated(int percent);
    void resultEntityListUpdated(const QList<resultEntity>& resultEntityList);
    void outlierObsUpdated(const QMap<QString, double>& outlierObs);

    void startSolvingConflictSets(const QString& modelDescription, const QList<TestItem>& testItemList, int truncateMode);
};


#endif // SYSTEMENTITY_H
