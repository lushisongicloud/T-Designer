#include "systementity.h"
#include "mainwindow.h"

#include <QDateTime>
#include <QDir>
#include <QFile>
#include <QMutex>
#include <QMutexLocker>
#include <QTextStream>
#include <QMessageBox>
#include <QDebug>
#include <QObject>
#include <QRegularExpression>
#include <QSet>
#include <vector>
#include <utility>
#include <stdexcept>
#include <cmath>
#include <z3_api.h>

namespace {

QMutex g_z3LogMutex;
thread_local const QString *g_currentZ3Logic = nullptr;
thread_local bool g_z3ErrorLogged = false;
thread_local QString g_lastZ3ErrorMessage;

QString writeZ3FailureLog(const QString &logic, const QString &errorMessage)
{
    QMutexLocker locker(&g_z3LogMutex);
    QDir baseDir(QDir::current());
    const QString logDir = QString("logs");
    if (!baseDir.exists(logDir)) {
        baseDir.mkpath(logDir);
    }
    baseDir.cd(logDir);

    const QString timestamp = QDateTime::currentDateTimeUtc().toString(QString("yyyyMMdd_HHmmsszzz"));
    const QString fileName = QString("z3_error_%1.txt").arg(timestamp);

    QFile file(baseDir.filePath(fileName));
    if (!file.open(QIODevice::WriteOnly | QIODevice::Text)) {
        qWarning() << "Failed to open Z3 log file.";
        return QString();
    }

    QTextStream stream(&file);
    stream << "Z3 Error: " << errorMessage << "\n";
    stream << "----------- Logic -----------\n";
    stream << logic;
    file.close();
    return file.fileName();
}

void errorHandler(Z3_context ctx, Z3_error_code err)
{
    const char *msg = Z3_get_error_msg(ctx, err);
    const QString message = QString::fromUtf8(msg ? msg : "unknown error");
    if (!g_z3ErrorLogged && g_currentZ3Logic) {
        const QString path = writeZ3FailureLog(*g_currentZ3Logic, message);
        if (!path.isEmpty()) {
            qWarning() << "Z3 error logged to" << QDir::toNativeSeparators(path);
        }
        g_z3ErrorLogged = true;
        g_lastZ3ErrorMessage = message;
    }
}

void skipWhitespace(const QString &text, int &pos)
{
    while (pos < text.size() && text.at(pos).isSpace()) {
        ++pos;
    }
}

QString readSymbolToken(const QString &text, int &pos)
{
    skipWhitespace(text, pos);
    const int start = pos;
    while (pos < text.size()) {
        const QChar ch = text.at(pos);
        if (ch.isSpace() || ch == '(' || ch == ')') {
            break;
        }
        ++pos;
    }
    return text.mid(start, pos - start);
}

QString readBalancedToken(const QString &text, int &pos)
{
    skipWhitespace(text, pos);
    if (pos >= text.size()) {
        return QString();
    }
    if (text.at(pos) != '(') {
        return readSymbolToken(text, pos);
    }
    const int start = pos;
    int depth = 0;
    while (pos < text.size()) {
        const QChar ch = text.at(pos);
        if (ch == '(') {
            ++depth;
        } else if (ch == ')') {
            --depth;
        }
        ++pos;
        if (depth == 0) {
            break;
        }
    }
    return text.mid(start, pos - start);
}

QStringList splitTopLevelTokens(const QString &text)
{
    QStringList tokens;
    QString current;
    int depth = 0;
    for (int i = 0; i < text.size(); ++i) {
        const QChar ch = text.at(i);
        if (ch.isSpace() && depth == 0) {
            if (!current.trimmed().isEmpty()) {
                tokens.append(current.trimmed());
                current.clear();
            }
            continue;
        }
        current.append(ch);
        if (ch == '(') {
            ++depth;
        } else if (ch == ')') {
            --depth;
        }
    }
    if (!current.trimmed().isEmpty()) {
        tokens.append(current.trimmed());
    }
    return tokens;
}

z3::sort parseSortString(z3::context &ctx, const QString &sortText)
{
    const QString trimmed = sortText.trimmed();
    if (trimmed.isEmpty()) {
        throw std::runtime_error("empty sort string");
    }
    if (trimmed.compare(QString("Real"), Qt::CaseInsensitive) == 0) {
        return ctx.real_sort();
    }
    if (trimmed.compare(QString("Int"), Qt::CaseInsensitive) == 0) {
        return ctx.int_sort();
    }
    if (trimmed.compare(QString("Bool"), Qt::CaseInsensitive) == 0) {
        return ctx.bool_sort();
    }
    if (trimmed.startsWith(QString("(Array"), Qt::CaseInsensitive)) {
        QString inner = trimmed.mid(QString("(Array").size());
        if (inner.endsWith(')')) {
            inner.chop(1);
        }
        inner = inner.trimmed();
        const QStringList parts = splitTopLevelTokens(inner);
        if (parts.size() != 2) {
            throw std::runtime_error(QString("unable to parse array sort: %1").arg(trimmed).toStdString());
        }
        z3::sort domain = parseSortString(ctx, parts.at(0));
        z3::sort range = parseSortString(ctx, parts.at(1));
        return ctx.array_sort(domain, range);
    }
    throw std::runtime_error(QString("unsupported sort: %1").arg(trimmed).toStdString());
}

std::vector<std::pair<QString, QString>> collectFunctionDeclarations(const QString &logic)
{
    std::vector<std::pair<QString, QString>> declarations;
    QSet<QString> seen;
    int pos = 0;
    while (pos < logic.size()) {
        skipWhitespace(logic, pos);
        if (pos >= logic.size()) {
            break;
        }
        if (logic.midRef(pos, 12) == QString("(declare-fun")) {
            pos += 12;
            QString name = readSymbolToken(logic, pos);
            QString argsToken = readBalancedToken(logic, pos);
            QString sortToken = readBalancedToken(logic, pos);
            if (!name.isEmpty() && !sortToken.isEmpty() && !seen.contains(name)) {
                declarations.emplace_back(name.trimmed(), sortToken.trimmed());
                seen.insert(name.trimmed());
            }
            skipWhitespace(logic, pos);
            if (pos < logic.size() && logic.at(pos) == ')') {
                ++pos;
            }
            continue;
        }
        ++pos;
    }
    return declarations;
}

QString formatRangeValue(double number)
{
    if (std::fabs(number) < 1e-12) {
        number = 0.0;
    }
    QString text = QString::number(number, 'f', 12);
    if (text.contains(QLatin1Char('.'))) {
        while (text.endsWith(QLatin1Char('0'))) {
            text.chop(1);
        }
        if (text.endsWith(QLatin1Char('.'))) {
            text.chop(1);
        }
    }
    if (text == QLatin1String("-0")) {
        text = QString("0");
    }
    if (text.isEmpty()) {
        text = QString("0");
    }
    return text;
}

QString formatModelExpr(const z3::expr &value)
{
    if (value.is_bool()) {
        switch (value.bool_value()) {
        case Z3_L_TRUE:
            return QString("true");
        case Z3_L_FALSE:
            return QString("false");
        default:
            return QString("unknown");
        }
    }
    if (value.is_int() || value.is_real()) {
        const std::string text = value.to_string();
        bool ok = false;
        double number = QString::fromStdString(text).toDouble(&ok);
        if (ok) {
            return formatRangeValue(number);
        }
        return QString::fromStdString(text);
    }
    if (value.is_app() && value.num_args() == 0) {
        return QString::fromStdString(value.to_string());
    }
    if (value.is_array()) {
        QStringList entries;
        z3::expr asArray = value;
        while (asArray.is_app() && asArray.decl().decl_kind() == Z3_OP_STORE) {
            z3::expr index = asArray.arg(1);
            z3::expr val = asArray.arg(2);
            entries.append(QString("(%1 -> %2)")
                               .arg(QString::fromStdString(index.to_string()),
                                    QString::fromStdString(val.to_string())));
            asArray = asArray.arg(0);
        }
        entries.append(QString("else -> %1").arg(QString::fromStdString(asArray.to_string())));
        return QString("{%1}").arg(entries.join(QString(", ")));
    }
    return QString::fromStdString(value.to_string());
}

} // namespace

QList<QList<ComponentEntity>> candidateConflictList ;
QList<QList<ComponentEntity>> ConflictList;

SystemEntity::SystemEntity(SQliteDatabase *database)
{
    this->database = database;
}

int ProgressNum;
bool z3Solve(const QString &logic, int timeoutMs, QMap<QString, QString> *modelOut);
bool isSuperSet(QList<ComponentEntity>& set,QList<ComponentEntity>& superSet);
QString unchangingCode;
bool ThreadSolveResult[3];
int CurSolveCandidateConflictIdx[3];

GraphAdjList* graph = new GraphAdjList(1);



void SystemEntity::setMainWindow(MainWindow* window)
{
    mainWindow = window;
}

QList<ComponentEntity> SystemEntity::prepareModel(const QString& modelDescription) {
    num = 0;
    //QTime time;
    //time.start();

    QList<QString> qlist = modelDescription.split("END");
    if(qlist.size() != 2) {
        qDebug() << "Error: Invalid model description";
        return componentEntityList;
    }
    QString componentDescription = qlist[0].remove("DEF").remove("BEGIN").remove("END");
    QString linkDescription = qlist[1].remove("DEF").remove("BEGIN").remove("END");
    //qDebug()<<"modelDescription："<<modelDescription;
    componentEntityList = creatComponentEntity(componentDescription);
    //qDebug()<<"ComponentEntity Finished";
    systemLinkCode = creatSystemLinkCode(linkDescription);
    //qDebug()<<"systemLinkCode:"<<systemLinkCode;
    graph->ClearGraph();
    QList<QList<ComponentEntity>> test = AnlysisSystemLink(linkDescription, componentEntityList);

    //qDebug()<<"Link Finished";
    QString VariablesCode = creatVariablesCode(componentEntityList);
    //qDebug()<<"VariablesCode Finished";


    unchangingCode = "";
    unchangingCode.append(VariablesCode);
    unchangingCode.append(systemLinkCode);

    //QString out = "PrepareTime:"+QString::number(time.elapsed()/1000.0);
    //qDebug() << out << endl;
    return componentEntityList;
}

QList<obsEntity> SystemEntity::buildObsEntityList(const QList<TestItem> &testItemList)
{
    return creatObsEntity(testItemList);
}

void SystemEntity::setVariableRangeConfig(const rangeconfig::VariableRangeConfig &config)
{
    variableRangeConfig = config;
}

SystemEntity::IncrementalSolveSession SystemEntity::createIncrementalSolveSession(const QString &modelDescription,
                                                                                  const QList<TestItem> &testItemList,
                                                                                  const QStringList &variableWhitelist,
                                                                                  QString &errorMessage,
                                                                                  int timeoutMs)
{
    IncrementalSolveSession session;
    errorMessage.clear();

    prepareModel(modelDescription);

    QString testCode;
    obsEntityList = creatObsEntity(testItemList);
    for (const auto &obs : obsEntityList) {
        testCode += obs.getDescription();
    }

    const QString rangeCode = buildVariableRangeCode(variableWhitelist, testItemList);
    if (!rangeCode.isEmpty()) {
        testCode += rangeCode;
    }

    QString componentCode;
    for (const ComponentEntity &entity : componentEntityList) {
        componentCode += entity.getDescription();
    }

    session.baseLogic = unchangingCode + componentCode + testCode;

    session.context = std::make_shared<z3::context>();
    if (!session.context) {
        errorMessage = QString("无法创建Z3上下文");
        return session;
    }

    session.solver = std::make_shared<z3::solver>(*session.context);
    if (!session.solver) {
        errorMessage = QString("无法创建Z3求解器");
        session.context.reset();
        return session;
    }

    Z3_set_error_handler(*session.context, errorHandler);

    if (timeoutMs > 0) {
        z3::params params(*session.context);
        params.set("timeout", static_cast<unsigned>(timeoutMs));
        session.solver->set(params);
    }

    g_currentZ3Logic = &session.baseLogic;
    session.declaredFunctions = collectFunctionDeclarations(session.baseLogic);
    g_z3ErrorLogged = false;
    g_lastZ3ErrorMessage.clear();

    try {
        z3::expr_vector baseExprs = session.context->parse_string(session.baseLogic.toStdString().c_str());
        for (unsigned i = 0; i < baseExprs.size(); ++i) {
            session.solver->add(baseExprs[i]);
        }
    } catch (const z3::exception &ex) {
        errorMessage = QString::fromUtf8(ex.msg());
        g_currentZ3Logic = nullptr;
        return session;
    }

    if (g_z3ErrorLogged) {
        errorMessage = g_lastZ3ErrorMessage;
        g_currentZ3Logic = nullptr;
        return session;
    }

    const z3::check_result result = session.solver->check();
    g_currentZ3Logic = nullptr;
    if (result == z3::check_result::sat) {
        session.valid = true;
        return session;
    }

    if (result == z3::check_result::unsat) {
        errorMessage = QString("基础约束不可满足");
    } else {
        errorMessage = QString("Z3 返回 unknown 结果");
    }
    session.context.reset();
    session.solver.reset();
    session.baseLogic.clear();
    session.valid = false;
    return session;
}

bool SystemEntity::checkIncrementalSession(IncrementalSolveSession &session,
                                           const QStringList &extraAssertions,
                                           QString &errorMessage,
                                           int timeoutMs,
                                           QMap<QString, QString> *modelOut) const
{
    errorMessage.clear();
    if (modelOut) {
        modelOut->clear();
    }
    if (!session.valid || !session.context || !session.solver) {
        errorMessage = QString("增量求解会话未初始化");
        return false;
    }

    if (timeoutMs > 0) {
        z3::params params(*session.context);
        params.set("timeout", static_cast<unsigned>(timeoutMs));
        session.solver->set(params);
    }

    session.solver->push();
    bool popped = false;
    auto ensurePop = [&]() {
        if (!popped) {
            session.solver->pop();
            popped = true;
        }
    };

    QString incrementalLogic;
    if (!extraAssertions.isEmpty()) {
        incrementalLogic = extraAssertions.join(QString("\n"));
        try {
            z3::sort_vector sortVector(*session.context);
            z3::func_decl_vector declVector(*session.context);
            for (const auto &decl : session.declaredFunctions) {
                z3::sort range = parseSortString(*session.context, decl.second);
                z3::func_decl func = session.context->function(decl.first.toStdString().c_str(), 0, nullptr, range);
                declVector.push_back(func);
            }
            z3::expr_vector parsed = session.context->parse_string(incrementalLogic.toStdString().c_str(),
                                                                   sortVector,
                                                                   declVector);
            for (unsigned i = 0; i < parsed.size(); ++i) {
                session.solver->add(parsed[i]);
            }
        } catch (const std::exception &ex) {
            errorMessage = QString::fromUtf8(ex.what());
            ensurePop();
            return false;
        }
    }

    QString combinedLogic;
    if (!incrementalLogic.isEmpty()) {
        combinedLogic = session.baseLogic + incrementalLogic;
    } else {
        combinedLogic = session.baseLogic;
    }

    g_currentZ3Logic = &combinedLogic;
    g_z3ErrorLogged = false;
    g_lastZ3ErrorMessage.clear();

    z3::check_result result;
    try {
        result = session.solver->check();
    } catch (const z3::exception &ex) {
        errorMessage = QString::fromUtf8(ex.msg());
        ensurePop();
        g_currentZ3Logic = nullptr;
        return false;
    }

    g_currentZ3Logic = nullptr;

    if (g_z3ErrorLogged) {
        errorMessage = g_lastZ3ErrorMessage;
        ensurePop();
        return false;
    }

    bool sat = false;
    if (result == z3::check_result::sat) {
        sat = true;
        if (modelOut) {
            modelOut->clear();
            z3::model model = session.solver->get_model();
            const unsigned count = model.size();
            for (unsigned i = 0; i < count; ++i) {
                z3::func_decl decl = model.get_const_decl(i);
                const QString name = QString::fromStdString(decl.name().str());
                z3::expr value = model.get_const_interp(decl);
                modelOut->insert(name, formatModelExpr(value));
            }
        }
    } else if (result == z3::check_result::unsat) {
        sat = false;
        if (modelOut) {
            modelOut->clear();
        }
    } else {
        errorMessage = QString("Z3 返回 unknown 结果");
        sat = false;
    }

    ensurePop();
    return sat;
}

QString SystemEntity::buildVariableRangeCode(const QStringList &variables, const QList<TestItem> &testItemList) const
{
    Q_UNUSED(variables);
    Q_UNUSED(testItemList);
    return QString();
}

QMap<QString, double> SystemEntity::solveOutlierObs(QList<obsEntity>& obsEntityList,QList<resultEntity>& resultEntityList) const {

    //    异常观测的判断准则
    //    1）罕见故障需要置信度高的观测来支持。当前诊断候选解中已知故障的综合概率越低，则需要的置信度阈值应越高。
    //    计算方法：遍历resultEntityList中已知故障模式的单故障,计算其综合故障概率pf=1-(1-p1)*(1-p2)*...(1-pn)，其中pn为第个resultEntityList中已知故障模式的单故障的概率。如果观测的失效概率p2高于pf的1/10，则将其加入outlierObs中。此种情况下观测出现观测错误的综合概率p=p2*(1-pf)。
    //    2）如果去掉一个观测，可得到一个概率较高的已知故障的诊断解，则此观测需要进行确认。
    //    计算方法：根据概率由高到低的顺序遍历resultEntityList中的有且仅有1个观测故障b的双故障结果，如果除观测以外的器件故障c为已知故障，且故障概率高于resultEntityList中最可能诊断解概率的1/2，则将这个观测故障加入outlierObs中。观测出现观测错误的综合概率p的计算方法：找到所有包含器件b的singleObsResultEntity，假设有n个，则概率p=1-（1-c1.probability）*（1-c2.probability)*……*(1-cn.probability)，其中cn.probability为第n个singleObsResultEntity中器件c的故障模式概率

    // 遍历计算所有已知故障模式的单故障的综合概率
    double pf = 1.0;
    if (resultEntityList.begin()->getComponentCount() != 1 || resultEntityList.begin()->getFailureModes().contains("未知故障")) {
        pf = resultEntityList.begin()->getProbability();
    } else {
        for (const resultEntity &re : resultEntityList) {
            if (re.getComponentCount() == 1 && !re.getFailureModes().contains("未知故障")) {
                pf *= (1 - re.getProbability());
                //qDebug()<<"re.getComponentNames():"<<re.getComponentNames()<<" re.getFailureModes():"<<re.getFailureModes();
            }
        }
        pf = 1 - pf;
    }

    // 然后遍历找出满足条件的观测器件，并将它们加入到 outlierObs 中
    QMap<QString, double> outlierObs;

    // 然后遍历找出有且仅有一个观测器件的 resultEntity
    QList<resultEntity> singleObsResultEntityList;
    for (const resultEntity &re : resultEntityList) {
        if (re.getComponentCount("obs") == 1) {
            singleObsResultEntityList.append(re);
        }
    }
    for (const resultEntity &re : singleObsResultEntityList) {
        QString obsComponent = re.getComponentNames("obs");
        QString otherComponent = re.getComponentNames("!obs");

        // 如果outlierObs中已包含obsComponent，则跳过本次循环
        if (outlierObs.contains(obsComponent)) continue;

        // 检查规则2的条件
        double otherProbability = re.getFailureProbability(otherComponent);
        //人为设定了一个参数1/2，即当前最高概率解的概率的1/2
        resultEntity firstResult= resultEntityList.first();
        if (re.getFailureMode(otherComponent) != "未知故障" && (otherProbability >= firstResult.getProbability() / 2 ||(firstResult.getComponentCount() > 1 || firstResult.getFailureModes().contains("未知故障")))) {
            // 计算概率 p
            double p = 1.0;
            //qDebug() << "init obs" << obsComponent << "failPro:" << re.getFailureProbability(obsComponent);
            for (const resultEntity &re2 : singleObsResultEntityList) {
                QString otherCname = re2.getComponentNames("!obs");
                if (re2.containsComponent(obsComponent)) {
                    p *= (1 - re2.getFailureProbability(otherCname));
                }
            }
            //qDebug() << "after otherCname p:" << 1 - p;
            p = re.getFailureProbability(obsComponent) * (1 - p);

            // 将观测器件名称和概率加入到 outlierObs
            outlierObs.insert(obsComponent + ",观测阻滞", p);
        }
    }

    // 检查规则1的条件
    //此时的obs应直接从obsEntityList中找
    for (const obsEntity &obs : obsEntityList) {
        //qDebug()<<"obs.getName():"<<obs.getName()<<"obs.getConfidence():"<<obs.getConfidence()<<"obs.getFailureProbability():"<<obs.getFailureProbability();
        double obsFailureP = obs.getFailureProbability();
        if(obsFailureP > pf / 10 && obs.getConfidence()<0.95){
            outlierObs.insert(obs.getName() + ",观测可疑", obsFailureP *(1-pf));
        }
    }
    return outlierObs;
}

void SystemEntity::solveConflictSets(const QString& modelDescription, const QList<TestItem>& testItemList)
{
    QStringList ans;
    QString testCode;
    firstFailurePairProbability= 0.0;
    resultEntityList.clear();
    prepareModel(modelDescription);

    obsEntityList = creatObsEntity(testItemList);
    for (const auto &obsEntity : obsEntityList) {
        testCode += obsEntity.getDescription();
    }

    allComponentCode = "";
    for(int i=0; i<componentEntityList.count(); i++) {
        allComponentCode += componentEntityList.at(i).getDescription();
    }
    //qDebug()<<testCode;
    if(z3Solve(unchangingCode + allComponentCode + testCode) == true) {
        qDebug()<<"无故障，求解结束";
        ProgressNum = 100;
        emit(ProgressEnd(ans));
        return;
    }
    else {
        ans.append("存在冲突");
    }
    //对待求解清单按概率排序
    QList<FailureEntity> failureEntities;
    for(int i=0; i<componentEntityList.count(); i++) {
        failureEntities.append(FailureEntity(componentEntityList[i].getFailureProbability(), i, false));
    }
    std::sort(failureEntities.begin(), failureEntities.end());

    //求解单故障
    QList<FailureEntity>::iterator it = failureEntities.begin();
    while(it != failureEntities.end()) {
        if(singleFailureSolve(*it, testCode, ans, resultEntityList)) {
            it = failureEntities.erase(it);
        } else {
            ++it;
        }
    }
    //判断是否有单故障解，有则结束求解
    qDebug()<<"单故障求解结束,诊断解数量："<<ans.count()-1;
    //if(ans.count()>1){ ProgressNum = 100;emit(ProgressEnd(ans)); return;}

    //将观测器件增加到求解列表中 //从全部的观测中仅去掉当前待增加的观测，如果有解，则丢弃
    for(int i=0; i<obsEntityList.count(); i++) {
        QString adjustedTestCode = testCode;
        adjustedTestCode.remove(obsEntityList[i].getDescription());
        if(!z3Solve(unchangingCode + allComponentCode + adjustedTestCode)){
            failureEntities.append(FailureEntity(obsEntityList[i].getFailureProbability(), i, true));
        }
    }
    std::sort(failureEntities.begin(), failureEntities.end());

    // Create a max heap for failure pairs
    auto cmp = [](FailurePair left, FailurePair right) { return left < right; };
    std::priority_queue<FailurePair, std::vector<FailurePair>, decltype(cmp)> failurePairs(cmp);
    // Populate the heap
    for(int i=0; i<failureEntities.count(); i++) {
        for(int j=i+1; j<failureEntities.count(); j++) {
            failurePairs.push(FailurePair(failureEntities[i], failureEntities[j]));
        }
    }
    qDebug()<<"开始求解多故障";
    //双故障求解
    while(!failurePairs.empty()) {
        FailurePair pair = failurePairs.top();
        failurePairs.pop();
        // Check if the current pair's probability is below the threshold
        if(ans.count() <= 30 &&pair.probability < firstFailurePairProbability / 100) {
            qDebug()<<"截断概率："<<firstFailurePairProbability/100<<"当前概率："<<pair.probability;
            if(ans.count() >= 2) break;
        }
        else if(ans.count() > 30 && pair.probability < firstFailurePairProbability / 2) {
            qDebug()<<"截断概率："<<firstFailurePairProbability/2<<"当前概率："<<pair.probability;
            break;
        }
        if(pair.entity1.isObservation && !pair.entity2.isObservation)doubleFailureSolve(pair.entity2,pair.entity1, testCode, ans, resultEntityList);
        else doubleFailureSolve(pair.entity1,pair.entity2, testCode, ans, resultEntityList);
    }
    if(ans.count()>1)
    {
        qDebug()<<"双故障求解结束,诊断解数量："<<ans.count()-1;
        //判断是否存在异常观测，将resultEntityList中的resultEntity按概率由大到小的顺序排序
        //然后按概率由大到小的顺序进行遍历，找到第一个包含观测错误的多故障resultEntity，且除此以外的故障是除未知故障和观测错误的已知失效模式
        std::sort(resultEntityList.begin(), resultEntityList.end(),
                  [](const resultEntity &a, const resultEntity &b) {
            return a.getProbability() > b.getProbability();
        });

        QList<resultEntity> normalizedResultEntityList = resultEntityList;
        // 计算所有项的概率之和
        double sumProbability = 0.0;
        for (const auto& entity : normalizedResultEntityList) {
            sumProbability += entity.getProbability();
        }

        // 若概率之和不为0，则进行归一化
        if (std::abs(sumProbability) > 1e-6) {
            for (auto& entity : normalizedResultEntityList) {
                double normalizedProbability = entity.getProbability() / sumProbability;
                entity.setProbability(normalizedProbability);
                for (const auto& componentName : entity.getComponentNames().split(",")) {
                    double normalizedComponentProbability = entity.getFailureProbability(componentName) / sumProbability;
                    entity.setFailureProbability(componentName, normalizedComponentProbability);
                }
            }
        }
        emit updateOutlierObsTable(solveOutlierObs(obsEntityList, normalizedResultEntityList));
        ProgressNum = 100;
        emit(ProgressEnd(ans));
        return;
    }

    qDebug()<<"求解结束,未找到诊断解";
    ProgressNum = 100;
    emit(ProgressEnd(ans));
}
/**
 * @brief 求解当前系统描述+观测是否有解
 * @param modelDescription 模型的描述
 * @param testItemList 测试项列表，用于生成测试代码
 * @return
 *      - true：在当前约束条件下有解
 *      - false：在当前约束条件下无解
 */
bool SystemEntity::satisfiabilitySolve(const QString& modelDescription, const QList<TestItem>& testItemList)
{
    QStringList ans;
    QString testCode;
    firstFailurePairProbability= 0.0;
    resultEntityList.clear();
    prepareModel(modelDescription);

    obsEntityList = creatObsEntity(testItemList);
    for (const auto &obsEntity : obsEntityList) {
        testCode += obsEntity.getDescription();
    }
    allComponentCode = "";
    for(int i=0; i<componentEntityList.count(); i++) {
        allComponentCode += componentEntityList.at(i).getDescription();
    }
    //qDebug()<<testCode;
    if(z3Solve(unchangingCode + allComponentCode + testCode) == true) {
        qDebug()<<"无故障，求解结束";
        return true;
    }
    else {
        ans.append("存在冲突");
        return false;
    }
}
//包含关系：currentResultEntityList中的项，器件名相同的情况下，故障模式为"未知故障"的包含其他的已知故障模式。项目中如果是多故障的情况，项中至少存在一个器件与故障模式包含另一项中每一器件与故障模式，且剩余项的器件名称与故障模式均相同，则整个多故障项也包含另一故障项，注意：多故障项中器件名称与故障模式是按顺序一一对应的（即排第2的故障模式对应排第2的器件名称）
//举例：(格式为"器件名;故障模式")，实际格式并非这样，而是器件名存储于componentNameList，故障模式存储于failureModeList
//"KM;未知故障"包含"KM;线圈断路"
//"KM;接触不良"不包含"KM;线圈断路"
//"KM;线圈断路"不包含"KM;未知故障"
//"KM,L1;未知故障,未知故障"包含"KM,L1;线圈断路,导线松动"
//"KM,L1;未知故障,导线松动"包含"KM,L1;线圈断路,导线松动"
//"KM,L1;未知故障,未知故障"包含"KM,L1;线圈断路,未知故障"
//"KM,L1;未知故障,导线松动"包含"L1,KM;导线松动,线圈断路"
//"KM,L1;未知故障,导线松动"不包含"KM,L1;线圈断路,未知故障"
//"KM,L1;未知故障,导线松动"不包含"L1,KM;导线断开,导线松动"
//如果一项故障项包含另一故障项，则称被包含的项范围小，包含项范围大
//将计算分为两个阶段，先将待计算的项分为两部分：范围大的项、其他项；第一阶段计算范围大的项，然后根据计算结果对其他项进行排除（范围大的项如果被排除了，则对应的范围小的项可直接标记为应排除项），第二阶段计算经排除后的其他项。
//具体实现方法：
//遍历currentResultEntityList所有项：先记录含"未知故障"的项的序号，并只计算这些项,第一阶段计算完成后，记录计算的结果（待排除的含"未知故障"项的序号），开始进入第二阶段计算
//遍历currentResultEntityList中的剩余项（未含"未知故障"的项）,如果项被某个第一阶段计算结果中的项包含，则直接标记为需要排除，否则加入线程池，调用z3进行计算
//void SystemEntity::incrementalSolve(const QString& modelDescription, const QList<TestItem>& testItemList, QList<resultEntity>& currentResultEntityList,QList<resultEntity>& excludedResults)
//{
//    QStringList ans;
//    QString testCode;
//    prepareModel(modelDescription);
//    obsEntityList = creatObsEntity(testItemList);
//    for (const auto &obsEntity : obsEntityList) {
//        testCode += obsEntity.getDescription();
//    }

//    allComponentCode = "";
//    // 创建一个哈希表用于存储组件名与其对应的描述
//    QHash<QString, QString> componentDescriptions;
//    // 创建一个二维哈希表来存储组件名和故障模式的描述
//    QHash<QString, QHash<QString, QString>> failureDescriptions;
//    for (int i = 0; i < componentEntityList.count(); i++) {
//        allComponentCode += componentEntityList.at(i).getDescription();
//        componentDescriptions.insert(componentEntityList.at(i).getName(), componentEntityList.at(i).getDescription());
//        QList<FailureMode> failureModes = componentEntityList.at(i).getFailMode();
//        for (const auto &failureMode : failureModes) {
//            failureDescriptions[componentEntityList.at(i).getName()][failureMode.getName()] = failureMode.getDescribe();
//        }
//    }

//    // 1. 初始化一个指针或索引，用于遍历currentResultEntityList。
//    auto iter = currentResultEntityList.begin();

//    // 2. 当指针未到达currentResultEntityList的末尾时：
//    while (iter != currentResultEntityList.end()) {
//        QString code = allComponentCode;
//        QStringList failureModeList = iter->getFailureModes().split(",");
//        QStringList componentNameList = iter->getComponentNames().split(",");
//        int itemCount = componentNameList.count();
//        QString nameString;
//        for (int i = 0; i < itemCount; ++i) {
//            QString componentName = componentNameList.at(i);
//            QString failureMode = failureModeList.at(i);
//            // 从code中移除每项ComponentName对应的器件描述
//            if(componentName=="FU"){
//                qDebug()<<"code before:"<<code;
//                qDebug()<<"componentDescriptions[componentName]"<<componentDescriptions[componentName];
//                qDebug()<<"failureMode:"<<failureMode;
//            }
//            code.remove(componentDescriptions[componentName]);

//            //如果当前ComponentName项对应的FailureMode不是"未知故障"，则在code中增加ComponentName对应器件的故障模式描述
//            if (failureMode != "未知故障") {
//                code += failureDescriptions[componentName][failureMode];
//                if(componentName=="FU"){
//                    qDebug()<<"code after:"<<code;
//                    nameString = "FU";
//                }
//            }
//        }
//        code =  unchangingCode + code + testCode;

//        if(nameString == "FU")
//        {
//            qDebug()<<"Solving Code:"<<code;
//            qDebug()<<"z3Solve(code):"<<z3Solve(code);
//        }
//        // 如果不相符合，则从currentResultEntityList中移除当前结果。
//        if (!z3Solve(code)) {
//            excludedResults.append(*iter); // 将被排除的结果添加到专门的列表中
//            iter = currentResultEntityList.erase(iter);
//        }
//        // c. 如果相符合，则移动到下一个结果。
//        else {
//            ++iter;
//        }
//    }
//}
//void SystemEntity::incrementalSolve(const QString& modelDescription, const QList<TestItem>& testItemList, QList<resultEntity>& currentResultEntityList, QList<resultEntity>& excludedResults)
//{
//    prepareModel(modelDescription);
//    obsEntityList = creatObsEntity(testItemList);

//    QString testCode;
//    for (const auto &obsEntity : obsEntityList) {
//        testCode += obsEntity.getDescription();
//    }

//    // 创建一个哈希表用于存储组件名与其对应的描述,创建一个二维哈希表来存储组件名和故障模式的描述
//    QString allComponentCode = "";
//    QHash<QString, QString> componentDescriptions;
//    QHash<QString, QHash<QString, QString>> failureDescriptions;
//    for (int i = 0; i < componentEntityList.count(); i++) {
//        allComponentCode += componentEntityList.at(i).getDescription();
//        componentDescriptions.insert(componentEntityList.at(i).getName(), componentEntityList.at(i).getDescription());
//        QList<FailureMode> failureModes = componentEntityList.at(i).getFailMode();
//        for (const auto &failureMode : failureModes) {
//            failureDescriptions[componentEntityList.at(i).getName()][failureMode.getName()] = failureMode.getDescribe();
//        }
//    }

//    QVector<int> excludedIndexes;
//    QMutex mutex;

//    // 采用线程池来分发任务
//    QThreadPool pool;
//    //qDebug()<<"QThread::idealThreadCount():"<<QThread::idealThreadCount();
//    pool.setMaxThreadCount(QThread::idealThreadCount()); // 设置最大线程数

//    int index = 0;
//    for (const auto &resultEntity : currentResultEntityList) {

//        QString code = allComponentCode;
//        QStringList failureModeList = resultEntity.getFailureModes().split(",");
//        QStringList componentNameList = resultEntity.getComponentNames().split(",");
//        int itemCount = componentNameList.count();
//        for (int i = 0; i < itemCount; ++i) {
//            QString componentName = componentNameList.at(i);
//            QString failureMode = failureModeList.at(i);
//            code.remove(componentDescriptions[componentName]);// 从code中移除每项ComponentName对应的器件描述
//            if (failureMode != "未知故障") // 如果当前ComponentName项对应的FailureMode不是"未知故障"，则在code中增加ComponentName对应器件的故障模式描述
//            {
//                code += failureDescriptions[componentName][failureMode];
//            }
//        }
//        code = unchangingCode + code + testCode;

//        //多线程求解
//        SolverRunnable *solverRunnable = new SolverRunnable(code, index, excludedIndexes, mutex);
//        pool.start(solverRunnable); // 提交任务到线程池
//        index++;
//    }

//    pool.waitForDone(); // 等待所有任务完成

//    // 对excludedIndexes进行降序排序，确保从后向前删除，以免影响前面的索引位置
//    std::sort(excludedIndexes.begin(), excludedIndexes.end(), std::greater<int>());

//    // 排除不合适的结果
//    for (int i = 0; i < excludedIndexes.size(); ++i) {
//        int idx = excludedIndexes[i];
//        excludedResults.append(currentResultEntityList[idx]);
//        currentResultEntityList.removeAt(idx);
//    }
//}

//多线程优化版本
void SystemEntity::incrementalSolve(const QString& modelDescription, const QList<TestItem>& testItemList, QList<resultEntity>& currentResultEntityList, QList<resultEntity>& excludedResults)
{
    prepareModel(modelDescription);
    obsEntityList = creatObsEntity(testItemList);

    QString testCode;
    for (const auto &obsEntity : obsEntityList) {
        testCode += obsEntity.getDescription();
    }

    // 创建一个哈希表用于存储组件名与其对应的描述,创建一个二维哈希表来存储组件名和故障模式的描述
    QString allComponentCode = "";
    QHash<QString, QString> componentDescriptions;
    QHash<QString, QHash<QString, QString>> failureDescriptions;
    for (int i = 0; i < componentEntityList.count(); i++) {
        allComponentCode += componentEntityList.at(i).getDescription();
        componentDescriptions.insert(componentEntityList.at(i).getName(), componentEntityList.at(i).getDescription());
        QList<FailureMode> failureModes = componentEntityList.at(i).getFailMode();
        for (const auto &failureMode : failureModes) {
            failureDescriptions[componentEntityList.at(i).getName()][failureMode.getName()] = failureMode.getDescribe();
        }
    }

    QVector<int> excludedIndexes;
    QMutex mutex;

    // 采用线程池来分发任务
    QThreadPool pool;
    //qDebug()<<"QThread::idealThreadCount():"<<QThread::idealThreadCount();
    pool.setMaxThreadCount(QThread::idealThreadCount()); // 设置最大线程数

    QVector<int> firstStageProcessedIndexes;
    QVector<int> firstStageExcludedIndexes;
    for (int index = 0; index < currentResultEntityList.count(); ++index) {
        const auto &resultEntity = currentResultEntityList[index];
        QString code = allComponentCode;
        QStringList failureModeList = resultEntity.getFailureModes().split(",");
        if (failureModeList.contains("未知故障"))
        {
            firstStageProcessedIndexes.append(index);
            QStringList componentNameList = resultEntity.getComponentNames().split(",");
            int itemCount = componentNameList.count();
            for (int i = 0; i < itemCount; ++i) {
                QString componentName = componentNameList.at(i);
                QString failureMode = failureModeList.at(i);
                code.remove(componentDescriptions[componentName]);// 从code中移除每项ComponentName对应的器件描述
                if (failureMode != "未知故障") // 如果当前ComponentName项对应的FailureMode不是"未知故障"，则在code中增加ComponentName对应器件的故障模式描述
                {
                    code += failureDescriptions[componentName][failureMode];
                }
            }
            code = unchangingCode + code + testCode;

            //多线程求解
            SolverRunnable *solverRunnable = new SolverRunnable(code, index, excludedIndexes, mutex);
            pool.start(solverRunnable); // 提交任务到线程池
        }
    }
    pool.waitForDone(); // 等待所有任务完成
    //qDebug()<<"excludedIndexes"<<excludedIndexes;
    firstStageExcludedIndexes = excludedIndexes;
    for (int index = 0; index < currentResultEntityList.count(); ++index) {
        if (firstStageProcessedIndexes.contains(index)) continue;

        const auto &resultEntity = currentResultEntityList[index];
        QStringList failureModeList = resultEntity.getFailureModes().split(",");
        QStringList componentNameList = resultEntity.getComponentNames().split(",");
        QSet<QString> componentNameSet = QSet<QString>::fromList(componentNameList);

        bool isExcluded = false;
        for (int largeIndex : firstStageExcludedIndexes) {
            bool hasLargerScope = true; // 初始化为 true
            const auto &largeResultEntity = currentResultEntityList[largeIndex];
            QStringList largeFailureModeList = largeResultEntity.getFailureModes().split(",");
            QStringList largeComponentNameList = largeResultEntity.getComponentNames().split(",");
            QSet<QString> largeComponentNameSet = QSet<QString>::fromList(largeComponentNameList);

            if (componentNameSet == largeComponentNameSet) {
                for (const QString &componentName : componentNameSet) {
                    QString failureMode = failureModeList.at(componentNameList.indexOf(componentName));
                    QString largeFailureMode = largeFailureModeList.at(largeComponentNameList.indexOf(componentName));

                    if (largeFailureMode != "未知故障" && failureMode != largeFailureMode) {
                        hasLargerScope = false;
                        break; // 发现一项不满足条件，停止对当前largeIndex的计算
                    }
                }
            } else {
                hasLargerScope = false; // 如果组件名称集不匹配，则设置为 false
            }

            if (hasLargerScope) {
                isExcluded = true;
                break; // 找到一项可以包含待计算的当前项，则结束firstStageExcludedIndexes的遍历
            }
        }

        if (isExcluded) {
            excludedIndexes.append(index);
        } else {
            QString code = allComponentCode;
            int itemCount = componentNameList.count();
            for (int i = 0; i < itemCount; ++i) {
                QString componentName = componentNameList.at(i);
                QString failureMode = failureModeList.at(i);
                code.remove(componentDescriptions[componentName]);// 从code中移除每项ComponentName对应的器件描述
                if (failureMode != "未知故障") // 如果当前ComponentName项对应的FailureMode不是"未知故障"，则在code中增加ComponentName对应器件的故障模式描述
                {
                    code += failureDescriptions[componentName][failureMode];
                }
            }
            code = unchangingCode + code + testCode;
            // 加入线程池，调用z3进行计算
            SolverRunnable *solverRunnable = new SolverRunnable(code, index, excludedIndexes, mutex);
            pool.start(solverRunnable); // 提交任务到线程池
        }
    }
    pool.waitForDone(); // 等待所有任务完成

    // 对excludedIndexes进行降序排序，确保从后向前删除，以免影响前面的索引位置
    std::sort(excludedIndexes.begin(), excludedIndexes.end(), std::greater<int>());

    // 排除不合适的结果
    for (int i = 0; i < excludedIndexes.size(); ++i) {
        int idx = excludedIndexes[i];
        excludedResults.append(currentResultEntityList[idx]);
        currentResultEntityList.removeAt(idx);
    }
}
/**
 * @brief 完整的求解方法，用于进行单故障和双故障的求解
 * @param modelDescription 模型的描述，用于准备模型
 * @param testItemList 测试项列表，用于生成测试代码
 * @param truncateMode 求解截断模式：
 *      - 0：如果存在单故障解，则终止求解
 *      - 1：多故障求解阶段，根据概率对求解过程进行截断
 *      - 2：完成全部求解，不进行截断
 */
QList<resultEntity> SystemEntity::completeSolve(const QString& modelDescription, const QList<TestItem>& testItemList, int truncateMode, bool includeObs)
{
    int progress = 0;
    emit solvingStarted();

    QStringList ans;
    QString testCode;
    firstFailurePairProbability= 0.0;
    resultEntityList.clear();
    prepareModel(modelDescription);

    obsEntityList = creatObsEntity(testItemList);
    for (const auto &obsEntity : obsEntityList) {
        testCode += obsEntity.getDescription();
    }

    allComponentCode = "";
    for(int i=0; i<componentEntityList.count(); i++) {
        allComponentCode += componentEntityList.at(i).getDescription();
    }
    //qDebug()<<testCode;
    if(z3Solve(unchangingCode + allComponentCode + testCode) == true) {
        qDebug()<<"无故障，求解结束";
        emit progressUpdated(100);
        emit solvingFinished(ans);
        return resultEntityList;
    }
    else {
        ans.append("存在冲突");
    }
    //对待求解清单按概率排序
    QList<FailureEntity> failureEntities;
    for(int i=0; i<componentEntityList.count(); i++) {
        failureEntities.append(FailureEntity(componentEntityList[i].getFailureProbability(), i, false));
    }
//    for(int i=0; i<obsEntityList.count(); i++) {
//        if(!obsEntityList[i].obsType.isEmpty()){
//            failureEntities.append(FailureEntity(obsEntityList[i].getFailureProbability(), i, true));
//        }
//    }
    std::sort(failureEntities.begin(), failureEntities.end());
    emit progressUpdated(++progress);

    //求解单故障
    int totalIterations = failureEntities.size();
    int currentIteration = 0;
    QList<FailureEntity>::iterator it = failureEntities.begin();
    while(it != failureEntities.end()) {
        ++currentIteration;
        if(singleFailureSolve(*it, testCode, ans, resultEntityList)) //如果当前故障模式（且是已知故障模式）是一个可行解
        {
            it = failureEntities.erase(it);//则将其从待计算的故障模式中删除，此操作后failureEntities仅剩下不能单独成解的已知故障模式
        } else {
            ++it;
        }
        int currentProgress = 1 + ((currentIteration * 29) / totalIterations);
        if(progress != currentProgress)
        {
            progress = currentProgress;
            emit progressUpdated(progress);
        }
    }
    qDebug()<<"单故障求解结束,诊断解数量："<<ans.count()-1;
    emit resultEntityListUpdated(resultEntityList);
    //判断是否有单故障解，有则结束求解
    if(truncateMode == 0){
        if(ans.count()>1){ ProgressNum = 100;emit(ProgressEnd(ans)); emit progressUpdated(100); emit solvingFinished(ans); return resultEntityList;}
    }
    if(includeObs)
    {
        //将观测器件增加到求解列表中 //从全部的观测中仅去掉当前待增加的观测，如果有解，则丢弃
        for(int i=0; i<obsEntityList.count(); i++) {
            QString adjustedTestCode = testCode;
            adjustedTestCode.remove(obsEntityList[i].getDescription());
            if(!z3Solve(unchangingCode + allComponentCode + adjustedTestCode)){
                failureEntities.append(FailureEntity(obsEntityList[i].getFailureProbability(), i, true));
            }
        }
    }
    std::sort(failureEntities.begin(), failureEntities.end());

    // Create a max heap for failure pairs
    auto cmp = [](FailurePair left, FailurePair right) { return left < right; };
    std::priority_queue<FailurePair, std::vector<FailurePair>, decltype(cmp)> failurePairs(cmp);
    // Populate the heap
    for(int i=0; i<failureEntities.count(); i++) {
        for(int j=i+1; j<failureEntities.count(); j++) {
            //排除两个故障均为观测错误的情况
            if (!(failureEntities[i].isObservation && failureEntities[j].isObservation)) {
                failurePairs.push(FailurePair(failureEntities[i], failureEntities[j]));
            }
        }
    }

    qDebug()<<"开始求解多故障";
    //双故障求解
    int totalDoubleIterations = static_cast<int>(failurePairs.size());
    int currentDoubleIteration = 0;

    while(!failurePairs.empty()) {
        ++currentDoubleIteration;
        FailurePair pair = failurePairs.top();
        failurePairs.pop();

        //根据概率进行求解截断
        if(truncateMode==1){
            if(ans.count() <= 30 &&pair.probability < firstFailurePairProbability / 100) {
                qDebug()<<"截断概率："<<firstFailurePairProbability/100<<"当前概率："<<pair.probability;
                if(ans.count() >= 2) break;
            }
            else if(ans.count() > 30 && pair.probability < firstFailurePairProbability / 2) {
                qDebug()<<"截断概率："<<firstFailurePairProbability/2<<"当前概率："<<pair.probability;
                break;
            }
        }
        if(pair.entity1.isObservation && !pair.entity2.isObservation)doubleFailureSolve(pair.entity2,pair.entity1, testCode, ans, resultEntityList);
        else doubleFailureSolve(pair.entity1,pair.entity2, testCode, ans, resultEntityList);

        int currentDoubleProgress = 30 + ((currentDoubleIteration * 70) / totalDoubleIterations);
        if (progress != currentDoubleProgress) {
            progress = currentDoubleProgress;
            emit progressUpdated(progress);
        }
    }

    if(ans.count()>1)
    {
        qDebug()<<"双故障求解结束,诊断解数量："<<ans.count()-1;

        //在排序前输出求解结果
        emit resultEntityListUpdated(resultEntityList);

        //判断是否存在异常观测，将resultEntityList中的resultEntity按概率由大到小的顺序排序
        //然后按概率由大到小的顺序进行遍历，找到第一个包含观测错误的多故障resultEntity，且除此以外的故障是除未知故障和观测错误的已知失效模式
        std::sort(resultEntityList.begin(), resultEntityList.end(),
                  [](const resultEntity &a, const resultEntity &b) {
            return a.getProbability() > b.getProbability();
        });

        QList<resultEntity> normalizedResultEntityList = resultEntityList;
        // 计算所有项的概率之和
        double sumProbability = 0.0;
        for (const auto& entity : normalizedResultEntityList) {
            sumProbability += entity.getProbability();
        }
        qDebug() << "sumProbability:" << sumProbability;

        // 若概率之和不为0，则进行归一化
        if (std::abs(sumProbability) > 1e-10) {
            for (auto& entity : normalizedResultEntityList) {
                // 计算归一化的总体概率
                double normalizedProbability = entity.getProbability() / sumProbability;
                qDebug() << "entity.getProbability():" << entity.getProbability();
                qDebug() << "normalizedProbability:" << normalizedProbability;
                entity.setProbability(normalizedProbability);

                // 优化：预先计算组件名称列表和数量
                QStringList componentNames = entity.getComponentNames().split(",");
                int componentCount = componentNames.count();
                double precomputedValue = std::pow(sumProbability, 1.0 / componentCount);

                // 更新每个组件的归一化概率
                for (const auto& componentName : componentNames) {
                    double normalizedComponentProbability = entity.getFailureProbability(componentName) / precomputedValue;
                    qDebug() << componentName << ":" << entity.getFailureProbability(componentName);
                    qDebug() << "normalizedComponentProbability:" << normalizedComponentProbability;
                    entity.setFailureProbability(componentName, normalizedComponentProbability);
                }
            }
        }
        emit outlierObsUpdated(solveOutlierObs(obsEntityList, normalizedResultEntityList));
        emit progressUpdated(100);
        emit solvingFinished(ans);
        return resultEntityList;
    }
    qDebug()<<"求解结束,未找到诊断解";
    emit progressUpdated(100);
    emit solvingFinished(ans);
    return resultEntityList;
}
//如果当前故障模式是可行解，则返回true
bool SystemEntity::singleFailureSolve(const FailureEntity& entity, const QString& testCode, QStringList& ans, QList<resultEntity>& resultEntityList) {

    QString code = allComponentCode;

    code.remove(componentEntityList.at(entity.index).getDescription());
    code =  unchangingCode + code + testCode;
    QString FailureComponentName = componentEntityList.at(entity.index).getName();
    QList<FailureMode> ListFailureMode = componentEntityList.at(entity.index).getFailMode();
    if(z3Solve(code) == true)
    {
        QString failureName = "未知故障";
        ans.append(FailureComponentName);
        resultEntity singleUnknowResult;
        singleUnknowResult.setResult(FailureComponentName, failureName,ListFailureMode[0].getProbability());
        resultEntityList.append(singleUnknowResult);
        //emit updateResultTable(FailureComponentName, failureName, ListFailureMode[0].getProbability());
        int ansCount =0;
        for(int j=1; j<ListFailureMode.count(); j++) {
            QString codeWithFailure = code;
            codeWithFailure.append(ListFailureMode[j].getDescribe());
            if(z3Solve(codeWithFailure) == true) {
                failureName=ListFailureMode[j].getName();
                resultEntity singleknowResult;
                singleknowResult.setResult(FailureComponentName, failureName,ListFailureMode[j].getProbability());
                resultEntityList.append(singleknowResult);
                //emit updateResultTable(FailureComponentName, failureName, ListFailureMode[j].getProbability());
                ansCount++;
            }
        }
        //if(ansCount)return true;
        return true; //只要有解，不管是已知故障模式还是未知故障模式，均返回true
    }
    return false; //无解
}

bool SystemEntity::doubleFailureSolve(const FailureEntity& entity1, const FailureEntity& entity2, const QString& testCode, QStringList& ans, QList<resultEntity>& resultEntityList) {
    //QString code = unchangingCode ;
    QString codeComponent = allComponentCode;
    QString codeTest = testCode;

    QString failureComponentName1, failureComponentName2; // 声明两个可能故障的组件名
    QString failureMode1,failureMode2;
    double failureProbability1,failureProbability2=0.0;

    if(entity1.isObservation) {
        codeTest.remove(obsEntityList.at(entity1.index).getDescription());
        failureComponentName1 = obsEntityList.at(entity1.index).getName();
        failureMode1="观测错误";
        failureProbability1 = obsEntityList.at(entity1.index).getFailureProbability();
    } else {
        codeComponent.remove(componentEntityList.at(entity1.index).getDescription());
        failureComponentName1 = componentEntityList.at(entity1.index).getName();
        failureMode1="未知故障";
        failureProbability1 = componentEntityList.at(entity1.index).getFailMode()[0].getProbability();
    }

    if(entity2.isObservation) {
        codeTest.remove(obsEntityList.at(entity2.index).getDescription());
        failureComponentName2 = obsEntityList.at(entity2.index).getName();
        failureMode2="观测错误";
        failureProbability2 = obsEntityList.at(entity2.index).getFailureProbability();
    } else {
        codeComponent.remove(componentEntityList.at(entity2.index).getDescription());
        failureComponentName2 = componentEntityList.at(entity2.index).getName();
        failureMode2="未知故障";
        failureProbability2 = componentEntityList.at(entity2.index).getFailMode()[0].getProbability();
    }

    QString code = unchangingCode + codeComponent +codeTest;
    if(z3Solve(code) == true) {
        // 如果是第一次找到解，记录下这个概率
        if(firstFailurePairProbability == 0.0) {
            firstFailurePairProbability = entity1.failureProbability * entity2.failureProbability;
            //qDebug()<<"如果是第一次找到解，记录下这个概率:"<<firstFailurePairProbability;
        }
        // 在表格中更新这对故障组件的信息
        resultEntity doubleUnknowResult;
        doubleUnknowResult.setResult(failureComponentName1, failureMode1,failureProbability1);
        doubleUnknowResult.setResult(failureComponentName2, failureMode2,failureProbability2);
        resultEntityList.append(doubleUnknowResult);
        //qDebug()<< "doubleUnknowResult.getProbability():"<< doubleUnknowResult.getProbability();
        //emit updateResultTable(doubleUnknowResult.getComponentNames(),doubleUnknowResult.getFailureModes() , doubleUnknowResult.getProbability());
        //ans.append(failureComponentName1 + " , " + failureComponentName2);
        int ansCount =0;
        if(!entity1.isObservation){
            QList<FailureMode> ListFailureMode1 = componentEntityList.at(entity1.index).getFailMode();
            for(int j=1; j<ListFailureMode1.count(); j++) {
                QString codeWithFailure = code;
                codeWithFailure.append(ListFailureMode1[j].getDescribe());
                if(z3Solve(codeWithFailure) == true) {
                    if(!entity2.isObservation){
                        QList<FailureMode> ListFailureMode2 = componentEntityList.at(entity2.index).getFailMode();
                        for(int k=1; k<ListFailureMode2.count(); k++) {
                            codeWithFailure.append(ListFailureMode2[k].getDescribe());
                            if(z3Solve(codeWithFailure) == true) {
                                resultEntity doubleKnowResult;
                                doubleKnowResult.setResult(failureComponentName1, ListFailureMode1[j].getName(),ListFailureMode1[j].getProbability());
                                doubleKnowResult.setResult(failureComponentName2, ListFailureMode2[k].getName(),ListFailureMode2[k].getProbability());
                                resultEntityList.append(doubleKnowResult);
                                //emit updateResultTable(doubleKnowResult.getComponentNames(),doubleKnowResult.getFailureModes() , doubleKnowResult.getProbability());
                                ans.append(failureComponentName1 + " , " + failureComponentName2);
                                ansCount++;
                            }
                        }
                    }
                    else{ //entity2为观测
                        resultEntity doubleResultWithObs;
                        doubleResultWithObs.setResult(failureComponentName1,ListFailureMode1[j].getName(),ListFailureMode1[j].getProbability());
                        doubleResultWithObs.setResult(failureComponentName2, "观测错误",failureProbability2);
                        resultEntityList.append(doubleResultWithObs);
                        //emit updateResultTable(doubleResultWithObs.getComponentNames(),doubleResultWithObs.getFailureModes() , doubleResultWithObs.getProbability());
                        ans.append(failureComponentName1 + " , " + failureComponentName2);
                        ansCount++;
                    }
                }
            }
        }
        if(ansCount)return true;
    }
    return false;// 如果找不到已知故障模式的解，返回false
}

void SystemEntity::solveConflictSets(const QString& modelDescription, const QString& testDescription, QList<QStringList>& list)
{
    //    num = 0;
    //    QTime time;
    //    time.start();

    //    QList<QString> qlist= modelDescription.split("END");
    //    if(qlist.size()!=2){
    //        QStringList ans;
    //        ans.append("Error");
    //        return;
    //    }
    //    QString componentDescription = qlist[0].remove("DEF").remove("BEGIN").remove("END");
    //    QString linkDescription = qlist[1].remove("DEF").remove("BEGIN").remove("END");

    //    QList<ComponentEntity> componentEntityList = creatComponentEntity(componentDescription);


    //    QString systemLinkCode = creatSystemLinkCode(linkDescription);
    //    QString VariablesCode = creatVariablesCode(componentEntityList);
    //    QString testCode = creatTestsCode(testDescription);

    //    unchangingCode="";
    //    unchangingCode.append(VariablesCode);
    //    unchangingCode.append(systemLinkCode);
    //    unchangingCode.append(testCode);

    //    QString out = QString("PrepareTime:").append(QString::number(time.elapsed()/1000.0));
    //    qDebug()<< out<< endl;

    //    solve(list, componentEntityList);
    //    //    return thread_solve(unchangingCode,componentEntityList);
}
void SystemEntity::updateObsVarsMap(const QList<ComponentEntity>& componentEntityList)
{
    obsVarsMap.clear();
    obsVarsList.clear();
    componentNameList.clear();
    componentFailureProbability.clear();
    for(ComponentEntity code: componentEntityList){
        componentNameList.append(code.getName());//器件名称
        componentFailureProbability.insert(code.getName(),code.getFailureProbability());
        QString var = code.getVariable().simplified();
        QStringList varList = var.split("(declare-fun ", QString::SkipEmptyParts);
        for(QString mvar : varList){
            QStringList mvarParts = mvar.split("()", QString::SkipEmptyParts);
            if (mvarParts.size() >= 2) {
                QString name = mvarParts[0].trimmed();
                QString type = mvarParts[1].trimmed();
                type.chop(1); // Remove the last ")"
                type = type.trimmed(); // Remove leading/trailing spaces
                obsVarsMap.insert(name, type);
                obsVarsList.append(name);
            }
        }
    }
}

QString SystemEntity::creatVariablesCode(const QList<ComponentEntity>& componentEntityList)
{
    QString variablesCode;
    for(ComponentEntity code: componentEntityList){
        QString var = code.getVariable().simplified();
        //qDebug()<<"var:"<<var;
        variablesCode.append(var);
    }
    return variablesCode;
}

QList<ComponentEntity> SystemEntity::creatComponentEntity(const QString& componentDescription)
{
    QList<ComponentEntity> ans;

    QList<QString> ListRow= componentDescription.split('\n', QString::SkipEmptyParts);

    for(QString description: ListRow){
        ComponentEntity componentEntity;

        QList<QString> List = description.simplified().split(' ', QString::SkipEmptyParts);
        if(List.size()!=2) continue;
        QString mark = List[0];

        List = List[1].remove(")").split("(");
        if(List.size()!=2) {
            std::cout<<"ComponentEntity Error";
            continue;}

        componentEntity.setName(List[0]);

        QMap<QString, QString> parameterMap;
        List = List[1].split(",");
        for(QString va:List){
            QList<QString> parameter = va.split("=", QString::SkipEmptyParts);
            if(parameter.size()!=2) continue;
            parameterMap.insert(parameter[0],parameter[1]);
        }
        //qDebug()<<"mark :"<<mark;
        component component = database->selectComponentByMark(mark);
        //qDebug()<<"component get from database finished";
        QString makeCode;
        makeCode.append("%").append(mark).append("%");
        componentEntity.setVariable(component.getVariable().replace(makeCode,componentEntity.getName()).simplified());

        QString parameter = component.getParameter();
        QList<QString> parameterList= parameter.split(",", QString::SkipEmptyParts);


        QString descriptionCode = component.getDescription();
        descriptionCode = descriptionCode.replace(makeCode,componentEntity.getName()).simplified();
        //qDebug()<<"descriptionCode: "<<descriptionCode;
        for(QString parameter:parameterList){
            QString parameterCode;
            QString value = "";
            parameterCode.append("%").append(parameter.remove(" ")).append("%");
            if(parameterMap.contains(parameter)){
                value = parameterMap.find(parameter).value();
            }else{
                class::parameter p = database->selectParameterByNameAndComponentId(parameter,component.getId());
                value = p.getDefaultValue();
            }
            descriptionCode = descriptionCode.replace(parameterCode,value).simplified();
        }
        componentEntity.setDescription(descriptionCode);

        //替换ListFailureMode中的器件名称
        QList<FailureMode> ListFailureMode = component.getFailureMode();
        for(int i=0;i<ListFailureMode.count();i++)
        {
            ListFailureMode[i].describe=ListFailureMode[i].describe.replace(makeCode,componentEntity.getName()).simplified();
        }
        //        QStringList ListFailureMode = component.getFailureMode();
        //        for(int i=0;i<ListFailureMode.count();i++)
        //        {
        //            ListFailureMode[i]=ListFailureMode[i].replace(makeCode,componentEntity.getName()).simplified();

        //        }

        //替换ListFailureMode中的变量参数值
        for(QString parameter:parameterList){
            QString parameterCode;
            QString value = "";
            parameterCode.append("%").append(parameter.remove(" ")).append("%");
            if(parameterMap.contains(parameter)){
                value = parameterMap.find(parameter).value();
            }else{
                class::parameter p = database->selectParameterByNameAndComponentId(parameter,component.getId());
                value = p.getDefaultValue();
            }
            for(int i=0;i<ListFailureMode.count();i++)
            {
                ListFailureMode[i].describe=ListFailureMode[i].describe.replace(parameterCode,value).simplified();
            }
        }
        componentEntity.setFailMode(ListFailureMode);

        //实例化器件的故障概率赋值
        componentEntity.setFailureProbability(component.getFailureProbability());

        ans.append(componentEntity);
    }
    return ans;
}

QString SystemEntity::creatTestsCode(const QString& testString)
{
    QString testCode;
    QList<QString> ListRow= testString.split('\n', QString::SkipEmptyParts);
    for(QString code: ListRow){
        testCode.append("(assert");
        testCode.append(code);
        testCode.append(")");
    }
    return testCode;
}

#include <cmath>
//double calFailureProbabilityFromConfidence(double confidence) {
//    // Parameter adjustment
//    double a = 1.0;
//    double b = -23.0258509299405; // log(2.0e-5)
//    double c = 2.0e-5;
//    double d = -2.7; // adjusted to meet constraints for smoother transition at 0.95
//    double e = 2.0e-6;
//    double f = -230.25850929941;

//    double failureProbability = 0.0;

//    if (confidence < 0.0){
//        qDebug()<<"confidence must be between 0.0 and 1.0";
//        return 1.0;
//    }
//    else if (confidence < 0.1) {
//        failureProbability = a * std::exp(b * confidence);
//    }
//    else if (confidence < 0.95) {
//        failureProbability = c * std::exp(d * (confidence - 0.1));
//    }
//    else if (confidence <= 1.0){
//        failureProbability = e * std::exp(f * (confidence - 0.95));
//    }
//    else{
//        qDebug()<<"confidence must be between 0.0 and 1.0";
//        return 1.0e-20;
//    }
//    return failureProbability;
//}
double calFailureProbabilityFromConfidence(double confidence) {
    // 检查输入范围
    if (confidence < 0.0 || confidence > 1.0) {
        qDebug() << "confidence must be between 0.0 and 1.0";
        return confidence < 0.0 ? 1.0 : 1.0e-20;
    }
    // 每个插值段的多项式系数，格式：{a, b, c, d}
    const double coefficients[][4] = {
        {1.0, -12.19794691490771, 34.82536297889254, -28.45893829815438},
        {0.1, -6.0866424680738325, 26.28768148944623, -28.45893829815412},
        {0.05, 1.2832123403691726, -7.863044468338721, 10.94107587737103},
        {0.005, -0.2000734025340788, 3.625085202900858, -24.472343044385635},
        {0.001, -0.021107455076885277, -0.04576625375699124, 2.1583071058939307},
        {0.0001, -0.009496777158379958, 0.277979812127098, -2.5608845791899766},
        {1e-06, 0.00044936183167599273, -0.029326337375699424, -2.5608845791899766},
    };

    // 插值段的x值
    const double x[] = {0.0, 0.1, 0.5, 0.85, 0.9, 0.95, 0.99, 1.0};

    // 确定插值段
    int segment = sizeof(x) / sizeof(x[0]) - 2; // 默认选择最后一个插值段
    for (int i = 0; i < sizeof(x) / sizeof(x[0]) - 1; i++) {
        if (confidence >= x[i] && confidence < x[i + 1]) {
            segment = i;
            break;
        }
    }

    // 计算插值结果
    double dx = confidence - x[segment];
    double a = coefficients[segment][0];
    double b = coefficients[segment][1];
    double c = coefficients[segment][2];
    double d = coefficients[segment][3];
    double failureProbability = ((d * dx + c) * dx + b) * dx + a;

    return failureProbability;
}

QList<obsEntity> SystemEntity::creatObsEntity(const QList<TestItem>& testItemList) {
    QList<obsEntity> obsEntitys;
    double lowerLimitRatio = 0.95;
    double upperLimitRatio = 1.05;
    double errorValue = 0.0;
    int testIndex = 0;
    for (const auto& testItem : testItemList) {
        testIndex++; // increment the testIndex for the next TestItem
        if(testItem.value=="" || testItem.variable=="")continue;
        obsEntity obs;
        obs.setName("obs" + QString::number(testIndex));
        obs.setVariable(testItem.variable);
        obs.setConfidence(testItem.confidence);

        QString description;
        QString varType = obsVarsMap[testItem.variable];

        if(testItem.testType=="依赖功能"){
            TestItem actC = functionInfoMap[testItem.variable].actuatorConstraint;
            if(testItem.value=="功能正常")description = QString("(assert (= %1 %2))").arg(actC.variable).arg(actC.value);
            else description = QString("(assert (not (= %1 %2)))").arg(actC.variable).arg(actC.value);
            obs.obsType = testItem.testType;
        }
        else{
            // 判断变量的类型并构造description
            if(testItem.variable.endsWith("u"))errorValue=220*0.01;
            if(testItem.variable.endsWith("i"))errorValue=0.1;
            if (varType == "(Array Int Real)") {
                QString trimmedValue = testItem.value;
                QStringList components;
                if (trimmedValue.startsWith('(') && trimmedValue.endsWith(')')) {
                    trimmedValue.remove('(').remove(')');
                    QStringList positions = trimmedValue.split(',');
                    for (int i = 0; i < positions.size(); ++i) {
                        if (!positions[i].trimmed().isEmpty()) {
                            bool ok;
                            double num = positions[i].trimmed().toDouble(&ok);
                            if (ok) {
                                QString part = QString("(>= (select %1 %2) %3) "
                                                       "(<= (select %1 %2) %4)")
                                        .arg(testItem.variable)
                                        .arg(i)
                                        .arg(QString::number(num * lowerLimitRatio - errorValue, 'g'))
                                        .arg(QString::number(num * upperLimitRatio + errorValue, 'g'));
                                components << part;
                            } else {
                                // error: non-numeric value encountered
                                qDebug()<<"Error in creatObsEntity: non-numeric input";
                            }
                        }
                    }
                } else {
                    //输入常量符号而非数值的情况
                    for (int i = 0; i < 3; ++i) {
                        QString part = QString("(>= (select %1 %2) (* (select %3 %2) %4)) "
                                               "(<= (select %1 %2) (* (select %3 %2) %5))")
                                .arg(testItem.variable)
                                .arg(i)
                                .arg(trimmedValue)
                                .arg(lowerLimitRatio)
                                .arg(upperLimitRatio);
                        components << part;
                    }
                }
                description = "(assert (and " + components.join(" ") + "))";
            } else if (varType == "Real") {
                bool ok;
                double num =testItem.value.trimmed().toDouble(&ok);
                if(ok)
                {
                    description = QString("(assert (and (>= %1 %2)(<= %1 %3)))")
                            .arg(testItem.variable)
                            .arg(QString::number(num * lowerLimitRatio - errorValue, 'g'))
                            .arg(QString::number(num * upperLimitRatio + errorValue, 'g'));
                    //qDebug()<<"description:"<<description;
                }
                else
                {
                    //"[0,100.2]" , "(0,100.2)" , "[0,100.2)" , "(0,100.2]" , "<=100.2" , "<100.2" , ">100.2" , ">=100.2" , "smt(> %1 (* L7.1.i 1000))"
                    //QRegularExpression re("([\\[\\(])?\\s*([\\d\\.]+)?\\s*,\\s*([\\d\\.]+)?\\s*([\\]\\)])?|(<=|>=|<|>)\\s*([\\d\\.]+)|(smt\\(\\S+.+\\))");
                    QRegularExpression re("([\\[\\(])?\\s*(-?[\\d\\.]+)?\\s*,\\s*(-?[\\d\\.]+)?\\s*([\\]\\)])?|(<=|>=|<|>)\\s*(-?[\\d\\.]+)|(smt\\(\\S+.+\\))");
                    QRegularExpressionMatch match = re.match(testItem.value.trimmed());
                    if(match.hasMatch()) {
                        if(match.captured(1).length() > 0 && match.captured(4).length() > 0) {
                            QString startCompare = match.captured(1) == "[" ? ">=" : ">";
                            QString endCompare = match.captured(4) == "]" ? "<=" : "<";
                            double startValue = match.captured(2).toDouble();
                            double endValue = match.captured(3).toDouble();
                            description = QString("(assert (and (%1 %2 %3)(%4 %2 %5)))")
                                    .arg(startCompare)
                                    .arg(testItem.variable)
                                    .arg(QString::number(startValue, 'g'))
                                    .arg(endCompare)
                                    .arg(QString::number(endValue, 'g'));
                        } else if(match.captured(5).length() > 0) {
                            QString compare = match.captured(5);
                            double compareValue = match.captured(6).toDouble();
                            description = QString("(assert (%1 %2 %3))")
                                    .arg(compare)
                                    .arg(testItem.variable)
                                    .arg(QString::number(compareValue, 'g'));
                        } else if(match.captured(7).length() > 0) {
                            QString smtCode = match.captured(7).trimmed().remove("smt").replace("%1", testItem.variable);
                            description = QString("(assert %1)").arg(smtCode);
                        }
                        //qDebug()<<"description:"<<description;
                    }
                    else
                    {
                        // error: non-numeric value encountered
                        qDebug()<<"Error in creatObsEntity: non-numeric input";
                    }
                }
            } else if (varType == "Bool") {
                description = QString("(assert (= %1 %2))")
                        .arg(testItem.variable)
                        .arg(testItem.value);
            }
        }
        qDebug()<<"obs description:"<<description;
        obs.setDescription(description);

        // Construct failureProbability
        //double failureProbability = 2.0 / testItem.confidence * 1.0e-6;
        //obs.setFailureProbability(failureProbability);
        obs.setFailureProbability(calFailureProbabilityFromConfidence(testItem.confidence));

        obsEntitys.append(obs);
    }
    return obsEntitys;
}

void SolveByType(int Type)
{
    if(CurSolveCandidateConflictIdx[Type]<0) return;
    QList<ComponentEntity> candidateConflict ;
    candidateConflict=candidateConflictList[CurSolveCandidateConflictIdx[Type]];
    QString code = unchangingCode;
    for(ComponentEntity componentEntity:candidateConflict){
        code.append(componentEntity.getDescription());}
    //Lu 输出待z3求解code
    //qDebug().noquote()<<"==========================\nz3 code:\n"<< code;
    ThreadSolveResult[Type] = z3Solve(code);
}
void UpdateCurSolveCandidateConflictIdx(int index,int Type)
{
    for(int j=0;j<3;j++)
    {
        if(j==Type) continue;
        if(index<CurSolveCandidateConflictIdx[j]) CurSolveCandidateConflictIdx[j]--;
        if(index==CurSolveCandidateConflictIdx[j]) CurSolveCandidateConflictIdx[j]=-1;
    }
}
void ProcessResult(int Type)
{
    if(CurSolveCandidateConflictIdx[Type]<0) return;
    int CurIdx=CurSolveCandidateConflictIdx[Type];
    if(ThreadSolveResult[Type]==false){
        //在结果冲突集合中移除此冲突集的超集
        QList<QList<ComponentEntity>> temp_list;        //只是用来避免一直对List进行remove
        for(int i=0;i<ConflictList.size();i++){
            if(isSuperSet(candidateConflictList[CurIdx],ConflictList[i])){
                //                ConflictList.removeAt(i);
            } else {
                temp_list.append(ConflictList[i]);
            }
        }
        ConflictList = temp_list;

        //在候选集合中移除此冲突集的超集
        for(int i = CurIdx+1;i<candidateConflictList.size();){
            if(isSuperSet(candidateConflictList[CurIdx],candidateConflictList[i])){
                candidateConflictList.removeAt(i);
                UpdateCurSolveCandidateConflictIdx(i,Type);
            } else {
                i++;
            }
        }

        ConflictList.append(candidateConflictList[CurIdx]);
    }
    //sat 不冲突
    else if(ThreadSolveResult[Type]==true){
        //在候选集合中移除此集合的子集
        for(int i = 0;i<CurIdx;){
            if(isSuperSet(candidateConflictList[i],candidateConflictList[CurIdx])){
                candidateConflictList.removeAt(i);
                UpdateCurSolveCandidateConflictIdx(i,Type);
                CurIdx--;
            } else {
                i++;
            }
        }
    }
    candidateConflictList.removeAt(CurIdx);
    UpdateCurSolveCandidateConflictIdx(CurIdx,Type);
}
void GetCurSolveCandidateConflictIdx()
{
    if(candidateConflictList.count()>=1) CurSolveCandidateConflictIdx[0]=0;
    else CurSolveCandidateConflictIdx[0]=-1;
    if(candidateConflictList.count()>=3) CurSolveCandidateConflictIdx[1]=candidateConflictList.count()/2;
    else CurSolveCandidateConflictIdx[1]=-1;
    if(candidateConflictList.count()>=2) CurSolveCandidateConflictIdx[2]=candidateConflictList.count()-1;
    else CurSolveCandidateConflictIdx[2]=-1;
}
Mythread *ThreadSolve[3];//ThreadSolve[0]:从候选集的头开始进行求解计算  ThreadSolve[1]:从候选集的中间开始进行求解计算  ThreadSolve[2]:从候选集的尾开始进行求解计算
void CommandAndUpdateCandidateConflictList()
{
    int original_size = candidateConflictList.size();
    for(int i=0;i<3;i++) ThreadSolve[i]=new Mythread(nullptr,i+1);
    bool FirstIn=true;
    while(candidateConflictList.size())
    {
        double progress =1.0-(double)candidateConflictList.size()/original_size;
        ProgressNum = 100 * progress;
        //派发任务给3条子线程，第1条子线程从候选集的头开始进行求解计算，第2条子线程从候选集的尾开始进行求解计算，第3条子线程从候选集的中间开始进行求解计算
        if(FirstIn)
        {
            GetCurSolveCandidateConflictIdx();
            for(int i=0;i<3;i++) if(CurSolveCandidateConflictIdx[i]>=0) ThreadSolve[i]->start();
            FirstIn=false;
        }
        if((ThreadSolve[0]->isFinished()||CurSolveCandidateConflictIdx[0]<0)&&(ThreadSolve[1]->isFinished()||CurSolveCandidateConflictIdx[1]<0)&&(ThreadSolve[2]->isFinished()||CurSolveCandidateConflictIdx[2]<0))
        {
            for(int i=0;i<3;i++) if(CurSolveCandidateConflictIdx[i]>=0) ProcessResult(i);
            GetCurSolveCandidateConflictIdx();
            for(int i=0;i<3;i++) if(CurSolveCandidateConflictIdx[i]>=0) ThreadSolve[i]->start();
        }
    }
}
void SystemEntity::onCommandThreadEnd()
{
    QStringList ans;
    for(int i=0;i<ConflictList.size();i++){
        QString  Conflict = "{";
        for(ComponentEntity componentEntity:ConflictList[i]){
            Conflict.append(componentEntity.getName());
            Conflict.append(",");
        }
        Conflict.remove(Conflict.size()-1,1);
        Conflict.append("}");
        ans.append(Conflict);
    }
    //    QString out = "SolveTime:" + QString::number(timeSlove.elapsed()/1000.0);
    //    qDebug()<< out<< endl;
    ProgressNum=100;
    emit(ProgressEnd(ans));
    Z3_finalize_memory();
}
void SystemEntity::solve(const QList<ComponentEntity>& componentEntityList)
{
    //timeSlove.restart();
    candidateConflictList.clear();
    ConflictList.clear();
    ProgressNum=0;

    if(SoveType == 0)
        candidateConflictList = creatCandidateConflict(componentEntityList);
    else if(SoveType == 1)
        candidateConflictList = creatCandidateConflictWithGraph(componentEntityList);

    Mythread *CommandThread=new Mythread(nullptr,0);
    connect(CommandThread,SIGNAL(CommandThreadEnd()),this,SLOT(onCommandThreadEnd()));
    CommandThread->start();
}

void SystemEntity::solve(const QList<QStringList>& list, const QList<ComponentEntity>& componentEntityList)
{
    //timeSlove.restart();
    candidateConflictList.clear();
    ConflictList.clear();
    ProgressNum=0;

    QList<ComponentEntity> componentEntityTemp;
    int length1 = list.count();
    int length_com = componentEntityList.count();
    for(int i=0; i<length1; i++)
    {
        int length2 = list.at(i).count();
        for(int j=0; j<length2; j++)
        {
            QString list_temp = list.at(i).at(j);

            for(int m=0; m<length_com; m++)
            {
                if(list_temp == componentEntityList[m].getName())
                {
                    componentEntityTemp.append(componentEntityList[m]);
                    break;
                }
            }
        }

        candidateConflictList.append(componentEntityTemp);
        componentEntityTemp.clear();
    }

    //排序
    //    QList<ComponentEntity> newComponentEntityList;
    //    for(int i=0;i<candidateConflictList.length()-1;i++){
    //        for(int j=0;j<candidateConflictList.length()-1-i;j++){
    //            if(candidateConflictList[j].size()>candidateConflictList[j+1].size()){
    //                newComponentEntityList = candidateConflictList[j];
    //                candidateConflictList[j] = candidateConflictList[j+1];
    //                candidateConflictList[j+1] = newComponentEntityList;
    //            }
    //        }
    //    }
    std::sort(candidateConflictList.begin(), candidateConflictList.end(), [](QList<ComponentEntity>& a, QList<ComponentEntity>& b){return a.size() < b.size();});


    qDebug()<<"candidateConflictList加载完成";

    Mythread *CommandThread=new Mythread(nullptr,0);
    connect(CommandThread,SIGNAL(CommandThreadEnd()),this,SLOT(onCommandThreadEnd()));
    CommandThread->start();
}

QString SystemEntity::creatSystemLinkCode(const QString& systemLinkDescription)
{
    QString systemLinkCode;
    QList<QString> ListRow= systemLinkDescription.split('\n', QString::SkipEmptyParts);
    for(QString description: ListRow){
        if(description.startsWith("rawsmt")){
            description = description.remove("rawsmt").simplified();
            systemLinkCode.append(description);
        }
        else if(description.startsWith("(assert") || description.startsWith("(declare-fun")){
            systemLinkCode.append(description);
        }
        else if(description.startsWith("link")){
            description = description.remove("link").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;
            QString code = "(assert (= %A% %B%))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect2e(1P,")){
            description = description.remove("connect2e(1P,").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;
            QString code = "(assert (= %A%.u %B%.u))(assert (= (+ (select %A%.i 0) (select %B%.i 0)) 0))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect2e(3P,")){
            description = description.remove("connect2e(3P,").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;
            QString code = "(assert (= %A%.u %B%.u))(assert (= (+ (select %A%.i 0) (select %B%.i 0)) 0))(assert (= (+ (select %A%.i 1) (select %B%.i 1)) 0))(assert (= (+ (select %A%.i 2) (select %B%.i 2)) 0))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect3e(1P,")){
            description = description.remove("connect3e(1P,").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=3)
                continue;
            QString code = "(assert (= %A%.u %B%.u %C%.u))(assert (= (+ (select %A%.i 0) (select %B%.i 0) (select %C%.i 0)) 0))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            code.replace("%C%", parameters[2]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect3e(3P,")){
            description = description.remove("connect3e(3P,").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=3)
                continue;
            QString code = "(assert (= %A%.u %B%.u %C%.u))(assert (= (+ (select %A%.i 0) (select %B%.i 0) (select %C%.i 0)) 0))(assert (= (+ (select %A%.i 1) (select %B%.i 1) (select %C%.i 1)) 0))(assert (= (+ (select %A%.i 2) (select %B%.i 2) (select %C%.i 2)) 0))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            code.replace("%C%", parameters[2]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect2e")){
            description = description.remove("connect2e").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;
            QString code = "(assert (= (+ %A%.i %B%.i) 0))(assert (= %A%.u %B%.u))";
            //QString code = "(assert (= %A%.i %B%.i))(assert (= %A%.u %B%.u))";

            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect3e")){
            description = description.remove("connect3e").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=3)
                continue;
            QString code = "(assert (= (+ %A%.i %B%.i %C%.i) 0))(assert (= %A%.u %B%.u %C%.u))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            code.replace("%C%", parameters[2]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connecte")){
            description = description.remove("connecte").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()<2)
                continue;
            QString code = "(assert (= (+";
            for(int i=0;i<parameters.size();i++)code.append(" ").append(parameters[i]).append(".i");
            code.append(") 0))(assert (=");
            for(int i=0;i<parameters.size();i++)code.append(" ").append(parameters[i]).append(".u");
            code.append("))");
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect2m")){
            description = description.remove("connect2m").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;
            QString code = "(assert (= (+ %A%.F %B%.F) 0))(assert (= %A%.M %B%.M))";

            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect3m")){
            description = description.remove("connect3m").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=3)
                continue;
            QString code = "(assert (= (+ %A%.F %B%.F %C%.F) 0))(assert (= %A%.M %B%.M %C%.M))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            code.replace("%C%", parameters[2]);
            systemLinkCode.append(code);
        }
    }
    return systemLinkCode;
}

QList<QList<ComponentEntity>> SystemEntity::AnlysisSystemLink(const QString& systemLinkDescription, QList<ComponentEntity>& originalComponent)
{
    QVector<QString> module;
    QVector<ArcData> arc;

    //得到端点列表
    for(int i=0; i<originalComponent.count();i++)
        module.push_back(originalComponent[i].getName());

    QList<QList<ComponentEntity>> myVector;

    QString systemLinkCode;
    QList<QString> ListRow= systemLinkDescription.split('\n', QString::SkipEmptyParts);
    for(QString description: ListRow){
        if(description.startsWith("connect2e")){
            description = description.remove("connect2e").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=2)
                continue;

            QStringList port_1 = parameters[0].split('.',QString::SkipEmptyParts);
            QStringList port_2 = parameters[1].split('.',QString::SkipEmptyParts);

            ArcData data;
            data.Tail = port_1[0];
            data.Head = port_2[0];
            data.Weight = 1;
            arc.push_back(data);


            for(int i=0; i<module.length(); i++)
            {
                if(port_1[0] == module.at(i))
                {
                    int find_ans = originalComponent[i].findPort(port_1[1]);
                    if(find_ans == -1)
                        originalComponent[i].addPort(port_1[1]);
                    break;
                }
            }

            for(int i=0; i<module.length(); i++)
            {
                if(port_2[0] == module.at(i))
                {
                    int find_ans = originalComponent[i].findPort(port_2[1]);
                    if(find_ans == -1)
                        originalComponent[i].addPort(port_2[1]);
                    break;
                }
            }


            QString code = "(assert (= (+ %A%.i %B%.i) 0))(assert (= %A%.u %B%.u))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            systemLinkCode.append(code);
        }
        else if(description.startsWith("connect3e")){
            description = description.remove("connect3e").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()!=3)
                continue;
            QString code = "(assert (= (+ %A%.i %B%.i %C%.i) 0))(assert (= %A%.u %B%.u %C%.u))";
            code.replace("%A%", parameters[0]);
            code.replace("%B%", parameters[1]);
            code.replace("%C%", parameters[2]);
            systemLinkCode.append(code);
        }

        else if(description.startsWith("connecte")){
            description = description.remove("connecte").remove("(").remove(")").simplified();
            QList<QString> parameters= description.split(',', QString::SkipEmptyParts);
            if(parameters.size()<2)
                continue;

            if(parameters.size() == 2)
            {
                QStringList port_1 = parameters[0].split('.',QString::SkipEmptyParts);
                QStringList port_2 = parameters[1].split('.',QString::SkipEmptyParts);

                ArcData data;
                data.Tail = port_1[0];
                data.Head = port_2[0];
                data.Weight = 1;
                arc.push_back(data);


                for(int i=0; i<module.length(); i++)
                {
                    if(port_1[0] == module.at(i))
                    {
                        int find_ans = originalComponent[i].findPort(port_1[1]);
                        if(find_ans == -1)
                            originalComponent[i].addPort(port_1[1]);
                        break;
                    }
                }

                for(int i=0; i<module.length(); i++)
                {
                    if(port_2[0] == module.at(i))
                    {
                        int find_ans = originalComponent[i].findPort(port_2[1]);
                        if(find_ans == -1)
                            originalComponent[i].addPort(port_2[1]);
                        break;
                    }
                }
            }
            else
            {

                //下面这个是加了虚拟端口的
                //                        QString virtual_point = "Virtual" + QString::number(VirtualPoint);
                //                        VirtualPoint++;
                //                        module.append(virtual_point);
                //                        for(int i=0; i<parameters.size(); i++)
                //                        {
                //                            QStringList port_1 = parameters[i].split('.',QString::SkipEmptyParts);

                //                            ArcData data;
                //                            data.Tail = port_1[0];
                //                            data.Head = virtual_point;
                //                            data.Weight = 1;
                //                            arc.push_back(data);


                ////                            for(int m=0; m<module.length(); m++)
                ////                            {
                ////                                if(port_1[0] == module.at(m))
                ////                                {
                ////                                    int find_ans = originalComponent[m].findPort(port_1[1]);
                ////                                    if(find_ans == -1)
                ////                                        originalComponent[m].addPort(port_1[1]);
                ////                                    break;
                ////                                }
                ////                            }

                //                        }






                //下面这段是没加虚拟端口的
                for(int i=0; i<parameters.size()-1; i++)
                {
                    for(int j=1; j<parameters.size(); j++)
                    {

                        QStringList port_1 = parameters[i].split('.',QString::SkipEmptyParts);
                        QStringList port_2 = parameters[j].split('.',QString::SkipEmptyParts);

                        ArcData data;
                        data.Tail = port_1[0];
                        data.Head = port_2[0];
                        data.Weight = 1;
                        arc.push_back(data);


                        for(int m=0; m<module.length(); m++)
                        {
                            if(port_1[0] == module.at(m))
                            {
                                int find_ans = originalComponent[m].findPort(port_1[1]);
                                if(find_ans == -1)
                                    originalComponent[m].addPort(port_1[1]);
                                break;
                            }
                        }

                        for(int n=0; n<module.length(); n++)
                        {
                            if(port_2[0] == module.at(n))
                            {
                                int find_ans = originalComponent[n].findPort(port_2[1]);
                                if(find_ans == -1)
                                    originalComponent[n].addPort(port_2[1]);
                                break;
                            }
                        }
                    }

                }
            }





            QString code = "(assert (= (+";
            for(int i=0;i<parameters.size();i++)code.append(" ").append(parameters[i]).append(".i");
            code.append(") 0))(assert (=");
            for(int i=0;i<parameters.size();i++)code.append(" ").append(parameters[i]).append(".u");
            code.append("))");
            systemLinkCode.append(code);
        }


    }

    graph->Init(&module,&arc);
    //    graph->CandidateConflict();
    //    graph->Display();

    //    graph->Display_DFS(&node[0]);
    //    graph->Display_DFS(&node[1]);
    //    graph->Display_DFS(&node[2]);


    return  myVector;
}

bool z3Solve(const QString &logic, int timeoutMs, QMap<QString, QString> *modelOut)
{
    g_currentZ3Logic = &logic;
    g_z3ErrorLogged = false;
    g_lastZ3ErrorMessage.clear();
    if (modelOut) {
        modelOut->clear();
    }

    try {
        z3::context c;
        z3::solver s(c);
        Z3_set_error_handler(c, errorHandler);

        if (timeoutMs > 0) {
            z3::params params(c);
            params.set("timeout", static_cast<unsigned>(timeoutMs));
            s.set(params);
        }

        s.from_string(const_cast<char*>(logic.toStdString().c_str()));
        if (g_z3ErrorLogged) {
            g_currentZ3Logic = nullptr;
            return false;
        }

        const z3::check_result checkResult = s.check();
        if (g_z3ErrorLogged) {
            g_currentZ3Logic = nullptr;
            return false;
        }

        bool sat = false;
        switch (checkResult) {
        case z3::check_result::sat:
            sat = true;
            break;
        case z3::check_result::unsat:
            sat = false;
            break;
        case z3::check_result::unknown:
            QMessageBox::information(nullptr, QObject::tr("Z3求解"), QObject::tr("Z3 返回 unknown 结果"));
            sat = false;
            break;
        default:
            QMessageBox::information(nullptr, QObject::tr("Z3求解"), QObject::tr("Z3 返回未知结果"));
            sat = false;
            break;
        }

        if (sat && modelOut) {
            modelOut->clear();
            z3::model model = s.get_model();
            const unsigned count = model.size();
            for (unsigned i = 0; i < count; ++i) {
                z3::func_decl decl = model.get_const_decl(i);
                const QString name = QString::fromStdString(decl.name().str());
                z3::expr value = model.get_const_interp(decl);
                modelOut->insert(name, formatModelExpr(value));
            }
        } else if (!sat && modelOut) {
            modelOut->clear();
        }

        g_currentZ3Logic = nullptr;
        g_z3ErrorLogged = false;
        g_lastZ3ErrorMessage.clear();
        return sat;
    } catch (const z3::exception &ex) {
        const QString message = QString::fromUtf8(ex.msg());
        if (modelOut) {
            modelOut->clear();
        }
        if (g_currentZ3Logic && !g_z3ErrorLogged) {
            const QString path = writeZ3FailureLog(*g_currentZ3Logic, message);
            if (!path.isEmpty()) {
                qWarning() << "Z3 exception logged to" << QDir::toNativeSeparators(path);
            }
        }
        qWarning() << "Z3 exception:" << message;
        g_currentZ3Logic = nullptr;
        g_z3ErrorLogged = false;
        g_lastZ3ErrorMessage.clear();
        return false;
    }
}


QList<QList<ComponentEntity>> SystemEntity::creatCandidateConflict(const QList<ComponentEntity>& componentEntityList)
{
    QList<QList<ComponentEntity>> myVector;

    qDebug()<<"componentEntityList "<<componentEntityList.size();

    QList<ComponentEntity> newComponentEntityList;

    if(componentEntityList.size()==0){
        return myVector;
    }
    if(componentEntityList.size()==1){
        newComponentEntityList.append(componentEntityList[0]);
        myVector.append(newComponentEntityList);
        return myVector;
    }

    //Lu输出所有器件组合 临时调试使用
    //    if(componentEntityList.size()>1){
    //        myVector.append(componentEntityList);
    //        return myVector;
    //    }

    newComponentEntityList.append(componentEntityList[componentEntityList.size() - 1]);
    myVector.append(newComponentEntityList);

    for (int i = componentEntityList.size() - 2; i >= 0; i--)
    {
        int vectorLen = myVector.size();
        for (int j = 0; j < vectorLen; j++)
        {
            newComponentEntityList.clear();
            newComponentEntityList.append(componentEntityList[i]);
            for(ComponentEntity componentEntity:myVector[j]){
                newComponentEntityList.append(componentEntity);
            }
            myVector.append(newComponentEntityList);
        }

        newComponentEntityList.clear();
        newComponentEntityList.append(componentEntityList[i]);
        myVector.append(newComponentEntityList);
    }
    QTime timer;
    timer.restart();
    qDebug()<<"finish 1";
    //下面这段是排序
    //    for(int i=0;i<myVector.length()-1;i++){
    //        for(int j=0;j<myVector.length()-1-i;j++){
    //            if(myVector[j].size()>myVector[j+1].size()){
    //                newComponentEntityList = myVector[j];
    //                myVector[j] = myVector[j+1];
    //                myVector[j+1] = newComponentEntityList;
    //            }
    //        }
    //    }
    std::sort(myVector.begin(), myVector.end(), [](QList<ComponentEntity>& a, QList<ComponentEntity>& b){return a.size() < b.size();});
    qDebug()<<"finish 2 " << timer.elapsed() << " ms";
    //算复杂度大概
    //    int ans = 0;
    //    int n = 11;
    //    for(int i=1; i<=n; i++)
    //    {
    //        int up = n*(n-1)*(n-i+1);
    //        int down = 1;
    //        for(int j=1; j<=i;j++)
    //            down = down * j;

    //        ans = ans + up/down;
    //    }

    //    qDebug()<<"ans"<<ans<<"my_vector length"<<myVector.length();

    //    qDebug()<<"输出排列组合";

    //    QStringList ans;
    //    for(int i=0; i<myVector.count(); i++)
    //    {
    //        for(int j=0; j<myVector.at(i).count();j++)
    //            ans.push_back(myVector[i][j].getName());

    //        qDebug()<<ans;
    //        ans.clear();
    //    }


    return myVector;

}

QList<QList<ComponentEntity>> SystemEntity::creatCandidateConflictWithGraph(const QList<ComponentEntity>& componentEntityList)
{
    QList<QList<ComponentEntity>> myVector;

    QList<ComponentEntity> newComponentEntityList;

    //    QTime timer;
    //    timer.restart();
    QList<QStringList> connect_list = graph->CandidateConflict();

    currentModel->setConnectNodes(connect_list);

    //    qDebug()<<"排列组合时间ms"<<timer.elapsed();

    for(int i=0; i<connect_list.count();i++)
    {
        newComponentEntityList.clear();
        for(int j=0; j<connect_list.at(i).count();j++)
        {


            for(int m=0; m<componentEntityList.count();m++)
            {
                if(componentEntityList[m].getName() == connect_list.at(i).at(j))
                    newComponentEntityList.push_back(componentEntityList[m]);
            }
        }

        myVector.push_back(newComponentEntityList);

    }

    //排序
    //    for(int i=0;i<myVector.length()-1;i++){
    //        for(int j=0;j<myVector.length()-1-i;j++){
    //            if(myVector[j].size()>myVector[j+1].size()){
    //                newComponentEntityList = myVector[j];
    //                myVector[j] = myVector[j+1];
    //                myVector[j+1] = newComponentEntityList;
    //            }
    //        }
    //    }
    std::sort(myVector.begin(), myVector.end(), [](QList<ComponentEntity> a, QList<ComponentEntity> b){return a.size() < b.size();});

    //    qDebug()<<"输出名称排列组合";

    ////    QString ans;
    //    for(int i=0; i<connect_list.count(); i++)
    //        qDebug()<<connect_list.at(i);

    //    qDebug()<<"输出component排列组合";
    //    QStringList ans;
    //    for(int i=0; i<myVector.count(); i++)
    //    {
    //        for(int j=0; j<myVector.at(i).count();j++)
    //        {
    //            ans<<myVector[i][j].getName();
    //        }

    //        qDebug()<<ans;
    //        ans.clear();
    //    }

    return myVector;

}

bool isSuperSet(QList<ComponentEntity>& set, QList<ComponentEntity>& superSet)
{
    for (int i = 0; i < set.size(); i++)
    {
        int j;
        for (j = 0; j < superSet.size(); j++)
            if(set[i] == superSet[j])
                break;
        if (j == superSet.size())
            return false;
    }
    return true;
}

QList<TestItem> SystemEntity::RecommendObs(QString currentfunctionName, QList<QStringList> portListInConnectionList, QMap<QString, QString> functionLinkMap, QMap<QString, QString> functionComponentDependencyMap, QMap<QString, QString> functionDependencyMap, QMap<QString, double> componentFailureProbability, QList<resultEntity> currentResultEntityList) {
    QList<TestItem> recommendTestItemList;
    // 步骤1: 构建当前被诊断功能的图网络

    // 步骤2: 计算各测点的综合信息熵并创建推荐测试项目列表
    //    for (QString& port : linkStructure) {
    //            if (testItemProbabilities.contains(port)) {
    //                double p_pass = 1 - testItemProbabilities[port];
    //                double p_fail = 1 - p_pass;

    //                QStringList d_set = portListInConnectionList[linkStructure.indexOf(port)];
    //                QStringList u_set = portListInConnectionList[linkStructure.indexOf(port)];
    //                u_set.removeOne(port);

    //                double inform_d = 0.0;
    //                for (QString& d : d_set) {
    //                    double p = testItemProbabilities[d];
    //                    inform_d += -p * std::log2(p);
    //                }

    //                double inform_u = 0.0;
    //                for (QString& u : u_set) {
    //                    double p = testItemProbabilities[u];
    //                    inform_u += -p * std::log2(p);
    //                }

    //                double information_entropy = p_pass * inform_d + p_fail * inform_u;

    //                TestItem item;
    //                item.variable = port;
    //                item.confidence = information_entropy;
    //                recommendTestItemList.append(item);
    //            }
    //        }

    // 步骤3: 对推荐测试项目列表进行排序,值越小代表测试过后系统不确定性越好，该测试获取的信息量越大
    std::sort(recommendTestItemList.begin(), recommendTestItemList.end(), [](const TestItem& a, const TestItem& b) { return a.confidence < b.confidence; });
    return recommendTestItemList;
}
