#ifndef RULEPOOL_H
#define RULEPOOL_H

#include "myqsqldatabase.h"
#include "rulevariablepool.h"
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:故障诊断规则池
**************************************************/
#define TaskThreshold 0.1
class RulePool
{
public:
    RulePool();

    //设置规则池数据库指针
    void SetDatabase(myQSqlDatabase *TMATE_Database){m_Database = TMATE_Database;}

    //初始化规则信息
    bool InitRuleVector();

    //获取规则池规则信息
    QVector<DataBase::Str_Rule> GetRules(){return m_rules;}

    //开始条件解析
    void StartRuleDetection(RuleVariablePool &VariablePool);

    //计算条件语句结果
    bool calculate(QString expression,RuleVariablePool &VariablePool,double &ans);

    //设置所有规则为未检测
    void SetAllRuleUnused();

    //解析并对结果语句赋值
    bool ParsingAndAssigningResultingStatement(QString expression,RuleVariablePool &VariablePool);

    //获取规则相关变量的当前值用于显示
    QString GetRelatedParaValStr(QString RuleStr);

    QString GetRelatedWarnParaValStr(QString WarnRuleStr);
private:

    //数据库指针
    myQSqlDatabase *m_Database = nullptr;

    //规则信息
    QVector<DataBase::Str_Rule> m_rules;

    QVector<DataBase::Str_WarnRule> m_Warnrules;

    //规则是否生效,1代表正常，0代表异常，-1代表未用
    QVector<int> m_rulesIsUsed;

    //规则满足条件保持时间 单位200ms
    QVector<int> m_RuleDurTime;

    QVector<bool> m_ruleLastState;
};

#endif // RULEPOOL_H
