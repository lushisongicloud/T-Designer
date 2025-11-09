#include "rulepool.h"
#include  <ctype.h>
#include <string>
#include <algorithm>
#include<numeric>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

#define Epslion 1e-8
extern RuleVariablePool m_RuleVariablePool;
extern RulePool m_RulePool;
QStringList ListWarnningInfo;
extern QString GetParaStrWithoutValue(QString ParaStr);
RulePool::RulePool()
{

}

bool RulePool::InitRuleVector()
{
    //清空规则池
    m_rules.clear();

    m_Warnrules.clear();
    //查询是否设置的数据库指针
    if(m_Database==nullptr)
        return false;

    //查询所有规则信息
    m_rules =  m_Database->SelectRulesInforFromRuleBaseTable("","",1);

    m_Warnrules= m_Database->SelectWarnRulesInforFromRuleBaseTable("",1);
    //初始化所有规则信息为未检测
    for(int i=0;i<m_rules.size();i++){
        m_rulesIsUsed.push_back(-1);
        m_RuleDurTime.push_back(0);
        m_ruleLastState.push_back(false);
    }

    return true;
}

void RulePool::SetAllRuleUnused()
{
    //设置所有规则信息为未检测
    for(int i=0;i<m_rulesIsUsed.size();i++){
        m_rulesIsUsed[i]=-1;
    }
}

//获取规则相关变量的当前值用于显示
QString RulePool::GetRelatedWarnParaValStr(QString WarnRuleStr)
{
    QString RetStr="";
    QStringList ListWarnRuleStr=WarnRuleStr.split(",");
    for(int i=0;i<ListWarnRuleStr.count();i++)
    {
        if(ListWarnRuleStr.at(i).contains("=")) ListWarnRuleStr[i]=ListWarnRuleStr.at(i).mid(0,ListWarnRuleStr.at(i).indexOf("="));
    }
    for (int i = 0; i < ListWarnRuleStr.count(); ++i) {
            QString VariableName = ListWarnRuleStr.at(i);
            //判断变量池是否含有该变量，若不存在该变量则返回false
            if(m_RuleVariablePool.isContainVariable(VariableName))
            {
               //获取该变量信息
               DataBase::Signal signal = m_RuleVariablePool.GetVariable(VariableName);
               if(signal.valueType=="INT"){
                   RetStr+=VariableName+"="+QString::number(static_cast<double>(signal.value.INT));
                   if(i<ListWarnRuleStr.count()-1) RetStr+=",";
               }
               if(signal.valueType=="ENUM"){
                   RetStr+=VariableName+"="+QString::number(static_cast<double>(signal.value.ENUM));
                   if(i<ListWarnRuleStr.count()-1) RetStr+=",";
               }
               if(signal.valueType=="BOOL"){
                   RetStr+=VariableName+"="+QString::number(static_cast<double>(signal.value.BOOL?1:0));
                   if(i<ListWarnRuleStr.count()-1) RetStr+=",";
               }
               if(signal.valueType=="DOUBLE"){
                   RetStr+=VariableName+"="+QString::number(static_cast<double>(signal.value.DOUBLE),'f',1);
                   if(i<ListWarnRuleStr.count()-1) RetStr+=",";
               }
             }
    }
    return RetStr;
}

//获取规则相关变量的当前值用于显示
QString RulePool::GetRelatedParaValStr(QString RuleStr)
{
    QString RetStr="";
    for (int i = 0; i <= RuleStr.count(); ++i) {

        //若当前字符为变量名称
        if(RuleStr[i]=='['){
            QString VariableName = "";

            i++;//跳过“[”字符
            if(i>=RuleStr.count()) break;
            //获取变量名称
            while(RuleStr[i]!=']'){
                if(RuleStr[i]!=' ')
                    VariableName.append(RuleStr[i]);
                i++;
            }

            i++;//跳过“]”字符
            if(i>=RuleStr.count()) break;

            //[]内可能是true或false关键字
            if((VariableName == "true")||(VariableName == "false")){
                continue;
            }
            //判断变量池是否含有该变量，若不存在该变量则返回false
            if(m_RuleVariablePool.isContainVariable(VariableName))
            {
               //获取该变量信息
               DataBase::Signal signal = m_RuleVariablePool.GetVariable(VariableName);
               if(signal.valueType=="INT"){
                   RetStr+="["+VariableName+"]"+":"+QString::number(static_cast<double>(signal.value.INT))+";";
               }
               if(signal.valueType=="ENUM"){
                   RetStr+="["+VariableName+"]"+":"+QString::number(static_cast<double>(signal.value.ENUM))+";";
               }
               if(signal.valueType=="BOOL"){
                   RetStr+="["+VariableName+"]"+":"+QString::number(static_cast<double>(signal.value.BOOL?1:0))+";";
               }
               if(signal.valueType=="DOUBLE"){
                   RetStr+="["+VariableName+"]"+":"+QString::number(static_cast<double>(signal.value.DOUBLE),'f',1)+";";
               }
             }
         }
    }
    return RetStr;
}

void RulePool::StartRuleDetection(RuleVariablePool &VariablePool)
{//语句包括 [Variable]=1.0;[Variable1]>[Variabl2];[Variable1]-[Variable2]>0;[Variable]=[true];符号包括+-*/

    static int AutoSaveNum=0;
    //本轮更新的规则数
    int UpdateRuleNum = 0;

    do{
        //初始化本轮更新的规则数为0
        UpdateRuleNum = 0;

        //遍历所有规则信息，执行检测
        for(int i=0;i<m_rules.size();i++){

            //若规则被使用过，则跳过
            if(m_rulesIsUsed[i]!=-1){
                //qDebug()<<"规则"<<i<<":m_rulesIsUsed="<<m_rulesIsUsed[i];
                continue;
            }

            //判断规则条件是否成立

            //将所有条件信息分割
            QStringList ConditionList = m_rules[i].Condition.split(';', QString::SkipEmptyParts);

            //qDebug()<<endl<<"判断规则: "<<ConditionList;

            //规则是否生效变量,初始化为1,1代表规则生效，0代表规则不生效，-1代表规则有信号值还未定
            int RuleEffect = 1;

            //遍历该规则所有条件，查询是否满足
            for(auto cur:ConditionList){

                //将分割条件语句分割成左边和右边
                QStringList splitlist;
                if(cur.contains("<=")){
                    splitlist = cur.split("<=", QString::SkipEmptyParts);
                }
                else if(cur.contains(">=")){
                    splitlist = cur.split(">=", QString::SkipEmptyParts);
                }
                else if(cur.contains("<")){
                    splitlist = cur.split("<", QString::SkipEmptyParts);
                }
                else if(cur.contains(">")){
                    splitlist = cur.split(">", QString::SkipEmptyParts);
                }
                else if(cur.contains("=")){
                    splitlist = cur.split("=", QString::SkipEmptyParts);
                }
                else{
                    qDebug()<<"语句错误"<<cur; {RuleEffect = -1;break;}
                }
                //条件应被分割成左右两部分，若个数不为2则格式错误
                if(splitlist.size()!=2){
                    qDebug()<<"语句错误"<<cur; {RuleEffect = -1;break;}
                }

                //分别计算左右表达式并比较结果
                double left=0,right=0;

                //RuleEffect = -1;//测试
                //break;//测试
                //如果calculate返回值为false则代表有信号值未确定或有信号值在变量池不存在，则设置该规则为未检测并跳过该规则其他条件检测
                if((!calculate(splitlist[0],VariablePool,left))||(!calculate(splitlist[1],VariablePool,right))){
                    RuleEffect = -1;
                    break;
                }
                else{
                    //qDebug()<<"left"<<left;
                    //qDebug()<<"right"<<right;
                    if(cur.contains("<=")){
                        if(!(right-left>=Epslion))  RuleEffect = 0;
                    }
                    else if(cur.contains(">=")){
                        if(!(left-right>=Epslion))  RuleEffect = 0;
                    }
                    else if(cur.contains("<")){
                        if(!(right-left>Epslion))  RuleEffect = 0;
                    }
                    else if(cur.contains(">")){
                        if(!(left-right>Epslion))  RuleEffect = 0;
                    }
                    else if(cur.contains("=")){
                        //qDebug()<<"=判断"<<abs(right-left);
                        if(!(abs(right-left)<Epslion))  RuleEffect = 0;
                    }
                    else{
                        qDebug()<<"语句错误"<<cur;  {RuleEffect = -1;break;}
                    }
                    //qDebug()<<"规则"<<i<<":RuleEffect="<<RuleEffect;
                }
            }

            //更新该规则是否使用
            m_rulesIsUsed[i] = RuleEffect;

            //若RuleEffect为-1,则代表有信号值未确定或有信号值在变量池不存在
            if(RuleEffect==-1){
                //qDebug()<<"信号未定";
            }
            //若RuleEffect==0或1,则代表该规则被判定出结果，执行结果变量更新
            else if(RuleEffect==0||RuleEffect==1){

                //本轮更新的规则数增加1
                UpdateRuleNum++;

                //接下来更新规则结果里面的变量信息
                QStringList ResultList;
                //如果规则成立，那么需要更新ResultThen语句里面的变量,将语句所有赋值信息分割
                if(RuleEffect==1){
                    //满足保持时间要求后进行变量赋值 单位200ms 后续应解决延时不准的问题
                    //qDebug()<<"m_ruleLastState="<<m_ruleLastState[i]<<"DurTime="<<m_RuleDurTime[i];
                    if(m_ruleLastState[i]>0) m_RuleDurTime[i]++;
                    if(m_RuleDurTime[i]>=m_rules[i].DurTime*5)
                    {
                      //qDebug()<<endl<<"规则成立";
                      ResultList = m_rules[i].ResultThen.split(';', QString::SkipEmptyParts);
                    }
                    else
                    {
                        //qDebug()<<endl<<"规则不成立";
                        ResultList = m_rules[i].ResultElse.split(';', QString::SkipEmptyParts);
                    }
                }
                //如果规则不成立，那么需要更新ResultElse语句里面的变量,将语句所有赋值信息分割
                else{
                    m_RuleDurTime[i]=0;
                    //qDebug()<<endl<<"规则不成立";
                    ResultList = m_rules[i].ResultElse.split(';', QString::SkipEmptyParts);
                }
                m_ruleLastState[i]=RuleEffect;
                //qDebug()<<"ResultList: "<<ResultList;

                //遍历所有赋值语句，进行变量赋值
                for(auto result:ResultList){
                      if(!ParsingAndAssigningResultingStatement(result,VariablePool))  break;
                }

            }
            //若RuleEffect为-1,0,1以外的值，则此时程序出现异常，退出检测
            else{
                qDebug()<<"RuleEffect值异常";
                continue;
            }
        }
       //qDebug()<<"UpdateRuleNum="<<UpdateRuleNum;
    }while(UpdateRuleNum);

    //预警诊断，查看是否有匹配的工况
    //遍历所有规则信息，执行检测
    for(int i=0;i<m_Warnrules.size();i++){
        bool FlagWarnning=false;
        bool WarnValid=true;
        QStringList ListTaskPara=m_Warnrules.at(i).TaskParaList.split(",");
        for(int j=0;j<ListTaskPara.count();j++)
        {
            QString VariableName=ListTaskPara.at(j).split("=").at(0);
            QString StrVariableVal,StrThresholdVal;
            double VariableVal,ThresholdVal;
            StrVariableVal=ListTaskPara.at(j).split("=").at(1);
            if(ListTaskPara.at(j).split("=").at(1).contains("(")&&ListTaskPara.at(j).split("=").at(1).contains(")"))
            {
                StrVariableVal=ListTaskPara.at(j).split("=").at(1).mid(0,ListTaskPara.at(j).split("=").at(1).lastIndexOf("("));
                StrThresholdVal=ListTaskPara.at(j).split("=").at(1).mid(ListTaskPara.at(j).split("=").at(1).lastIndexOf("(")+1,ListTaskPara.at(j).split("=").at(1).lastIndexOf(")")-ListTaskPara.at(j).split("=").at(1).lastIndexOf("(")-1);
            }
            if((StrVariableVal=="true")||(StrVariableVal=="TRUE")) VariableVal=1;
            else if((StrVariableVal=="false")||(StrVariableVal=="FALSE")) VariableVal=0;
            else VariableVal=StrVariableVal.toDouble();

            if((StrThresholdVal=="true")||(StrThresholdVal=="TRUE")) ThresholdVal=1;
            else if((StrThresholdVal=="false")||(StrThresholdVal=="FALSE")) ThresholdVal=0;
            else if(StrThresholdVal!="")ThresholdVal=StrThresholdVal.toDouble();
            else ThresholdVal=0;

            if(VariablePool.isContainVariable(VariableName)){
                DataBase::Signal signal = VariablePool.GetVariable(VariableName);
                if(signal.isChecked==false){
                    WarnValid= false;
                    break;
                }
                if(signal.valueType=="INT"){
                    if(fabs(static_cast<double>(signal.value.INT)-VariableVal)>ThresholdVal)
                    {
                        WarnValid= false;
                        break;
                    }
                }
                else if(signal.valueType=="ENUM"){
                    //num = static_cast<double>(signal.value.ENUM);
                    if(fabs(static_cast<double>(signal.value.ENUM)-VariableVal)>ThresholdVal)
                    {
                        WarnValid= false;
                        break;
                    }
                }
                else if(signal.valueType=="BOOL"){
                    //num = static_cast<double>(signal.value.BOOL?1:0);
                    if(fabs(static_cast<double>(signal.value.BOOL?1:0)-VariableVal)>ThresholdVal)
                    {
                        WarnValid= false;
                        break;
                    }
                }
                else if(signal.valueType=="DOUBLE"){
                    //num = static_cast<double>(signal.value.DOUBLE);
                    if(fabs(static_cast<double>(signal.value.DOUBLE)-VariableVal)>ThresholdVal)
                    {
                        WarnValid= false;
                        break;
                    }
                }
            }//end of if(VariablePool.isContainVariable(VariableName))
        }//end of for(int j=0;j<ListTaskPara.count();j++)
        QString TaskPara,WarnPara,StrWarnningInfo;
        if(WarnValid)//工况匹配，查看预警参数
        {
            TaskPara=GetParaStrWithoutValue(m_Warnrules[i].TaskParaList);
            WarnPara=GetParaStrWithoutValue(m_Warnrules[i].WarnParaList);
            StrWarnningInfo=m_Warnrules.at(i).Name+":"+m_RulePool.GetRelatedWarnParaValStr(TaskPara)+";"+m_RulePool.GetRelatedWarnParaValStr(WarnPara);

            //存储工况参数到数据库
            AutoSaveNum++;
            if(AutoSaveNum>=5*60)//1分钟记录1次
            {
                AutoSaveNum=0;
                m_Database->TaskDataSave(StrWarnningInfo);
            }

            QStringList ListWarnPara=m_Warnrules.at(i).WarnParaList.split(",");
            for(int j=0;j<ListWarnPara.count();j++)
            {
                QString VariableName=ListWarnPara.at(j).split("=").at(0);
                QString StrVariableVal,StrThresholdVal;
                double VariableVal,ThresholdVal;
                StrVariableVal=ListWarnPara.at(j).split("=").at(1);
                if(ListWarnPara.at(j).split("=").at(1).contains("(")&&ListWarnPara.at(j).split("=").at(1).contains(")"))
                {
                    StrVariableVal=ListWarnPara.at(j).split("=").at(1).mid(0,ListWarnPara.at(j).split("=").at(1).lastIndexOf("("));
                    StrThresholdVal=ListWarnPara.at(j).split("=").at(1).mid(ListWarnPara.at(j).split("=").at(1).lastIndexOf("(")+1,ListWarnPara.at(j).split("=").at(1).lastIndexOf(")")-ListWarnPara.at(j).split("=").at(1).lastIndexOf("(")-1);
                }
                if((StrVariableVal=="true")||(StrVariableVal=="TRUE")) VariableVal=1;
                else if((StrVariableVal=="false")||(StrVariableVal=="FALSE")) VariableVal=0;
                else VariableVal=StrVariableVal.toDouble();

                if((StrThresholdVal=="true")||(StrThresholdVal=="TRUE")) ThresholdVal=1;
                else if((StrThresholdVal=="false")||(StrThresholdVal=="FALSE")) ThresholdVal=0;
                else if(StrThresholdVal!="")ThresholdVal=StrThresholdVal.toDouble();
                else ThresholdVal=0;

                if(VariablePool.isContainVariable(VariableName)){
                    DataBase::Signal signal = VariablePool.GetVariable(VariableName);
                    if(signal.isChecked==false){
                        FlagWarnning= false;
                        break;
                    }
                    if(signal.valueType=="INT"){
                        if(fabs(static_cast<double>(signal.value.INT)-VariableVal)>ThresholdVal)
                        {
                            FlagWarnning= true;
                            break;
                        }
                    }
                    else if(signal.valueType=="ENUM"){
                        //num = static_cast<double>(signal.value.ENUM);
                        if(fabs(static_cast<double>(signal.value.ENUM)-VariableVal)>ThresholdVal)
                        {
                            FlagWarnning= true;
                            break;
                        }
                    }
                    else if(signal.valueType=="BOOL"){
                        //num = static_cast<double>(signal.value.BOOL?1:0);
                        if(fabs(static_cast<double>(signal.value.BOOL?1:0)-VariableVal)>ThresholdVal)
                        {
                            FlagWarnning= true;
                            break;
                        }
                    }
                    else if(signal.valueType=="DOUBLE"){
                        //num = static_cast<double>(signal.value.DOUBLE);
                        if(fabs(static_cast<double>(signal.value.DOUBLE)-VariableVal)>ThresholdVal)
                        {
                            FlagWarnning= true;
                            break;
                        }
                    }
                }//end of if(VariablePool.isContainVariable(VariableName))
            }//end of for(int j=0;j<ListTaskPara.count();j++)
        }//end of if(WarnValid)//工况匹配，查看预警参数

        bool WarnningExisted=false;
        int WarnningIndex;
        for(int j=0;j<ListWarnningInfo.count();j++)//工况:参数1=值,参数2=值;参数1=值,参数2=值
        {
            if(ListWarnningInfo.at(j).split(":").at(0)==m_Warnrules.at(i).Name)
            {
                WarnningExisted=true;
                WarnningIndex=j;
                break;
            }
        }

        if(FlagWarnning)//如果预警则添加到列表中并增加数据库历史记录，反之则将预警从列表中删除
        {        
            if(WarnningExisted)  ListWarnningInfo[WarnningIndex]=StrWarnningInfo;
            else
            {
                ListWarnningInfo.append(StrWarnningInfo);
                m_Database->InsertWarnToWarnRecord(StrWarnningInfo);
                m_Database->TaskDataSave(StrWarnningInfo);
            }
        }
        else
        {
            if(WarnningExisted)
            {
                ListWarnningInfo.removeAt(WarnningIndex);
                m_Database->UpdateWarnToWarnRecord(m_Warnrules.at(i).Name);
            }
        }
    }//end of for(int i=0;i<m_Warnrules.size();i++){
}

bool RulePool::calculate(QString expression,RuleVariablePool &VariablePool,double &ans)
{//解析字符计算公式,通过ans返回值，解析失败返回false,该程序为一个基本计算器子程序,具体算法思想参考leetcode基本计算器
    //[Variable];[Variable1]+1;[Variable1]-[Variable2];[true];

    //qDebug()<<"expression"<<expression;
    QVector<double> stk;//通过stk存储变量值
    QChar preSign = '+';
    QString NumString = "";
    int LastAbsPos=-1;
    double tmpnum=0;
    double num = 0;
    int n = expression.length();
    for (int i = 0; i <= n; ++i) {

        //若当前字符为变量名称
        if(i<n&&expression[i]=='['){
            QString VariableName = "";

            i++;//跳过“[”字符

            //获取变量名称
            while(i<n&&expression[i]!=']'){
                if(expression[i]!=' ')
                    VariableName.append(expression[i]);
                i++;
            }

            i++;//跳过“]”字符

            //[]内可能是true或false关键字
            //若为true则值为1
            if(VariableName == "true"){
                num = 1;
            }
            //若为false则值为0
            else if(VariableName == "false"){
                num = 0;
            }
            //否则为变量,解析变量是否被初始化并获取其值
            else{
                //判断变量池是否含有该变量，若不存在该变量则返回false
                if(VariablePool.isContainVariable(VariableName)){
                    //获取该变量信息
                    DataBase::Signal signal = VariablePool.GetVariable(VariableName);
                    //如果变量还未初始化，返回false
                    if(signal.isChecked==false){
                        return false;
                    }
                    //否则根据变量的类型给变量赋值
                    else{
                        if(signal.valueType=="INT"){
                            num = static_cast<double>(signal.value.INT);
                            //qDebug()<<"INT";
                        }
                        if(signal.valueType=="ENUM"){
                            num = static_cast<double>(signal.value.ENUM);
                            //qDebug()<<"ENUM";
                        }
                        if(signal.valueType=="BOOL"){
                            num = static_cast<double>(signal.value.BOOL?1:0);
                            //qDebug()<<"BOOL";
                        }
                        if(signal.valueType=="DOUBLE"){
                            num = static_cast<double>(signal.value.DOUBLE);
                            //qDebug()<<"DOUBLE";
                        }
                    }
                }
                //若不存在该变量则返回false
                else{
                    return false;
                }
            }
            //qDebug()<<"Variable"<<num;
        }

        //若为数值则转化为数值
        if(i<n&&((expression[i]>='0'&&expression[i]<='9')||(expression[i]=='.'))){
            NumString.append(expression[i]);
            num = NumString.toDouble();
            //qDebug()<<"NumString"<<NumString<<num;
            //i++;
        }

        bool AddFlag=true;
        //若为末尾或为运算符,则将之前的num数值加入到stack
        if(i>=n||expression[i]=='+'||expression[i]=='-'||expression[i]=='*'||expression[i]=='/'||expression[i]=='|'){
            //添加数值到容器中
            if((expression[i]=='|')&&(LastAbsPos<0)) AddFlag=false;
            if(AddFlag)
            {
                if(preSign=='+'){
                    stk.push_back(num);
                }
                else if(preSign=='-'){
                    stk.push_back(-num);
                }
                else if(preSign=='*'){
                    stk.back() *= num;
                }
                else if(preSign=='/'){
                    stk.back() /= num;
                }
                preSign = expression[i];
            }

            if(expression[i]=='|'){
                if(LastAbsPos>-1){
                    for(int j=LastAbsPos;j<stk.length();j++) {
                        tmpnum+=stk[j];
                    }
                    if(tmpnum<0)
                        for(int j=LastAbsPos;j<stk.length();j++) {
                            stk[j]*=-1;
                        }
                    LastAbsPos=-1;
                }
                else   LastAbsPos=stk.length();
            }

            NumString.clear();
            num = 0;
        }       
    }
    //计算stack内的和即为结果

    for(auto m:stk){
        //qDebug()<<"stk"<<m;
    }
    ans =  std::accumulate(stk.begin(), stk.end(), 0.0);

    //qDebug()<<"ans"<<ans<<endl;
    return true;
}

bool RulePool::ParsingAndAssigningResultingStatement(QString expression, RuleVariablePool &VariablePool)
{//结果语句只能是赋值语句,如[Variable]=1.0;[Variable1]=[Variabl2];[Variable1]=[true]

    //将表达式分割为左右部分
    QStringList List = expression.split('=', QString::SkipEmptyParts);
    if(List.size()!=2){
        return false;
    }

    //左边一定为变量名称
    QString LeftVariableName;
    if(List[0].startsWith("[")&&List[0].endsWith("]")){
        LeftVariableName = List[0];
        LeftVariableName.remove("[").remove("]").remove(" ");
        //若变量池不包含该变量，则输出异常
        if(!VariablePool.isContainVariable(LeftVariableName)){
            return false;
        }
    }
    else{
        return false;
    }

   // qDebug()<<"左变量"<<LeftVariableName;

    //右边可以为变量名称也可以为值
    double num = 0;
    if(List[1].startsWith("[")&&List[1].endsWith("]")){
        QString RightVariableName = List[1];
        RightVariableName = RightVariableName.remove("[").remove("]").remove(" ");

        //qDebug()<<"右变量"<<RightVariableName;

        if(RightVariableName == "true"){
            num = 1;
        }

        else if(RightVariableName == "false"){
            num = 0;
        }
        else{
            //若变量池不包含该变量，则输出异常
            if(!VariablePool.isContainVariable(RightVariableName)){
                return false;
            }
            else{
                DataBase::Signal signal = VariablePool.GetVariable(RightVariableName);
                if(signal.isChecked==false){
                    return true;
                }
                else{
                    if(signal.valueType=="INT"){
                        num = static_cast<double>(signal.value.INT);
                    }
                    if(signal.valueType=="ENUM"){
                        num = static_cast<double>(signal.value.ENUM);
                    }
                    if(signal.valueType=="BOOL"){
                        num = static_cast<double>(signal.value.BOOL?0:1);
                    }
                    if(signal.valueType=="DOUBLE"){
                        num = static_cast<double>(signal.value.DOUBLE);
                    }
                }
            }
        }
    }
    else{
        QString NumString = List[1].remove(" ");
        num = NumString.toDouble();
    }

    //qDebug()<<"右值"<<num;


    //给变量赋值
    DataBase::Signal signal = VariablePool.GetVariable(LeftVariableName);

    if(signal.valueType=="INT"){
        VariablePool.SetVariableValue(LeftVariableName,static_cast<int>(num));
    }
    if(signal.valueType=="ENUM"){
        VariablePool.SetVariableValue(LeftVariableName,static_cast<int>(num));
    }
    if(signal.valueType=="BOOL"){
        VariablePool.SetVariableValue(LeftVariableName,static_cast<bool>(num));

    }
    if(signal.valueType=="DOUBLE"){
        VariablePool.SetVariableValue(LeftVariableName,static_cast<double>(num));
    }

    return true;
}
