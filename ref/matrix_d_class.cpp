#include "matrix_d_class.h"
#include  <QtDebug>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0

#pragma execution_character_set("utf-8")
#endif

//初始化测试偏好集
void Matrix_D_class::now_time()
{
    QDateTime time = QDateTime::currentDateTime();
    QString str = time.toString("yyyy-MM-dd hh:mm:ss dddd");
    //qDebug()<<str;
}

void Matrix_D_class::init_test_preference_message(QString selected_model)
{
    sql_prepare = QString("SELECT TEST_COST_PREFERENCE,TEST_LEVEL_PREFERENCE,TEST_TIME_PREFERENCE,FAULT_PROBABILITY_PREFERENCE "
                          "FROM MODELS WHERE MODEL_NAME = '%1';").arg(selected_model);
    //查找TMATE数据库模型测试偏好集
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.ThisPreferData.TEST_COST_prefer = qsQuery_TMATE_MDB.value(0).toInt();
        Matrix_D.ThisPreferData.TEST_LEVEL_prefer = qsQuery_TMATE_MDB.value(1).toInt();
        Matrix_D.ThisPreferData.TEST_TIME_prefer = qsQuery_TMATE_MDB.value(2).toInt();
        Matrix_D.ThisPreferData.FAULT_PROBABLITY_prefer = qsQuery_TMATE_MDB.value(3).toInt();
    }
}

//初始化最底层模块集除故障先验概率外所有信息
void Matrix_D_class::init_the_lowest_module_message(QString selected_model)
{
    //清空最底层模块集
    Matrix_D.list_LOWEST_MODULE_DATA.clear();

    //查询MODULE_TID,MODULE_NAME,MTTF
    sql_prepare = QString("SELECT MODULE_TID,MODULE_NAME,MTTF,REPAIR_NOTES FROM MODULE_PROPS "
                          "WHERE IS_LOWEST_HIERARCHY = 1 AND MODEL_NAME = '%1';").arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.OneModuleData.MODULE_TID = qsQuery_TMATE_MDB.value(0).toString();
        Matrix_D.OneModuleData.MODULE_NAME = qsQuery_TMATE_MDB.value(1).toString();
        Matrix_D.OneModuleData.MODULE_MTTF = qsQuery_TMATE_MDB.value(2).toDouble();
        Matrix_D.OneModuleData.REPAIR_NOTES = qsQuery_TMATE_MDB.value(3).toString();
        Matrix_D.OneModuleData.sign_module = true;
        Matrix_D.list_LOWEST_MODULE_DATA.append(Matrix_D.OneModuleData);
    }

    //获取信号集
    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
    {
        sql_prepare = QString("SELECT SIGNAL_NAME FROM MODULE_SIGNALS "
                              "WHERE MODULE_TID = '%1' AND MODEL_NAME = '%2';")
                .arg(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_TID).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.append(qsQuery_TMATE_MDB.value(0).toString());
        }
    }
}

//初始化目前使能模块的故障先验概率
void Matrix_D_class::init_the_fault_probablity_message()
{
    //计算目前使能模块的MTTF总和
    double sum_MTTF = 0;
    for(int i=0;i<list_LOWEST_MODULE_DATA.size();i++)
    {
        if(list_LOWEST_MODULE_DATA[i].sign_module)
            sum_MTTF += list_LOWEST_MODULE_DATA[i].MODULE_MTTF;
    }

    //计算目前使能模块的MTTF平均值
    double average_MTTF = sum_MTTF/list_LOWEST_MODULE_DATA.size();

    //计算目前使能模块转置后的MTTF总和
    double sum_transed_MTTF = 0;
    for(int i=0;i<list_LOWEST_MODULE_DATA.size();i++)
    {
        if(list_LOWEST_MODULE_DATA[i].sign_module)
        {
            double transed_MTTF = average_MTTF/list_LOWEST_MODULE_DATA[i].MODULE_MTTF;
            sum_transed_MTTF += transed_MTTF;
        }
    }

    //计算目前使能模块的故障先验概率
    for(int i=0;i<list_LOWEST_MODULE_DATA.size();i++)
    {
        if(list_LOWEST_MODULE_DATA[i].sign_module)
            list_LOWEST_MODULE_DATA[i].FAULT_PROBABLITY = (average_MTTF/list_LOWEST_MODULE_DATA[i].MODULE_MTTF)/sum_transed_MTTF;
    }
}

//初始化测试与征兆集
void Matrix_D_class::init_the_test_message(QString selected_model)
{
    //qDebug()<<"init_the_test_message";
    //now_time();
    //清空测试与征兆集
    Matrix_D.list_TEST_DATA.clear();
    //查找TMATE数据库TEST_PROPS表所有测试信息
    sql_prepare = QString("SELECT TEST_TID,TEST_NAME,TEST_LEVEL,TEST_COST,TEST_TIME,"
                          "DESCRIPTION,TEST_PROCEDURE,TEST_TYPE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                          "FROM TEST_PROPS WHERE MODEL_NAME = '%1';").arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.OneTestData.sign_test = true;
        Matrix_D.OneTestData.TEST_TID = qsQuery_TMATE_MDB.value(0).toString();
        Matrix_D.OneTestData.TEST_NAME = qsQuery_TMATE_MDB.value(1).toString();
        Matrix_D.OneTestData.TEST_LEVEL = qsQuery_TMATE_MDB.value(2).toDouble();
        Matrix_D.OneTestData.TEST_COST = qsQuery_TMATE_MDB.value(3).toDouble();
        Matrix_D.OneTestData.TEST_TIME = qsQuery_TMATE_MDB.value(4).toDouble();
        Matrix_D.OneTestData.DESCRIPTION = qsQuery_TMATE_MDB.value(5).toString();
        Matrix_D.OneTestData.TEST_PROCEDURE = qsQuery_TMATE_MDB.value(6).toString();
        Matrix_D.OneTestData.TEST_TYPE = qsQuery_TMATE_MDB.value(7).toInt();
        Matrix_D.OneTestData.TEST_SIGNAL_IS_EXIT_OR_NOT = qsQuery_TMATE_MDB.value(8).toInt();
        Matrix_D.list_TEST_DATA.append(Matrix_D.OneTestData);
    }

    //now_time();
    //查找TMATE数据库TEST_RESOURCES表所有测试所需资源信息
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        sql_prepare = QString("SELECT RESOURCE_NAME FROM TEST_RESOURCES "
                              "WHERE TEST_NAME = '%1' AND MODEL_NAME = '%2';").arg(Matrix_D.list_TEST_DATA[i].TEST_NAME).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            Matrix_D.list_TEST_DATA[i].need_tools.append(qsQuery_TMATE_MDB.value(0).toString());
        }
    }

    //now_time();
    //查找TMATE数据库TESTS_IN_TEST_POINT表所有测试与测试点TID关系信息
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        sql_prepare = QString("SELECT TP_TID,TP_CONNECTED_MODULE_TID FROM TESTS_IN_TEST_POINT WHERE TEST_TID = '%1' AND MODEL_NAME = '%2';")
                .arg(Matrix_D.list_TEST_DATA[i].TEST_TID).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            Matrix_D.list_TEST_DATA[i].TEST_POINT_TID = qsQuery_TMATE_MDB.value(0).toString();
            Matrix_D.list_TEST_DATA[i].Connected_module_TID =  qsQuery_TMATE_MDB.value(1).toString();
        }
    }

    //查找TMATE数据库测试所属测试点连接的模块TID
//    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
//    {
//        Matrix_D.list_TEST_DATA[i].Connected_module_TID = select_test_connected_module(Matrix_D.list_TEST_DATA[i].TEST_POINT_TID,selected_model);
//    }

    //now_time();
    //查找TMATE数据库TESTS_IN_TEST_POINT表所有测试与测试点名称关系信息
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        sql_prepare = QString("SELECT TEST_POINT_NAME FROM TEST_POINTS WHERE TP_TID = '%1' AND MODEL_NAME = '%2';")
                .arg(Matrix_D.list_TEST_DATA[i].TEST_POINT_TID).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            Matrix_D.list_TEST_DATA[i].TEST_POINT_NAME = qsQuery_TMATE_MDB.value(0).toString();
        }
    }

    //now_time();
    //查找TMATE数据库TEST_OUTCOME_SIGNALS表所有测试输出信号信息
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        sql_prepare = QString("SELECT SIGNAL_NAME FROM TEST_OUTCOME_SIGNALS WHERE TEST_TID = '%1' AND MODEL_NAME = '%2';")
                .arg(Matrix_D.list_TEST_DATA[i].TEST_TID).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            Matrix_D.list_TEST_DATA[i].list_signals.append(qsQuery_TMATE_MDB.value(0).toString());
        }
    }
    //now_time();
    //qDebug()<<"init_the_test_message";
}

//解析D矩阵
void Matrix_D_class::read_the_D_Matrix(QString selected_model)
{
    Matrix_D.Matrix_D_value.clear();

    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        sql_prepare = QString("SELECT D_VALUE FROM MATRIX_D_AND_TEST_MARK WHERE TEST_TID = '%1' AND MODEL_NAME = '%2';")
                .arg(Matrix_D.list_TEST_DATA[i].TEST_TID).arg(selected_model);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            QString MDB_VALUE = qsQuery_TMATE_MDB.value(0).toString();
            QList<int> OneRowDvalue = trans_16to2(MDB_VALUE,Matrix_D.list_LOWEST_MODULE_DATA.size());
            Matrix_D.Matrix_D_value.append(OneRowDvalue);
        }
    }
}

//D矩阵解析转换函数
QList<int> Matrix_D_class::trans_16to2(QString string,int Num_List)
{
    QList<int> list;
    int n = string.size();

    for(int i=0;i<n;i++)
    {
        char now_char = string[i].unicode();
        if(now_char>='A'&&now_char<='F')
        {
            int a=static_cast<int>(now_char-'A'+10);
            switch(a)
            {
            case 10:list.append(1);list.append(0);list.append(1);list.append(0);break;
            case 11:list.append(1);list.append(0);list.append(1);list.append(1);break;
            case 12:list.append(1);list.append(1);list.append(0);list.append(0);break;
            case 13:list.append(1);list.append(1);list.append(0);list.append(1);break;
            case 14:list.append(1);list.append(1);list.append(1);list.append(0);break;
            case 15:list.append(1);list.append(1);list.append(1);list.append(1);break;
            }
        }
        else if(isdigit(now_char))
        {
            int b=static_cast<int>(now_char-'0');
            switch(b)
            {
            case 0:list.append(0);list.append(0);list.append(0);list.append(0);break;
            case 1:list.append(0);list.append(0);list.append(0);list.append(1);break;
            case 2:list.append(0);list.append(0);list.append(1);list.append(0);break;
            case 3:list.append(0);list.append(0);list.append(1);list.append(1);break;
            case 4:list.append(0);list.append(1);list.append(0);list.append(0);break;
            case 5:list.append(0);list.append(1);list.append(0);list.append(1);break;
            case 6:list.append(0);list.append(1);list.append(1);list.append(0);break;
            case 7:list.append(0);list.append(1);list.append(1);list.append(1);break;
            case 8:list.append(1);list.append(0);list.append(0);list.append(0);break;
            case 9:list.append(1);list.append(0);list.append(0);list.append(1);break;
            }
        }
    }

    QList<int> result_list;
    for(int i=0;i<Num_List;i++)
    {
        result_list.append(list[i]);
    }
    return result_list;
}

//初始化可用工具集
void Matrix_D_class::init_the_tool_message(QString selected_model)
{
    //清零可使用工具集
    Matrix_D.list_Tool_DATA.clear();
    Matrix_D.diagnostic_record.list_tool.clear();
    //查找TMATE数据库MODEL_RESOURCES表可用工具集
    sql_prepare = QString("SELECT RESOURCE_NAME FROM MODEL_RESOURCES WHERE AVAILABLE = TRUE AND MODEL_NAME = '%1';").arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.list_Tool_DATA.append(qsQuery_TMATE_MDB.value(0).toString());
        Matrix_D.diagnostic_record.list_tool.append(qsQuery_TMATE_MDB.value(0).toString());
    }
}

//初始化条件D矩阵(即考虑已发现现象、测试工具等条件的D矩阵)
void Matrix_D_class::init_condition_D_matrix()
{
    //矩阵列标志变量置为false,默认所有模块都不保留
    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
        Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module = false;

    //矩阵行标志变量置为true,默认所有测试均可用
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
        Matrix_D.list_TEST_DATA[i].sign_test = true;

    //基于测试工具简化D矩阵
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        //若测试需要工具，检测工具是否存在
        if(Matrix_D.list_TEST_DATA[i].need_tools.size())
        {
            //对每一个工具和工具库对比
            for(int j=0;j<Matrix_D.list_TEST_DATA[i].need_tools.size();j++)
            {
                if(!Matrix_D.list_Tool_DATA.contains(Matrix_D.list_TEST_DATA[i].need_tools[j]))
                {
                    Matrix_D.list_TEST_DATA[i].sign_test = false;
                }
            }
        }
    }



    //基于对测试和征兆的选择简化D矩阵
    //当前项为测试且测试异常或项为征兆且征兆存在,相关信号需要保留,该测试需要删除
    bool Have_test_abnormal_or_symptom_exit = false;
    Matrix_D.diagnostic_record.fault_phenomenon = "";
    Matrix_D.diagnostic_record.advance_omen_test = "";
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT==0)
            {
                Matrix_D.diagnostic_record.advance_omen_test.append(Matrix_D.list_TEST_DATA[i].TEST_NAME);
                Matrix_D.diagnostic_record.advance_omen_test.append(";");

                QString test_procedure = Matrix_D.list_TEST_DATA[i].TEST_PROCEDURE;
                test_procedure.remove(" ").remove("<DIV>").remove("</DIV>").remove("\r").remove("\n");
                if(test_procedure != nullptr)
                {
                    Matrix_D.diagnostic_record.fault_phenomenon.append(Matrix_D.list_TEST_DATA[i].TEST_PROCEDURE);
                    Matrix_D.diagnostic_record.fault_phenomenon.append(",不正常;");
                }
                Have_test_abnormal_or_symptom_exit = true;
                Matrix_D.list_TEST_DATA[i].sign_test = false;
                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
                {
                    if(Matrix_D.Matrix_D_value[i][j])
                        Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module = true;
                }
            }
        }
    }

//    for(int i=0;i<list_TEST_DATA.size();i++)
//    {
//        if(list_TEST_DATA[i].TEST_NAME == "T_S11_690V开关电源1-12-G2-t-1S11")
//        {
//            qDebug()<<list_TEST_DATA[i].sign_test;
//            for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
//            {
//                if(Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module)
//                {
//                    qDebug()<<Matrix_D.Matrix_D_value[i][j];
//                }
//            }
//        }
//    }
//        for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
//        {
//            if(Matrix_D.list_TEST_DATA[i].sign_test)
//            {
//                qDebug()<<Matrix_D.list_TEST_DATA[i].TEST_NAME;
//            }
//        }
//        for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
//        {
//            if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
//            {
//                qDebug()<<Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_NAME;
//            }
//        }

    //若没有测试异常或征兆出现，则所有信号需要保留
    if(!Have_test_abnormal_or_symptom_exit)
    {
        for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
            Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module = true;
    }

    //当前项为测试且测试正常或为征兆且征兆不存在,相关最底层模块需要删除,该测试需要删除
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT == 1)
            {
                Matrix_D.list_TEST_DATA[i].sign_test = false;
                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
                {
                    if(Matrix_D.Matrix_D_value[i][j])
                        Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module = false;
                }
            }
        }
    }
    print_out();
}

//删除D矩阵第Num行
void Matrix_D_class::delete_one_test_row(int Num)
{
    Matrix_D.list_TEST_DATA[Num].sign_test = false;
}

//删除D矩阵第Num列
void Matrix_D_class::delete_one_module_Column(int Num)
{
    Matrix_D.list_LOWEST_MODULE_DATA[Num].sign_module = false;
}

//判断当前D矩阵检测是否结束
bool Matrix_D_class::diagnosis_end()
{
    //删除无用测试，即全0行
    for(int i=0;i<list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            bool all_zero = true;
            for(int j=0;j<Matrix_D_value[i].size();j++)
            {
                if(Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module)
                {
                    if(Matrix_D_value[i][j])
                    {
                        all_zero = false;
                    }
                }
            }
            if(all_zero)
                delete_one_test_row(i);
        }
    }

    //删除无用测试，若存在多个全1行，则只需保留一个
    int all_one_line_number = 0;
    for(int i=0;i<list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            bool all_one = true;
            for(int j=0;j<Matrix_D_value[i].size();j++)
            {
                if(Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module)
                {
                    if(!Matrix_D_value[i][j])
                    {
                        all_one = false;
                    }
                }
            }
            if(all_one)
            {
                all_one_line_number++;
                if(all_one_line_number>=2)
                    delete_one_test_row(i);
            }
        }
    }

    print_out();
    bool end = true;//默认检测需要结束
    //若所有测试均已使用,则检测需要结束
    int not_used_test_num = 0;
    for(int i=0;i<list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
           not_used_test_num++;
        }
    }
    if(not_used_test_num == 0)
        return end;

    //若还有测试未使用,判断未隔离故障模块个数，若个数小于等于1，则检测需要结束
    int fuzzy_module_num = 0;
    for(int i=0;i<list_LOWEST_MODULE_DATA.size();i++)
    {
        if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
        {
           fuzzy_module_num++;
        }
    }
    if(fuzzy_module_num <= 1)
        return end;

    //若还有测试未使用且未隔离模块数大于1，则检测需要继续
    end = false;
    return end;
}

QString Matrix_D_class::select_a_test_from_now_test_data()//在当前测试库中选择一个测试并返回测试TID
{

    //初始化目前使能模块的故障先验概率
    init_the_fault_probablity_message();

    //初始化可用测试集
    QList<QString> list_can_use_test_TID;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            list_can_use_test_TID.append(Matrix_D.list_TEST_DATA[i].TEST_TID);
        }
    }

    //qDebug()<<"Name";
    //初始化化目前使能测试的信息增益
    QList<double> list_Information_gain_rate;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            double fault_probablity_message = 0;
            double Information_gain_rate = 0;
            for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
            {
                if(Matrix_D.list_LOWEST_MODULE_DATA[j].sign_module)
                {
                    if(Matrix_D_value[i][j])
                    {
                        fault_probablity_message+=list_LOWEST_MODULE_DATA[j].FAULT_PROBABLITY;
                    }
                }
            }
            if(static_cast<int>(fault_probablity_message)==1)
                Information_gain_rate = 1;
            else
                Information_gain_rate = -(fault_probablity_message*log(fault_probablity_message)/log(2)+(1-fault_probablity_message)*log((1-fault_probablity_message))/log(2));
            list_Information_gain_rate.append(Information_gain_rate);
            //qDebug()<<Matrix_D.list_TEST_DATA[i].TEST_NAME;
            //qDebug()<<fault_probablity_message;
            //qDebug()<<Information_gain_rate;
        }
    }

    //qDebug()<<"Information_gain_rate";
    //归一化测试信息增益
    QList<double> list_normal_Information_gain_rate;

    double sum_Information_gain_rate = 0;
    for(int i=0;i<list_Information_gain_rate.size();i++){
        sum_Information_gain_rate+=list_Information_gain_rate[i];}
    //qDebug()<<sum_Information_gain_rate;
    for(int i=0;i<list_Information_gain_rate.size();i++){
        list_normal_Information_gain_rate.append(list_Information_gain_rate[i]/sum_Information_gain_rate);
        //qDebug()<<list_Information_gain_rate[i]/sum_Information_gain_rate;
    }


    //初始化测试总代价
    QList<double> list_Total_test_cost;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
        {
            double Total_test_cost = 0;
            Total_test_cost = ThisPreferData.TEST_COST_prefer*list_TEST_DATA[i].TEST_COST;
            Total_test_cost += ThisPreferData.TEST_LEVEL_prefer*list_TEST_DATA[i].TEST_LEVEL;
            Total_test_cost += ThisPreferData.TEST_TIME_prefer*list_TEST_DATA[i].TEST_TIME;
            list_Total_test_cost.append(Total_test_cost);
        }
    }

    //qDebug()<<"test_cost";
    //归一化测试总代价
    QList<double> list_normal_Total_test_cost;
    int sum_Total_test_cost = 0;
    for(int i=0;i<list_Total_test_cost.size();i++){
        sum_Total_test_cost+=list_Total_test_cost[i];}

    for(int i=0;i<list_Total_test_cost.size();i++){
        list_normal_Total_test_cost.append(list_Total_test_cost[i]/sum_Total_test_cost);
        //qDebug()<<list_Total_test_cost[i]/sum_Total_test_cost;
    }


    //计算信息增益率与测试总代价的最终占比
    double fault_probablity_ratio = ThisPreferData.FAULT_PROBABLITY_prefer;
    double average_total_test_cost_ratio = (ThisPreferData.TEST_COST_prefer+ThisPreferData.TEST_LEVEL_prefer+ThisPreferData.TEST_TIME_prefer)/3.0;
    double sum_total_ratio = average_total_test_cost_ratio + fault_probablity_ratio;

    //计算并选取最大综合增益

    double The_Max_k_value = (fault_probablity_ratio/sum_total_ratio)*list_normal_Information_gain_rate[0]
            - (average_total_test_cost_ratio/sum_total_ratio)*list_normal_Total_test_cost[0];
    int The_Max_k_test_number = 0;

    //qDebug()<<"k";
    for(int i=0;i<list_normal_Information_gain_rate.size();i++)
    {
        double k = (fault_probablity_ratio/sum_total_ratio)*list_normal_Information_gain_rate[i]
                - (average_total_test_cost_ratio/sum_total_ratio)*list_normal_Total_test_cost[i];
        //qDebug()<<k;
        if(The_Max_k_value<k)
        {
            The_Max_k_test_number = i;
            The_Max_k_value = k;
        }
    }

    int TID_NUM = 0;
    for(int i=0;i<list_TEST_DATA.size();i++)
    {
        if(list_TEST_DATA[i].sign_test)
        {
        if(list_TEST_DATA[i].TEST_TID == list_can_use_test_TID[The_Max_k_test_number])
        {
            TID_NUM = i;
            break;
        }
        }
    }

    one_test_cord.Diagnosis_test_name = list_TEST_DATA[TID_NUM].TEST_NAME;
    one_test_cord.recommend_or_self_selected = "推荐测试";
    one_test_cord.yes_or_no = "测试正常";
    diagnostic_record.list_Diagnosis_test_record.append(one_test_cord);

    return list_TEST_DATA[TID_NUM].TEST_TID;
}

//查找当前测试的多媒体信息并存储到多媒体信息表
void Matrix_D_class::select_multimedia_of_this_test(QString selected_model, QString test_TID)
{
    Matrix_D.MULTIMEDIA_List.clear();
    sql_prepare = QString("SELECT FILE_SIZE,CHECKSUM,MEDIA_NAME "
                          "FROM TEST_MEDIA WHERE MODEL_NAME = '%1' AND TID = '%2';").arg(selected_model).arg(test_TID);
    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.MULTIMEDIA.FILE_SIZE = qsQuery_TMATE_MDB.value(0).toInt();
        Matrix_D.MULTIMEDIA.CHECKSUM = qsQuery_TMATE_MDB.value(1).toString();
        Matrix_D.MULTIMEDIA.MEDIA_NAME = qsQuery_TMATE_MDB.value(2).toString();
        Matrix_D.MULTIMEDIA_List.append(Matrix_D.MULTIMEDIA);
    }

    //查找数据库MULTIMEDIA表该模型包含的多媒体资源列表
    for(int i=0;i<Matrix_D.MULTIMEDIA_List.size();i++)
    {
        sql_prepare = QString("SELECT IMAGE_DATA FROM MULTIMEDIA "
                              "WHERE CHECKSUM = '%1' AND FILE_SIZE = %2;")
                .arg(Matrix_D.MULTIMEDIA_List[i].CHECKSUM).arg(Matrix_D.MULTIMEDIA_List[i].FILE_SIZE);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next()){
            Matrix_D.MULTIMEDIA_List[i].IMAGE_DATA = qsQuery_TMATE_MDB.value(0).toByteArray();}
    }
}

//查找当前故障模块的多媒体信息并存储到多媒体信息表
void Matrix_D_class::select_multimedia_of_this_module(QString selected_model, QString module_TID)
{
    Matrix_D.MULTIMEDIA_List.clear();
    sql_prepare = QString("SELECT FILE_SIZE,CHECKSUM,MEDIA_NAME "
                          "FROM MODULE_MEDIA WHERE MODEL_NAME = '%1' AND TID = '%2';").arg(selected_model).arg(module_TID);
    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.MULTIMEDIA.FILE_SIZE = qsQuery_TMATE_MDB.value(0).toInt();
        Matrix_D.MULTIMEDIA.CHECKSUM = qsQuery_TMATE_MDB.value(1).toString();
        Matrix_D.MULTIMEDIA.MEDIA_NAME = qsQuery_TMATE_MDB.value(2).toString();
        Matrix_D.MULTIMEDIA_List.append(Matrix_D.MULTIMEDIA);
    }
    //查找数据库MULTIMEDIA表该模型包含的多媒体资源列表
    for(int i=0;i<Matrix_D.MULTIMEDIA_List.size();i++)
    {
        sql_prepare = QString("SELECT IMAGE_DATA FROM MULTIMEDIA "
                              "WHERE CHECKSUM = '%1' AND FILE_SIZE = %2;")
                .arg(Matrix_D.MULTIMEDIA_List[i].CHECKSUM).arg(Matrix_D.MULTIMEDIA_List[i].FILE_SIZE);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next()){
            Matrix_D.MULTIMEDIA_List[i].IMAGE_DATA = qsQuery_TMATE_MDB.value(0).toByteArray();}
    }
}

void Matrix_D_class::print_out()//测试输出
{
//    //输出
//    int num_test = 0;
//    for(int i=0;i<list_TEST_DATA.size();i++)
//    {
//        if(list_TEST_DATA[i].sign_test){
//            num_test++;
//            qDebug()<<list_TEST_DATA[i].TEST_NAME;
//        }
//    }
//    qDebug()<<num_test;

//    int num_module = 0;
//    for(int i=0;i<list_LOWEST_MODULE_DATA.size();i++)
//    {
//        if(list_LOWEST_MODULE_DATA[i].sign_module)
//        {
//            num_module++;
//            qDebug()<<list_LOWEST_MODULE_DATA[i].MODULE_NAME;
//        }
//    }
//    qDebug()<<num_module;

//    for(int i=0;i<list_TEST_DATA.size();i++)
//    {
//        if(list_TEST_DATA[i].sign_test)
//        {
//            QList<int> line;
//            for(int j=0;j<list_LOWEST_MODULE_DATA.size();j++)
//            {
//                if(list_LOWEST_MODULE_DATA[j].sign_module)
//                    line.append(Matrix_D_value[i][j]);
//            }
//            qDebug()<<line;
//        }
    //    }
}

//通过测试点TID寻找所连接的模块
QString Matrix_D_class::select_test_connected_module(QString targrt_test_point_TID,QString model_name)
{
    //TID父级相关信息
    typedef struct  {
        QString PARENT_TID;//父层级TID
        QString CHILD_TYPE;//该目标属性(仅区分module和point)
        int CHILD_REF_NO;//目标在父模块的编号
        int PORT;
    }StrParentData;

    //查询测试点父模块信息
    StrParentData TP_Data;
    sql_prepare = QString("SELECT PARENT_TID,CHILD_TYPE,CHILD_REF_NO FROM MODEL_HIERARCHY "
                                "WHERE TID = '%1' AND MODEL_NAME = '%2';").arg(targrt_test_point_TID).arg(model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        TP_Data.PARENT_TID = qsQuery_TMATE_MDB.value(0).toString();
        TP_Data.CHILD_TYPE = qsQuery_TMATE_MDB.value(1).toString();
        TP_Data.CHILD_REF_NO = qsQuery_TMATE_MDB.value(2).toInt();
        TP_Data.PORT = 1;
    }

    //查询目标点对应的上一层的父模块信息
    StrParentData Module_Data;
    sql_prepare = QString("SELECT SOURCE_TYPE,SOURCE_REF_NO,SOURCE_PORT FROM DEPENDENCY "
                                "WHERE PARENT_TID = '%1' AND DEST_TYPE = '%2' AND "
                          "DEST_REF_NO = %3 AND DEST_PORT = %4 AND MODEL_NAME = '%5';")
            .arg(TP_Data.PARENT_TID).arg(TP_Data.CHILD_TYPE).arg(TP_Data.CHILD_REF_NO).arg(TP_Data.PORT).arg(model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Module_Data.PARENT_TID = TP_Data.PARENT_TID;
        Module_Data.CHILD_TYPE = qsQuery_TMATE_MDB.value(0).toString();
        Module_Data.CHILD_REF_NO = qsQuery_TMATE_MDB.value(1).toInt();
        Module_Data.PORT = 1;
    }

    //查询上一级模块TID
    QString Module_TID;
    sql_prepare = QString("SELECT TID FROM MODEL_HIERARCHY WHERE PARENT_TID = '%1' AND CHILD_TYPE = '%2' AND CHILD_REF_NO = %3 AND MODEL_NAME = '%4';")
            .arg(Module_Data.PARENT_TID).arg(Module_Data.CHILD_TYPE).arg(Module_Data.CHILD_REF_NO).arg(model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
        Module_TID = qsQuery_TMATE_MDB.value(0).toString();
    return Module_TID;

//    //查询上一级模块TID
//    QString Module_TID;
//    sql_prepare = QString("SELECT TP_CONNECTED_MODULE_TID FROM TESTS_IN_TEST_POINT WHERE TP_TID = '%1' AND MODEL_NAME = '%2';")
//            .arg(targrt_test_point_TID).arg(model_name);
//    qsQuery_TMATE_MDB.exec(sql_prepare);
//    while(qsQuery_TMATE_MDB.next())
//        Module_TID = qsQuery_TMATE_MDB.value(0).toString();
//    return Module_TID;
}

QList<QString> Matrix_D_class::select_module_transitive_telation(QString traget_module_TID, QString model_name)//获取模块传递链
{
    QList<QString> list_parents_TID;//回溯父模块集TID（最后一个为顶层）
    QList<QString> list_parents_NAME;//回溯父模块集（最后一个为顶层）
    //获取模块传递链TID
        list_parents_TID.append(traget_module_TID);
        QString next_parent_TID = nullptr;
        do{
            next_parent_TID = nullptr;
            sql_prepare = QString("SELECT PARENT_TID FROM MODEL_HIERARCHY "
                                  "WHERE TID = '%1' AND MODEL_NAME = '%2';")
                    .arg(list_parents_TID[list_parents_TID.size() - 1])
                    .arg(model_name);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            while(qsQuery_TMATE_MDB.next())
            {
                list_parents_TID.append(qsQuery_TMATE_MDB.value(0).toString());
                next_parent_TID  = qsQuery_TMATE_MDB.value(0).toString();
            }
        }while(next_parent_TID != nullptr);

    //获取模块传递链名称
        for(int i=0;i<list_parents_TID.size();i++)
        {
            sql_prepare = QString("SELECT MODULE_NAME FROM MODULE_PROPS WHERE MODULE_TID = '%1' AND MODEL_NAME = '%2';")
                    .arg(list_parents_TID[i]).arg(model_name);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            while(qsQuery_TMATE_MDB.next())
            {
                list_parents_NAME.append(qsQuery_TMATE_MDB.value(0).toString());
            }
        }
        return list_parents_NAME;
}
