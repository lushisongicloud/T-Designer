/*************************************************
 * Copyright:杭州诺云科技有限公司
 * Author:许伟
 * Date:2020-5-11
 * Description:D矩阵相关所有内容存储及变换函数
**************************************************/
#ifndef MATRIX_D_CLASS_H
#define MATRIX_D_CLASS_H
#include <QMainWindow>
#include <QDateTime>
#include <QtSql>

class Matrix_D_class{
    public:
    //测试偏好集定义

    void now_time();

    typedef struct  {
        int TEST_COST_prefer = 5;//测试花费占比数值
        int TEST_LEVEL_prefer = 5;//测试优先级占比数值
        int TEST_TIME_prefer = 5;//测试时间占比数值
        int FAULT_PROBABLITY_prefer = 10;//故障先验概率占比数值
    }StrPreferData;
    StrPreferData ThisPreferData;
    void init_test_preference_message(QString selected_model);//初始化测试偏好集

    //最底层模块集定义
    typedef struct  {
        bool sign_module;//模块使能标志变量
        QString MODULE_TID;//模块ID
        QString MODULE_NAME;//模块名称
        double MODULE_MTTF;//模块MTTF
        double FAULT_PROBABLITY;//故障先验概率
        QString REPAIR_NOTES;//维修说明
        QList<QString> list_signals;//信号集
    }StrModuleData;//最底层单元数据集定义
    StrModuleData OneModuleData;
    QList<StrModuleData> list_LOWEST_MODULE_DATA;//最底层单元数据集结构列表
    void init_the_lowest_module_message(QString selected_model);//初始化最底层模块集
    void init_the_fault_probablity_message();//初始化目前使能模块的故障先验概率

    //测试和征兆集定义
    typedef struct  {
        bool sign_test;//测试使能标志变量
        QString TEST_TID;//测试TID
        QString TEST_NAME;//测试名称
        double TEST_COST;//测试花费
        double TEST_LEVEL;//测试优先级
        double TEST_TIME;//测试时间
        int TEST_TYPE;//测试类型
        QString DESCRIPTION;//测试描述
        QString TEST_PROCEDURE;//测试步骤
        QString TEST_POINT_NAME;//测试所属的测试点名称
        QString TEST_POINT_TID;//测试所属的测试点TID
        QString Connected_module_TID;//测试所属测试点连接的模块TID
        int TEST_SIGNAL_IS_EXIT_OR_NOT;//测试或征兆是否存在
        QList<QString> need_tools;//所需工具集
        QList<QString> list_signals;//信号集
    }StrTestData;
    StrTestData OneTestData;
    QList<StrTestData>list_TEST_DATA;//测试结构列表
    void init_the_test_message(QString selected_model);//初始化测试与征兆集

    //D矩阵定义
    QList<QList<int>> Matrix_D_value;
    void read_the_D_Matrix(QString selected_model);//解析D矩阵
    QList<int> trans_16to2(QString string,int Num_List);//D矩阵值解析函数

    //可用工具集定义
    QList<QString> list_Tool_DATA;
    void init_the_tool_message(QString selected_model);//初始化工具集

    //D矩阵操作
    void delete_one_test_row(int Num);//删除D矩阵第Num行
    void delete_one_module_Column(int Num);//删除D矩阵第Num列
    void init_condition_D_matrix();//初始化条件D矩阵(即考虑已发现现象、测试工具等条件的D矩阵)
    bool diagnosis_end();//判断当前D矩阵检测是否结束
    QString select_a_test_from_now_test_data();//在当前测试库中选择一个测试并返回测试TID

    //当前检测测试多媒体相关信息
    typedef struct{
        int FILE_SIZE;
        QString CHECKSUM;
        QString MEDIA_NAME;
        QByteArray IMAGE_DATA;
    }Str_MULTIMEDIA;
    QList<Str_MULTIMEDIA> MULTIMEDIA_List;
    Str_MULTIMEDIA MULTIMEDIA;
    void select_multimedia_of_this_test(QString selected_model,QString test_TID);//查找当前测试的多媒体信息并存储到多媒体信息表
    void select_multimedia_of_this_module(QString selected_model,QString module_TID);//查找当前模块的多媒体信息并存储到多媒体信息表

    //一个测试记录
    typedef struct{
        QString Diagnosis_test_name;//诊断测试名称
        QString recommend_or_self_selected = "推荐测试";//诊断测试是推荐测试还是自选测试
        QString yes_or_no = "测试正常";//诊断测试是否正常或跳过
    }str_test_record;
    str_test_record one_test_cord;

    //诊断记录信息
    typedef struct{
        QString DIAGNOSTIC_ID;//诊断编号
        QDateTime start_time;//诊断开始时间//在点击诊断时初始化
        QDateTime finish_time;//诊断结束时间//在诊断反馈界面时初始化
        QDate Diagnosis_Date;//检修日期//在点击诊断时初始化
        QString feedback_text;//诊断留言//点击提交记录时初始化
        QString user_name;//用户名称//在诊断反馈界面初始化
        QString maintain_company;//维修单位//在诊断反馈界面初始化
        QString equipment_name;//装备名称//在诊断反馈界面初始化
        QString boat_number;//舰艇舷号//点击提交记录时初始化
        bool if_solved_or_not;//是否解决//在诊断反馈界面初始化
        QString fault_phenomenon;//故障现象//在初始化条件D矩阵时初始化
        QString fault_module;//诊断故障模块//在结果界面初始化
        QList<QString> list_tool;//工具集合//初始化条件D矩阵时初始化
        QString advance_omen_test;//预先征兆的名称//初始化条件D矩阵时初始化
        QList<str_test_record> list_Diagnosis_test_record;//诊断测试记录//在点击诊断时初始化
    }str_diagnostic_record;
    str_diagnostic_record  diagnostic_record;

    void print_out();//测试输出
    QString select_test_connected_module(QString targrt_test_point_TID,QString model_name);//通过测试点TID寻找所连接的模块
    QList<QString> select_module_transitive_telation(QString traget_module_TID,QString model_name);//获取模块传递链
};

extern Matrix_D_class  Matrix_D;//D矩阵类实例化
extern QString diagnosis_model_name;//诊断模型名称
extern QSqlDatabase TMATE_MDB;//TMATE数据库链接
extern QSqlQuery qsQuery_TMATE_MDB;//TMATE数据库选择模型
extern QString sql_prepare;//数据库检索准备语句

#endif // MATRIX_D_CLASS_H
