/*************************************************
 * Copyright:杭州诺云科技有限公司
 * Author:许伟
 * Date:2020-5-11
 * Description:诊断主文件及其相关函数
**************************************************/
#ifndef DIAGNOSIS_MAINWINDOW_H
#define DIAGNOSIS_MAINWINDOW_H

#include <QMainWindow>
#include <QtSql>
#include <QtCharts>
#include "dialog_wait.h"
#include "thread_init.h"
#include "myqsqltablemodel.h"
namespace Ui {
class Diagnosis_MainWindow;
}

typedef struct{
    QString Operating_user; //用户名
    QString Operating_ID;//用户ID
    QString User_department;//用户单位
    QString Operating_PSW; //用户密码
    int Operating_limit;//操作权限
    QDateTime  LoginTime;//上次登录时间
}Str_account;

class Diagnosis_MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    explicit Diagnosis_MainWindow(QWidget *parent = nullptr);
    ~Diagnosis_MainWindow();

    QString  tableWidgetStyleSheet;//qss格式
    QString  tableViewStyleSheet;//qss格式
    QString  tableWidgetScrollBarStyleSheet;//qss格式
    QString  tableWidgetHorizontalHeaderStyleSheet;//qss格式

    void connect_TMATE_MDB();//创建TMATE数据库连接

signals:
    //void send_the_Testlist_to_select_another_test(QList<QString> list_test);//选择其他测试信号
    void send_the_details_record_to_the_UI(QList<QList<QString>> list);
    void send_the_ToolList_to_case_entry_test_new(QList<QString>);//发送工具列表到工具新增界面
private slots:
    void on_toolButton_delete_model_clicked();

    void on_toolButton_start_diagnosis_clicked();

    void on_toolButton_tool_select_next_clicked();

    void on_tableWidget_tool_select_cellChanged(int row, int column);

    void on_toolButton_tool_select_last_clicked();

    void on_toolButton_diagnosis_normal_clicked();

    void on_toolButton_diagnosis_abnormal_clicked();

    void on_toolButton_skip_this_test_clicked();

    void on_toolButton_clicked();

    void on_toolButton_8_clicked();

    void on_toolButton_slelct_other_test_clicked();

    void on_toolButton_tool_select_all_clicked();

    void on_btn_tool_serch_clicked();

    void on_toolButton_known_test_select_last_clicked();

    void on_tableWidget_known_test_select_cellChanged(int row, int column);

    void on_btn_known_test_searching_clicked();

    void on_toolButton_known_test_all_no_clicked();

    void on_toolButton_known_test_all_skip_clicked();

    void on_toolButton_known_test_all_yes_clicked();

    void on_toolButton_known_test_select_next_clicked();

    void on_btn_known_symptom_searching_clicked();

    void on_toolButton_known_symptom_select_last_clicked();

    void on_toolButton_known_symptom_select_next_clicked();

    void on_tableWidget_known_symptom_select_cellChanged(int row, int column);

    void on_toolButton_known_symptom_select_all_clicked();

    void on_toolButton_tool_not_select_all_clicked();

    void on_toolButton_not_exit_symptom_select_all_clicked();

    void on_select_ratio_triggered();

    void on_toolButton_known_symptom_all_skip_clicked();

    void on_tableWidget_test_file_doubleClicked(const QModelIndex &index);

    void on_toolButton_resule_next_clicked();

    void on_toolButton_information_feedback_return_clicked();

    void on_toolButton_information_feedback_submit_clicked();

    void on_radioButton_problem_is_solved_clicked(bool checked);

    void on_radioButton_problem_is_not_solved_clicked(bool checked);

    void on_toolButton_4_clicked();

    void on_toolButton_record_query_view_details_clicked();

    void on_tableWidget_diagnosis_record_table_cellChanged(int row, int column);

    void on_checkBox_hide_unresolved_records_clicked(bool checked);

    void on_checkBox_hide_solved_records_clicked(bool checked);

    void on_toolButton_record_query_query_clicked();

    void on_toolButton_6_clicked();

    void on_toolButton_7_clicked();

    void on_toolButton_3_clicked();

private:
    Ui::Diagnosis_MainWindow *ui;

    int screenWidth;

    bool init_tool_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_known_test_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_known_symptom_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_Currently_displayed_diagnostic_record_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_case_entry_known_symptom_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_case_entry_test_result_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    bool init_case_entry_fault_module_list_is_not_cell_change;//用于解决tablewidget初始化时触发槽信号问题
    MyQSqlTableModel  *tabModel;  //数据选择模型
    Dialog_wait *dlg_delay;//模态对话框
    QDialog *dlg_showPicture;//展示图片窗口
    QLabel *picture_Label;
    thread_init  thread_init_Data;//初始化线程

    QString user_or_model = "model";//案例录入中模型和用户录入选择

    QWidget* mpShadeWindow;//遮罩窗口

    //当前显示的诊断记录信息
    typedef struct{
        QString DIAGNOSTIC_ID;//诊断编号
        QDateTime start_time;//诊断开始时间
        QDateTime finish_time;//诊断结束时间
        QDate Diagnosis_Date;//检修日期
        QString feedback_text;//诊断留言
        QString user_name;//用户名称
        QString maintain_company;//维修单位
        QString equipment_name;//装备名称
        QString boat_number;//舰艇舷号
        bool if_solved_or_not;//是否解决
        QString fault_phenomenon;//故障现象
        QString fault_module;//故障模块
        bool pitch_on = false;
        bool Is_artificial_cord = false;
    }str_Currently_displayed_diagnostic_record;

    QList<str_Currently_displayed_diagnostic_record> Currently_displayed_diagnostic_record_list;

    typedef struct{
        QString TEST_NAME;//测试名称
        int TEST_SIGNAL_IS_EXIT_OR_NOT;//测试状态
        int row;//选中行
        int column;//选中列
        bool have_test_selected;
    }str_case_entry_select_one_test;
    str_case_entry_select_one_test selected_test_and_state;

    //    //一个测试记录
    //    typedef struct{
    //        QString Diagnosis_test_name;//诊断测试名称
    //        QString recommend_or_self_selected = "推荐测试";//诊断测试是推荐测试还是自选测试
    //        QString yes_or_no = "测试正常";//诊断测试是否正常或跳过
    //    }str_test_record;
    //    str_test_record case_entry_one_test_cord;

    bool hide_unresolved_records = false;//是否隐藏未解决记录
    bool hide_solved_records = false;//是否隐藏已解决记录

    QString encrypt(const QString& str);//字符串加密

    void init_model_list();//初始化数据库模型UI列表
    void init_tool_list(QString model_name,QString fuzzy_search);//初始化模型所需工具UI列表
    void init_test_list(QString model_name,QString fuzzy_name_search,QString fuzzy_description_search);//初始化测试信号UI列表
    void init_symptom_list(QString model_name,QString fuzzy_name_search,QString fuzzy_description_search);//初始化测试信号UI列表
    void init_diagnosis_record_query_list();//初始化诊断记录查询列表
    void InitAccountManage();

    void delete_lacal_MODELS_all_information(QString selected_model);//删除本地所有该模型信息

    //选取模块所属的分机
    QString ModuleBelongsSubSystem(QString ModelName,QString ModuleName);

    void show_now_test_data_to_UI(QString TEST_TID);//依据TEST_TID在诊断界面UI显示相关信息
    void show_the_diagnosis_result();//显示诊断结果

    void iniBarChart();//初始化统计预测树状图
    void build_diagnosis_result(QString boat_name,int solved_number,int undersolved_number);//构建诊断情况图表
    void build_repair_time(QList<int> repair_time_list);//构建修理时间曲线图表
    void build_repair_interval(QList<int> repair_interval_list);//构建修理间隔曲线图表
    void build_fuzzy_set(QList<int> fuzzy_set_list);//构建诊断模糊组图表
    void redrawBarChart(QString boatNumber,QDateTime start_Time,QDateTime finish_Time);//重绘预测树状图


    void init_case_entry_model_list();//初始化案例录入模型列表
    void init_case_entry_symptom_list(QString model_name,QString fuzzy_search,QString user_or_model);//初始化案例录入征兆选择信号UI列表
    void init_case_entry_test_list(QString model_name, QString fuzzy_search, QString user_or_model,bool hide_selected_tests);//初始化案例录入初始化测试UI列表
    void init_case_entry_fault_module_list(QString model_name,QString fuzzy_search,QString user_or_model);//初始化案例录入故障模块选择UI列表
    void save_case_entry_one_test_result_to_record();//将测试信息保存到诊断记录

    void hide_menu_bar();
    void show_menu_bar();
    //void init_the_signal_message(QString selected_model);//初始化信号集
    //void init_condition_signal_message(QString selected_model);//初始化配置后的信号集
    //void init_fault_list(QString model_name);//初始化故障列表
private slots:
    void onthread_Data_finished();
    void on_toolButton_record_query_delete_clicked();
    void on_toolButton_resule_OK_next_clicked();
    void on_toolButton_all_result_next_clicked();
    void fault_vague_group_list_clicked();
    void on_toolButton_more_fault_details_return_clicked();
    void on_tableWidget_result_more_fault_details_file_doubleClicked(const QModelIndex &index);
    void on_electronic_manual_triggered();
    void on_toolButton_record_query_query_2_clicked();
    void on_toolButton_case_entry_model_selected_OK_clicked();
    void on_radioButton_select_known_symptom_model_clicked();
    void on_radioButton_select_known_symptom_user_clicked();
    void on_btn_case_entry_known_symptom_searching_clicked();
    void on_tableWidget_case_entry__known_symptom_select_cellChanged(int row, int column);
    void on_toolButton_case_entry_known_symptom_select_all_clicked();
    void on_toolButton_case_entry_not_exit_symptom_select_all_clicked();
    void on_toolButton_case_entry_known_symptom_all_skip_clicked();
    void on_toolButton_case_entry_known_symptom_select_new_clicked();
    void on_toolButton_case_entry_known_symptom_select_next_clicked();
    void on_radioButton_select_test_result_model_clicked();
    void on_radioButton_select_test_result_user_clicked();
    void on_btn_case_entry_test_result_searching_clicked();
    void on_tableWidget_case_entry_test_result_cellChanged(int row, int column);
    void on_toolButton_case_entry_test_result_next_clicked();
    void on_toolButton_case_entry_test_result_new_clicked();
    void on_toolButton_case_entry_test_result_diagnosis_result_clicked();
    void on_btn_case_entry_fault_module_searching_clicked();
    void on_radioButton_select_fault_module_model_clicked();
    void on_radioButton_select_fault_module_user_clicked();
    void on_toolButton_case_entry_fault_module_select_new_clicked();
    void on_toolButton_case_entry_fault_module_select_next_clicked();
    void on_tableWidget_case_entry_fault_module_select_cellChanged(int row, int column);
    void on_toolButton_case_entry_information_feedback_submit_clicked();
    void on_radioButton_case_entry_problem_is_solved_clicked();
    void on_radioButton_case_entry_problem_is_not_solved_clicked();
    void on_Display_menu_bar_triggered(bool checked);
    void on_tableWidget_solve_file_doubleClicked(const QModelIndex &index);
    void on_toolButton_export_statistics_chart_clicked();
    void on_pushButton_last_test_photo_clicked();
    void on_pushButton_next_test_photo_clicked();
    void on_pushButton_last_solve_image_clicked();
    void on_pushButton_next_solve_image_clicked();
    void on_pushButton_last_more_fault_details_image_clicked();
    void on_pushButton_next_more_fault_details_image_clicked();
    void on_btn_add_account_clicked();
    void on_pushButton_delete_account_clicked();
    void on_pushButton_change_password_clicked();
    void on_pushButton_change_permission_clicked();
    void on_toolButton_record_query_output_clicked();


protected:
    virtual void resizeEvent(QResizeEvent *event) override;
};

#endif // DIAGNOSIS_MAINWINDOW_H
