#include "formhydraulicstate.h"
#include "ui_formhydraulicstate.h"


#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif
extern RuleVariablePool m_RuleVariablePool;
FormHydraulicState::FormHydraulicState(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),m_Database(TMATE_Database),
    ui(new Ui::FormHydraulicState)
{
    ui->setupUi(this);
    ui->widget3D->installEventFilter(this);//widget控件安装事件过滤器
    ui->widget3D->setMouseTracking(true);
    ui->widgetBackPumpState->installEventFilter(this);//widget控件安装事件过滤器
    ui->widgetBackPumpState->setMouseTracking(true);
    ui->widgetCentreBoxState->installEventFilter(this);//widget控件安装事件过滤器
    ui->widgetCentreBoxState->setMouseTracking(true);
    ui->widgetHydraulicState->installEventFilter(this);//widget控件安装事件过滤器
    ui->widgetHydraulicState->setMouseTracking(true);
    ui->widgetImprovePumpState->installEventFilter(this);//widget控件安装事件过滤器
    ui->widgetImprovePumpState->setMouseTracking(true);
    ui->widgetMechCtrolBoxState->installEventFilter(this);//widget控件安装事件过滤器
    ui->widgetMechCtrolBoxState->setMouseTracking(true);
    SetStackWidgetPage(5);
}

#define AlarmHydroPosxmin 295
#define AlarmHydroPosxmax 896
#define AlarmHydroPosymin 80
#define AlarmHydroPosymax 750
#define AlarmCentreBoxPosxmin 880
#define AlarmCentreBoxPosxmax 1115
#define AlarmCentreBoxPosymin 45
#define AlarmCentreBoxPosymax 305
#define AlarmMechBoxPosxmin 700
#define AlarmMechBoxPosxmax 880
#define AlarmMechBoxPosymin 75
#define AlarmMechBoxPosymax 300
#define AlarmBackPumpPosxmin 115
#define AlarmBackPumpPosxmax 260
#define AlarmBackPumpPosymin 56
#define AlarmBackPumpPosymax 307
#define AlarmImprovePumpPosxmin 265
#define AlarmImprovePumpPosxmax 445
#define AlarmImprovePumpPosymin 70
#define AlarmImprovePumpPosymax 285
#define ModMode 1
bool FormHydraulicState::eventFilter(QObject *obj, QEvent *event)
{
    if (obj == ui->widget3D) // 你要过滤的对象
    {
        if (event->type() == QEvent::MouseButtonPress)
        {

           //根据坐标确定转到哪个分系统
            QMouseEvent *mouseEvent = (QMouseEvent *)event;
            if(mouseEvent->buttons()&Qt::LeftButton)
            {
                QPoint p=mouseEvent->pos();
                //QString s="x= "+QString::number(p.x())+" y= "+QString::number(p.y());
                if((p.x()>AlarmCentreBoxPosxmin)&&(p.x()<AlarmCentreBoxPosxmax)&&(p.y()>AlarmCentreBoxPosymin)&&(p.y()<AlarmCentreBoxPosymax))
                    SetStackWidgetPage(1);//1电源滤波机柜（中心控制箱）
                else if(p.x()>AlarmMechBoxPosxmin&&p.x()<AlarmMechBoxPosxmax&&p.y()>AlarmMechBoxPosymin&&p.y()<AlarmMechBoxPosymax)
                    SetStackWidgetPage(2);//2收放控制机柜（机旁控制箱）
                //else if(p.x()>AlarmBackPumpPosxmin&&p.x()<AlarmBackPumpPosxmax&&p.y()>AlarmBackPumpPosymin&&p.y()<AlarmBackPumpPosymax)
                    //SetStackWidgetPage(3); //3备用控制箱 不用  //lu
                else if(p.x()>AlarmImprovePumpPosxmin&&p.x()<AlarmImprovePumpPosxmax&&p.y()>AlarmImprovePumpPosymin&&p.y()<AlarmImprovePumpPosymax)
                    SetStackWidgetPage(4);//4传感器系统（提升泵）
                else if(p.x()>AlarmHydroPosxmin&&p.x()<AlarmHydroPosxmax&&p.y()>AlarmHydroPosymin&&p.y()<AlarmHydroPosymax)
                    SetStackWidgetPage(0);//5系统组成（page_3D）
            }

        }
        if(event->type()==QEvent::MouseMove)
                {
                    QMouseEvent *mouseEvent = (QMouseEvent *)event;

                    QPoint p=mouseEvent->pos();
                    //QString s="x= "+QString::number(p.x())+" y= "+QString::number(p.y());
                    //qDebug()<<s;

                }
        return true; // 注意这里一定要返回true，表示你要过滤该事件原本的实现
    }
    else if (obj == ui->widgetBackPumpState||obj == ui->widgetCentreBoxState||obj == ui->widgetHydraulicState||obj == ui->widgetImprovePumpState||obj == ui->widgetMechCtrolBoxState)
    {
        #ifdef ModMode

        if (event->type() == QEvent::MouseButtonPress)
        {

           //根据坐标确定转到哪个分系统
            QMouseEvent *mouseEvent = (QMouseEvent *)event;
            if(mouseEvent->buttons()&Qt::LeftButton)
            {
                QPoint p=mouseEvent->pos();
                bool ok=false;
                int AlarmIdx=QInputDialog::getInt(this,"报警序号","输入报警的序号，从1开始",1,1,50,1,&ok);
                if(ok)
                {
                    qDebug()<<m_Database->UpdateAlarmCursor(GetStackWidgetPageName(),AlarmIdx,p.x(),p.y());
                }
            }
        }
        return true;
        #endif

      if(event->type()==QEvent::MouseMove)
                {
                    QMouseEvent *mouseEvent = (QMouseEvent *)event;

                    QPoint p=mouseEvent->pos();
                    //QString s="x= "+QString::number(p.x())+" y= "+QString::number(p.y());
                    //qDebug()<<s;

                }
    }
    return false; // 返回false表示不过滤，还按默认的来
}

void FormHydraulicState::InitDisPlayRadioButton()
{
    LoadDisPlayRadioButton(0,m_RuleVariablePool.GetAlarmSignalVector("传感器信号-外部"));
    //qDebug()<<"original size="<<m_RuleVariablePool.GetAlarmSignalVector("液压系统").size();
    LoadDisPlayRadioButton(1,m_RuleVariablePool.GetAlarmSignalVector("传感器信号-内部"));
    LoadDisPlayRadioButton(2,m_RuleVariablePool.GetAlarmSignalVector("变频器控制信号"));
    LoadDisPlayRadioButton(3,m_RuleVariablePool.GetAlarmSignalVector("备用泵电机启动箱"));
    LoadDisPlayRadioButton(4,m_RuleVariablePool.GetAlarmSignalVector("提升泵电机启动箱"));
}
void FormHydraulicState::DelDisPlayRadioButton()
{
    qDeleteAll(DisPlayQCheckBox[0]);
    qDeleteAll(DisPlayQCheckBox[1]);
    qDeleteAll(DisPlayQCheckBox[2]);
    qDeleteAll(DisPlayQCheckBox[3]);
    qDeleteAll(DisPlayQCheckBox[4]);
}
void FormHydraulicState::LoadDisPlayRadioButton(int SignalPosIdx,QVector<DataBase::Signal> Alarm_signal)
{
    DisPlayQCheckBox[SignalPosIdx].resize( Alarm_signal.size());
    //qDebug()<<"SignalPosIdx="<<SignalPosIdx<<" Alarm_signal size="<<Alarm_signal.size();
    for(int i=0;i<Alarm_signal.size();i++)
    {
         //qDebug()<<"i="<<i<<"posx="<<Alarm_signal[i].DisplayPosx<<"posy="<<Alarm_signal[i].DisplayPosy;
         if(SignalPosIdx==0)   DisPlayQCheckBox[SignalPosIdx][i]=new QCheckBox(ui->widgetHydraulicState);
         if(SignalPosIdx==1)   DisPlayQCheckBox[SignalPosIdx][i]=new QCheckBox(ui->widgetCentreBoxState);
         if(SignalPosIdx==2)   DisPlayQCheckBox[SignalPosIdx][i]=new QCheckBox(ui->widgetMechCtrolBoxState);
         if(SignalPosIdx==3)   DisPlayQCheckBox[SignalPosIdx][i]=new QCheckBox(ui->widgetBackPumpState);
         if(SignalPosIdx==4)   DisPlayQCheckBox[SignalPosIdx][i]=new QCheckBox(ui->widgetImprovePumpState);
         DisPlayQCheckBox[SignalPosIdx][i]->setEnabled(false);
         DisPlayQCheckBox[SignalPosIdx][i]->setCheckable(true);
         DisPlayQCheckBox[SignalPosIdx][i]->setText("");
         DisPlayQCheckBox[SignalPosIdx][i]->setChecked(true);
         DisPlayQCheckBox[SignalPosIdx][i]->show();
         DisPlayQCheckBox[SignalPosIdx][i]->move(Alarm_signal[i].DisplayPosx,Alarm_signal[i].DisplayPosy);
         if(DisPlayQCheckBox[SignalPosIdx][i]->pos().x()==0&&DisPlayQCheckBox[SignalPosIdx][i]->pos().y()==0)
         {
             DisPlayQCheckBox[SignalPosIdx][i]->setVisible(false);
         }
    }
}

FormHydraulicState::~FormHydraulicState()
{
    delete ui;
}

void FormHydraulicState::UpDate(QMap<QString,DataBase::Signal> signal)
{
        //qDebug()<<"void FormRealTimeData::UpDate(QVector<DataBase::Signal> signal) 待完善";
    if(ui->stackedWidget->currentIndex()>4) return;
    QVector<DataBase::Signal> Alarm_signal;
    if(ui->stackedWidget->currentIndex()==0) Alarm_signal=m_RuleVariablePool.GetAlarmSignalVector("传感器信号-外部");
    if(ui->stackedWidget->currentIndex()==1) Alarm_signal=m_RuleVariablePool.GetAlarmSignalVector("传感器信号-内部");
    if(ui->stackedWidget->currentIndex()==2) Alarm_signal=m_RuleVariablePool.GetAlarmSignalVector("变频器控制信号");
    if(ui->stackedWidget->currentIndex()==3) Alarm_signal=m_RuleVariablePool.GetAlarmSignalVector("备用泵电机启动箱");
    if(ui->stackedWidget->currentIndex()==4) Alarm_signal=m_RuleVariablePool.GetAlarmSignalVector("提升泵电机启动箱");

    //for(int i=0;i<Alarm_signal.size();i++)  qDebug()<<DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->isChecked();
//return;
    //在对应的原理图中显示报警灯
    for(int i=0;i<DisPlayQCheckBox[ui->stackedWidget->currentIndex()].size();i++)
    {
        if(DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().x()==0&&DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().y()==0)
        {
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setVisible(false);
            continue;
        }
        if(Alarm_signal[i].value.BOOL)
        {
            //qDebug()<<Alarm_signal[i].Note;
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->raise();
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setChecked(false);
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setVisible(true);
            //同一器件可能有多种不同报警
            for(int j=0;j<i;j++)
            {
                if(DisPlayQCheckBox[ui->stackedWidget->currentIndex()][j]->pos().x()==DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().x())
                {
                    if(DisPlayQCheckBox[ui->stackedWidget->currentIndex()][j]->pos().y()==DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().y())
                      DisPlayQCheckBox[ui->stackedWidget->currentIndex()][j]->setChecked(false);                  
                }
            }
        }
        else
        {
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setChecked(true);
            DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setVisible(true);
            //同一器件可能有多种不同报警
            for(int j=0;j<i;j++)
            {
                if(DisPlayQCheckBox[ui->stackedWidget->currentIndex()][j]->pos().x()==DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().x())
                {

                    if(DisPlayQCheckBox[ui->stackedWidget->currentIndex()][j]->pos().y()==DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->pos().y())
                    {
                        if(Alarm_signal[j].value.BOOL) DisPlayQCheckBox[ui->stackedWidget->currentIndex()][i]->setChecked(false);
                    }
                }
            }
        }
    }
}

void FormHydraulicState::SetStackWidgetPage(int WinInd)
{
  ui->stackedWidget->setCurrentIndex(WinInd);
  emit newFaliureError();
}

//0:液压系统 1：中心控制箱 2：机旁控制箱 3：备用泵电机启动箱 4：提升泵电机启动箱
int FormHydraulicState::GetStackWidgetPageName()
{
  return ui->stackedWidget->currentIndex();
}

void FormHydraulicState::Set3DWidgetPNG(int Ind)//0:液压系统 1：中心控制箱 2：机旁控制箱 3：备用泵电机启动箱 4：提升泵电机启动箱
{
    QString StyleSheetStr="#widget3D{border-image: url(C:/MDB/images/";

    ui->widget3D->setStyleSheet(StyleSheetStr+QString::number(Ind)+".png);}");
   /*
    switch(Ind)
    {
      case 0x00:
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/3D模型.png);}");
        break;

      case -1:
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/3D模型.png);}");
        break;
      case 0://0:液压系统
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/液压系统报警图.png);}");
        break;
      case 1://1：中心控制箱
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/中心控制箱报警图.png);}");
        break;
      case 2://2：机旁控制箱
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/机旁控制箱报警图.png);}");
        break;
      case 3://3：备用泵电机启动箱
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/备用泵电机启动箱报警图.png);}");
        break;
      case 4://4：提升泵电机启动箱
        ui->widget3D->setStyleSheet("#widget3D{border-image: url(:/widget/提升泵电机启动箱报警图.png);}");
        break;
    }
    */
    ui->widget3D->update();

}

void FormHydraulicState::on_BtReturn_6_clicked()
{
    SetStackWidgetPage(5);
}

void FormHydraulicState::on_BtReturn_2_clicked()
{
    SetStackWidgetPage(5);
}

void FormHydraulicState::on_BtReturn_3_clicked()
{
    SetStackWidgetPage(5);
}

void FormHydraulicState::on_BtReturn_4_clicked()
{
    SetStackWidgetPage(5);
}

void FormHydraulicState::on_BtReturn_5_clicked()
{
    SetStackWidgetPage(5);
}
