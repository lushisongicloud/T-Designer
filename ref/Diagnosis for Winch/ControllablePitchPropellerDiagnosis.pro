#-------------------------------------------------
#
# Project created by QtCreator 2021-04-26T10:20:42
#
#-------------------------------------------------


QT       += core gui sql charts network axcontainer

greaterThan(QT_MAJOR_VERSION, 4): QT += widgets printsupport

TARGET = ControllablePitchPropellerDiagnosis
TEMPLATE = app

# The following define makes your compiler emit warnings if you use
# any feature of Qt which has been marked as deprecated (the exact warnings
# depend on your compiler). Please consult the documentation of the
# deprecated API in order to know how to port your code away from it.
DEFINES += QT_DEPRECATED_WARNINGS

# You can also make your code fail to compile if you use deprecated APIs.
# In order to do so, uncomment the following line.
# You can also select to disable deprecated APIs only up to a certain version of Qt.
#DEFINES += QT_DISABLE_DEPRECATED_BEFORE=0x060000    # disables all the APIs deprecated before Qt 6.0.0

CONFIG += c++11


SOURCES += \
        main.cpp \
        mainwindow.cpp \
    myqsqldatabase.cpp \
    UserManage/usermanage.cpp \
    UserManage/add_new_account.cpp \
    UserManage/qdlglogin.cpp \
    ConnectManage/connectset.cpp \
    VariableManage/variablemanage.cpp \
    VariableManage/dialogvariabledefine.cpp \
    RuleManage/rulemanage.cpp \
    RuleManage/dialogruledefine.cpp \
    RealTimeDisplayManage/formhydraulicstate.cpp \
    RealTimeDisplayManage/formrealtimedata.cpp \
    RealTimeDisplayManage/formalarminformation.cpp \
    DataTransManage/mk2cpu_datatransthread.cpp \
    DataTransManage/mk5cpu_datatransthread.cpp \
    DataTransManage/detector1_datatransthread.cpp \
    Diagnosis/diagnosis.cpp \
    Diagnosis/rulepool.cpp \
    Diagnosis/rulevariablepool.cpp \
    mythread.cpp \
    texteditdelegate.cpp \
    dialogallbasepara.cpp \
    WarnManage/dialogwarningdefine.cpp \
    WarnManage/rulewarnmanage.cpp \
    RealTimeDisplayManage/formwarninformation.cpp \
    dialogshowtaskcurve.cpp \
    ./common/simplegraph.cpp \
    qcustomplot.cpp \
    Data_Save.cpp \
    drawgridset.cpp \
    dlgmessage.cpp \
    bqgraphicsitem.cpp \
    bqgraphicsscene.cpp \
    bpointitem.cpp \
    bqgraphicsitem.cpp \
    bqgraphicsscene.cpp \
    bqgraphicsview.cpp \
    dlgtestprio.cpp

HEADERS += \
        mainwindow.h \
    myqsqldatabase.h \
    UserManage/usermanage.h \
    UserManage/add_new_account.h \
    UserManage/qdlglogin.h \
    ConnectManage/connectset.h \
    VariableManage/variablemanage.h \
    VariableManage/dialogvariabledefine.h \
    RuleManage/rulemanage.h \
    RuleManage/dialogruledefine.h \
    RealTimeDisplayManage/formhydraulicstate.h \
    RealTimeDisplayManage/formrealtimedata.h \
    RealTimeDisplayManage/formalarminformation.h \
    DataTransManage/mk2cpu_datatransthread.h \
    DataTransManage/mk5cpu_datatransthread.h \
    DataTransManage/detector1_datatransthread.h \
    Diagnosis/diagnosis.h \
    Diagnosis/rulepool.h \
    Diagnosis/rulevariablepool.h \
    mythread.h \
    texteditdelegate.h \
    dialogallbasepara.h \
    WarnManage/dialogwarningdefine.h \
    WarnManage/rulewarnmanage.h \
    RealTimeDisplayManage/formwarninformation.h \
    dialogshowtaskcurve.h \
    ./common/simplegraph.h\
    qcustomplot.h \
    bdaqctrl.h \
    CommDef.h \
    Data_Save.h \
    drawgridset.h \
    dlgmessage.h \
    bqgraphicsitem.h \
    bqgraphicsscene.h \
    bpointitem.h \
    bqgraphicsitem.h \
    bqgraphicsscene.h \
    bqgraphicsview.h \
    dlgtestprio.h

FORMS += \
        mainwindow.ui \
    UserManage/usermanage.ui \
    UserManage/add_new_account.ui \
    UserManage/qdlglogin.ui \
    ConnectManage/connectset.ui \
    VariableManage/variablemanage.ui \
    VariableManage/dialogvariabledefine.ui \
    RuleManage/rulemanage.ui \
    RuleManage/dialogruledefine.ui \
    RealTimeDisplayManage/formhydraulicstate.ui \
    RealTimeDisplayManage/formrealtimedata.ui \
    RealTimeDisplayManage/formalarminformation.ui \
    WarnManage/dialogwarningdefine.ui \
    dialogallbasepara.ui \
    WarnManage/dialogwarningdefine.ui \
    WarnManage/rulewarnmanage.ui \
    RealTimeDisplayManage/formwarninformation.ui \
    dialogshowtaskcurve.ui \
    drawgridset.ui \
    dlgmessage.ui \
    dlgtestprio.ui

# Default rules for deployment.
qnx: target.path = /tmp/$${TARGET}/bin
else: unix:!android: target.path = /opt/$${TARGET}/bin
!isEmpty(target.path): INSTALLS += target

RESOURCES += \
    images/images.qrc
RC_ICONS = DiagnosisIcon.ico
DISTFILES +=
