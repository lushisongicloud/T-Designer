#-------------------------------------------------
#
# Project created by QtCreator 2022-02-07T21:57:24
#
#-------------------------------------------------

QT       += core gui sql widgets concurrent xml

greaterThan(QT_MAJOR_VERSION, 4): QT += widgets

TARGET = T-Solver
TEMPLATE = app

# QMAKE_CXXFLAGS_RELEASE -= -O3

# The following define makes your compiler emit warnings if you use
# any feature of Qt which has been marked as deprecated (the exact warnings
# depend on your compiler). Please consult the documentation of the
# deprecated API in order to know how to port your code away from it.
DEFINES += QT_DEPRECATED_WARNINGS

# You can also make your code fail to compile if you use deprecated APIs.
# In order to do so, uncomment the following line.
# You can also select to disable deprecated APIs only up to a certain version of Qt.
#DEFINES += QT_DISABLE_DEPRECATED_BEFORE=0x060000    # disables all the APIs deprecated before Qt 6.0.0

CONFIG += c++17
CONFIG += qscintilla2
CONFIG += utf8_source
win32-msvc* {
    QMAKE_CXXFLAGS += /utf-8
    QMAKE_CFLAGS += /utf-8
}

win32-g++ {
    QMAKE_CXXFLAGS += -finput-charset=UTF-8 -fexec-charset=UTF-8
}

macx {
    QMAKE_POST_LINK = install_name_tool -change libqscintilla2_qt$${QT_MAJOR_VERSION}.15.dylib $$[QT_INSTALL_LIBS]/libqscintilla2_qt$${QT_MAJOR_VERSION}.15.dylib $(TARGET)
}

SOURCES += \
    BO/worker.cpp \
    DO/diagnosisgraph.cpp \
        main.cpp \
        mainwindow.cpp \
    solverrunnable.cpp \
    sqlitedatabase.cpp \
    DO/component.cpp \
    DO/parameter.cpp \
    DO/model.cpp \
    BO/componententity.cpp \
    BO/systementity.cpp \
    formcreatnewcomponent.cpp \
    widget/mycombobox.cpp \
    widget/selectfunctiondialog.cpp \
    z3solverthread.cpp \
    mythread.cpp \
    graphadjlist.cpp \
    combotree.cpp \
    binaryboolcalcute.cpp \
    cutthread.cpp \
    variable_range_config.cpp \
    testability/constraint_utils.cpp \
    testability/smt_facade.cpp \
    testability/function_catalog.cpp \
    testability/d_matrix_builder.cpp \
    testability/demo_runner.cpp \
    widget/dmatrixoptionsdialog.cpp \
    widget/dmatrixmodel.cpp \
    widget/dmatrixviewerdialog.cpp \
    widget/dmatrixselectiondialog.cpp \
    widget/variablerangedialog.cpp \
    function_variable_config.cpp \
    widget/functionvariablevaluedialog.cpp

INCLUDEPATH += \
        $$PWD/include/z3

LIBS += $$PWD/lib/libz3.lib

HEADERS += \
    BO/worker.h \
    DO/diagnosisgraph.h \
        mainwindow.h \
    solverrunnable.h \
    sqlitedatabase.h \
    DO/component.h \
    DO/parameter.h \
    DO/model.h \
    BO/componententity.h \
    BO/systementity.h \
    formcreatnewcomponent.h \
    widget/mycombobox.h \
    widget/selectfunctiondialog.h \
    z3solverthread.h \
    mythread.h \
    graphadjlist.h \
    combotree.h \
    binaryboolcalcute.h \
    cutthread.h \
    graphlisthead.h \
    variable_range_config.h \
    testability/constraint_utils.h \
    testability/testability_types.h \
    testability/smt_facade.h \
    testability/function_catalog.h \
    testability/d_matrix_builder.h \
    testability/demo_runner.h \
    widget/dmatrixoptionsdialog.h \
    widget/dmatrixmodel.h \
    widget/dmatrixviewerdialog.h \
    widget/dmatrixselectiondialog.h \
    widget/variablerangedialog.h \
    function_variable_config.h \
    widget/functionvariablevaluedialog.h

FORMS += \
    mainwindow.ui \
    formcreatnewcomponent.ui \
    widget/selectfunctiondialog.ui \
    widget/dmatrixoptionsdialog.ui \
    widget/dmatrixviewerdialog.ui

INCLUDEPATH += \
        $$PWD/include/z3

LIBS += $$PWD/lib/libz3.lib

# Default rules for deployment.
qnx: target.path = /tmp/$${TARGET}/bin
else: unix:!android: target.path = /opt/$${TARGET}/bin
!isEmpty(target.path): INSTALLS += target
