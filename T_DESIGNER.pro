#-------------------------------------------------
#
# Project created by QtCreator 2022-01-10T11:42:37
#
#-------------------------------------------------

QT       += core gui axcontainer charts sql webenginewidgets concurrent xml

greaterThan(QT_MAJOR_VERSION, 4): QT += widgets

TARGET = T-DESIGNER
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
CONFIG += qscintilla2

macx {
    QMAKE_POST_LINK = install_name_tool -change libqscintilla2_qt$${QT_MAJOR_VERSION}.15.dylib $$[QT_INSTALL_LIBS]/libqscintilla2_qt$${QT_MAJOR_VERSION}.15.dylib $(TARGET)
}

SOURCES += \
        main.cpp \
        mainwindow.cpp \
    common.cpp \
    mxdrawxlib.cpp \
    qxlabel.cpp \
    DrawStyle.cpp \
    formaxwidget.cpp \
    dialognewproject.cpp \
    dialogloadsymbol.cpp \
    dialogsymbolattribute.cpp \
    dialogmodifyptermial.cpp \
    dialogsymbols.cpp \
    dialogsymbolsort.cpp \
    dialogBranchAttr.cpp \
    dialogunitmanage.cpp \
    dialogfuncdefine.cpp \
    dialogpageattr.cpp \
    dialogpagenameset.cpp \
    dialogUnitAttr.cpp \
    dialogterminalattr.cpp \
    dialoggenerate.cpp \
    dialogmultiline.cpp \
    dialoglinedefine.cpp \
    dialogcabledefine.cpp \
    dialogconnectattr.cpp \
    dialoglinkedit.cpp \
    dialogsingletermattr.cpp \
    dialognewspur.cpp \
    dialognewlib.cpp \
    dialogattrdefset.cpp \
    dialogfactorymanage.cpp \
    dialogfactoryedit.cpp \
    dialognewfunc.cpp \
    qscilexercppattach.cpp \
    dialogtermbatchmark.cpp \
    graphadjlist.cpp \
    dialogdiagnoseui.cpp \
    dialogfunctionmanage.cpp \
    qxcombobox.cpp \
    dialog_select_another_test.cpp \
    dialog_wait.cpp \
    dialogflurunit.cpp \
    dialogsettestpreference.cpp \
    dialogusertest.cpp \
    dialogaddcondition.cpp \
    dialogdiagusertest.cpp \
    dialogaddterminal.cpp \
    dialogtestreport.cpp \
    dialogmultilib.cpp \
    bpointitem.cpp \
    bqgraphicsitem.cpp \
    bqgraphicsscene.cpp \
    bqgraphicsview.cpp \
    dialogtag.cpp \
    widget/codecheckdialog.cpp \
    widget/mycombobox.cpp \
    widget/mygraphicsview.cpp \
    widget/selectfunctiondialog.cpp \
    widget/containermodel.cpp \
    widget/containertreedialog.cpp \
    widget/containerhierarchyutils.cpp \
    BO/container/containerdata.cpp \
    BO/container/behavioraggregator.cpp \
    BO/function/functiondependencyresolver.cpp \
    BO/test/testdefinition.cpp \
    BO/test/testgeneratorservice.cpp \
    BO/test/diagnosticmatrixbuilder.cpp \
    BO/containerrepository.cpp \
    BO/componententity.cpp \
    BO/systementity.cpp \
    BO/worker.cpp \
    DO/component.cpp \
    DO/diagnosisgraph.cpp \
    DO/model.cpp \
    DO/parameter.cpp \
    sqlitedatabase.cpp \
    mythread.cpp \
    solverrunnable.cpp \
    z3solverthread.cpp \
    combotree.cpp \
    cutthread.cpp
HEADERS += \
        mainwindow.h \
    common.h \
    mxdrawxlib.h \
    qxlabel.h \
    DrawStyle.h \
    formaxwidget.h \
    dialognewproject.h \
    dialogloadsymbol.h \
    dialogsymbolattribute.h \
    dialogmodifyptermial.h \
    dialogsymbols.h \
    dialogsymbolsort.h \
    dialogBranchAttr.h \
    dialogunitmanage.h \
    dialogfuncdefine.h \
    dialogpageattr.h \
    dialogpagenameset.h \
    dialogUnitAttr.h \
    dialogterminalattr.h \
    dialoggenerate.h \
    dialogmultiline.h \
    dialoglinedefine.h \
    dialogcabledefine.h \
    dialogconnectattr.h \
    dialoglinkedit.h \
    dialogsingletermattr.h \
    dialognewspur.h \
    dialognewlib.h \
    dialogattrdefset.h \
    dialogfactorymanage.h \
    dialogfactoryedit.h \
    dialognewfunc.h \
    qscilexercppattach.h \
    dialogtermbatchmark.h \
    graphadjlist.h \
    graphlisthead.h \
    dialogdiagnoseui.h \
    dialogfunctionmanage.h \
    qxcombobox.h \
    dialog_select_another_test.h \
    dialog_wait.h \
    dialogflurunit.h \
    dialogsettestpreference.h \
    dialogusertest.h \
    dialogaddcondition.h \
    dialogdiagusertest.h \
    dialogaddterminal.h \
    dialogtestreport.h \
    dialogmultilib.h \
    bpointitem.h \
    bqgraphicsitem.h \
    bqgraphicsscene.h \
    bqgraphicsview.h \
    dialogtag.h \
    widget/codecheckdialog.h \
    widget/mycombobox.h \
    widget/mygraphicsview.h \
    widget/selectfunctiondialog.h \
    widget/containermodel.h \
    widget/containertreedialog.h \
    widget/containerhierarchyutils.h \
    BO/container/containerdata.h \
    BO/container/behavioraggregator.h \
    BO/function/functiondependencyresolver.h \
    BO/function/functioninfo.h \
    BO/test/testdefinition.h \
    BO/test/testgeneratorservice.h \
    BO/test/diagnosticmatrixbuilder.h \
    BO/containerrepository.h \
    BO/componententity.h \
    BO/systementity.h \
    BO/worker.h \
    DO/component.h \
    DO/diagnosisgraph.h \
    DO/model.h \
    DO/parameter.h \
    DO/containerentity.h \
    sqlitedatabase.h \
    mythread.h \
    solverrunnable.h \
    z3solverthread.h \
    combotree.h \
    cutthread.h

FORMS += \
        mainwindow.ui \
    formaxwidget.ui \
    dialognewproject.ui \
    dialogloadsymbol.ui \
    dialogsymbolattribute.ui \
    dialogmodifyptermial.ui \
    dialogsymbols.ui \
    dialogsymbolsort.ui \
    dialogBranchAttr.ui \
    dialogunitmanage.ui \
    dialogfuncdefine.ui \
    dialogpageattr.ui \
    dialogpagenameset.ui \
    dialogUnitAttr.ui \
    dialogterminalattr.ui \
    dialoggenerate.ui \
    dialogmultiline.ui \
    dialoglinedefine.ui \
    dialogcabledefine.ui \
    dialogconnectattr.ui \
    dialoglinkedit.ui \
    dialogsingletermattr.ui \
    dialognewspur.ui \
    dialognewlib.ui \
    dialogattrdefset.ui \
    dialogfactorymanage.ui \
    dialogfactoryedit.ui \
    dialognewfunc.ui \
    dialogtermbatchmark.ui \
    dialogdiagnoseui.ui \
    dialogfunctionmanage.ui \
    dialog_select_another_test.ui \
    dialog_wait.ui \
    dialogflurunit.ui \
    dialogsettestpreference.ui \
    dialogusertest.ui \
    dialogaddcondition.ui \
    dialogdiagusertest.ui \
    dialogaddterminal.ui \
    dialogtestreport.ui \
    dialogmultilib.ui \
    dialogtag.ui \
    widget/selectfunctiondialog.ui \
    widget/containertreedialog.ui

# Default rules for deployment.
qnx: target.path = /tmp/$${TARGET}/bin
else: unix:!android: target.path = /opt/$${TARGET}/bin
!isEmpty(target.path): INSTALLS += target

RC_ICONS = T1.ico

RESOURCES += \
    image.qrc

win32:CONFIG(release, debug|release): LIBS += -L$$PWD/./ -lqscintilla2_qt5
else:win32:CONFIG(debug, debug|release): LIBS += -L$$PWD/./ -lqscintilla2_qt5d
else:unix: LIBS += -L$$PWD/./ -lqscintilla2_qt5

INCLUDEPATH += \
        $$PWD/include/z3

LIBS += $$PWD/lib/libz3.lib

INCLUDEPATH += $$PWD/.
DEPENDPATH += $$PWD/.

