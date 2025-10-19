TEMPLATE = app
TARGET = workflow_core_tests
CONFIG += console c++11 qt testcase
QT += core testlib sql

SOURCES += \
    test_workflow_core.cpp \
    ../BO/container/containerdata.cpp \
    ../BO/container/behavioraggregator.cpp \
    ../BO/function/functiondependencyresolver.cpp \
    ../BO/function/tmodelvalidator.cpp \
    ../BO/test/testdefinition.cpp \
    ../BO/test/testgeneratorservice.cpp \
    ../BO/test/diagnosticmatrixbuilder.cpp \
    ../BO/containerrepository.cpp

INCLUDEPATH +=     ..     ../BO     ../DO     ../widget
