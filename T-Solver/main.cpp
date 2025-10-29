#include "mainwindow.h"
#include "sqlitedatabase.h"
#include "testability/demo_runner.h"

#include <QApplication>
#include <QCoreApplication>
#include <QTextStream>
#include <QStringList>

int main(int argc, char *argv[])
{
    QStringList args;
    for (int i = 1; i < argc; ++i) {
        args << QString::fromLocal8Bit(argv[i]);
    }
    qDebug()<<"main args";

    if (args.contains(QStringLiteral("--testability-demo"))) {
        QCoreApplication app(argc, argv);
        SQliteDatabase database(QStringLiteral("Model.db"));
        QString log;
        bool ok = testability::runHydroDemo(&database, &log);
        QTextStream(stdout) << log << endl;
        return ok ? 0 : 1;
    }

    QApplication a(argc, argv);
    MainWindow w;
    w.showNormal();
    return a.exec();
}
