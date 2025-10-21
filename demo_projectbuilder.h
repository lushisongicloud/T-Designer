#ifndef DEMO_PROJECTBUILDER_H
#define DEMO_PROJECTBUILDER_H

#include <QString>

class DemoProjectBuilder
{
public:
    static bool buildDemoProject(const QString &projectDir, const QString &projectName, QString *errorMessage = nullptr);

private:
    static bool buildProjectDatabase(const QString &dbPath, QString *errorMessage);
    static bool buildModelDatabase(const QString &dbPath, QString *errorMessage);
    static bool writeSwProFile(const QString &filePath, const QString &projectName, QString *errorMessage);
    static bool writeTestParams(const QString &filePath, QString *errorMessage);

    static QString demoFunctionXml();
    static QString containerPortsJson(const QString &equipmentTag,
                                      const QString &outPort,
                                      const QString &outCategory = QStringLiteral("hydraulic"),
                                      const QString &inPort = QString(),
                                      const QString &inCategory = QStringLiteral("hydraulic"));
    static QString coilBaseTModel();
    static QString coilTModel();
    static QString elecPortTModel();
    static QString psuTModel();
    static QString psuBehaviorJson();
    static QString actuatorBehaviorJson();
    static QString subsystemBehaviorJson();
    static QStringList demoTestJsonList();
};

#endif // DEMO_PROJECTBUILDER_H
