#ifndef TESTDEFINITION_H
#define TESTDEFINITION_H

#include <QJsonObject>
#include <QString>
#include <QStringList>
#include <QVariantMap>

enum class TestCategory {
    Signal,
    Function,
    FaultMode
};

QString testCategoryToString(TestCategory category);
TestCategory testCategoryFromString(const QString &text);

struct GeneratedTest {
    QString id;
    TestCategory category = TestCategory::Signal;
    QString name;
    QString description;
    QString targetId;
    QStringList prerequisites;
    QStringList detectableFaults;
    QStringList isolatableFaults;
    QVariantMap metrics;
    double estimatedCost = 0.0;
    double estimatedDuration = 0.0;

    QJsonObject toJson() const;
    static GeneratedTest fromJson(const QJsonObject &object);
};

#endif // TESTDEFINITION_H
