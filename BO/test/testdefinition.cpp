#include "BO/test/testdefinition.h"

#include <QJsonArray>
#include <QtGlobal>

QString testCategoryToString(TestCategory category)
{
    switch (category) {
    case TestCategory::Signal: return QString("signal");
    case TestCategory::Function: return QString("function");
    case TestCategory::FaultMode: return QString("faultMode");
    }
    return QString("signal");
}

TestCategory testCategoryFromString(const QString &text)
{
    const QString normalized = text.trimmed().toLower();
    if (normalized == QString("function")) return TestCategory::Function;
    if (normalized == QString("faultmode")) return TestCategory::FaultMode;
    return TestCategory::Signal;
}

QJsonObject GeneratedTest::toJson() const
{
    QJsonObject obj;
    if (!id.isEmpty()) obj.insert(QString("id"), id);
    obj.insert(QString("category"), testCategoryToString(category));
    if (!name.isEmpty()) obj.insert(QString("name"), name);
    if (!description.isEmpty()) obj.insert(QString("description"), description);
    if (!targetId.isEmpty()) obj.insert(QString("targetId"), targetId);
    if (!prerequisites.isEmpty()) obj.insert(QString("prerequisites"), QJsonArray::fromStringList(prerequisites));
    if (!detectableFaults.isEmpty()) obj.insert(QString("detectableFaults"), QJsonArray::fromStringList(detectableFaults));
    if (!isolatableFaults.isEmpty()) obj.insert(QString("isolatableFaults"), QJsonArray::fromStringList(isolatableFaults));
    if (!metrics.isEmpty()) obj.insert(QString("metrics"), QJsonObject::fromVariantMap(metrics));
    if (!qFuzzyIsNull(estimatedCost)) obj.insert(QString("estimatedCost"), estimatedCost);
    if (!qFuzzyIsNull(estimatedDuration)) obj.insert(QString("estimatedDuration"), estimatedDuration);
    return obj;
}

GeneratedTest GeneratedTest::fromJson(const QJsonObject &object)
{
    GeneratedTest test;
    test.id = object.value(QString("id")).toString();
    test.category = testCategoryFromString(object.value(QString("category")).toString());
    test.name = object.value(QString("name")).toString();
    test.description = object.value(QString("description")).toString();
    test.targetId = object.value(QString("targetId")).toString();
    const QJsonArray prereqArray = object.value(QString("prerequisites")).toArray();
    for (const QJsonValue &value : prereqArray)
        test.prerequisites.append(value.toString());
    const QJsonArray detectArray = object.value(QString("detectableFaults")).toArray();
    for (const QJsonValue &value : detectArray)
        test.detectableFaults.append(value.toString());
    const QJsonArray isolateArray = object.value(QString("isolatableFaults")).toArray();
    for (const QJsonValue &value : isolateArray)
        test.isolatableFaults.append(value.toString());
    if (object.contains(QString("metrics")))
        test.metrics = object.value(QString("metrics")).toObject().toVariantMap();
    if (object.contains(QString("estimatedCost")))
        test.estimatedCost = object.value(QString("estimatedCost")).toDouble();
    if (object.contains(QString("estimatedDuration")))
        test.estimatedDuration = object.value(QString("estimatedDuration")).toDouble();
    return test;
}
