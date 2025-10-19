#include "BO/test/testdefinition.h"

#include <QJsonArray>
#include <QtGlobal>

QString testCategoryToString(TestCategory category)
{
    switch (category) {
    case TestCategory::Signal: return QStringLiteral("signal");
    case TestCategory::Function: return QStringLiteral("function");
    case TestCategory::FaultMode: return QStringLiteral("faultMode");
    }
    return QStringLiteral("signal");
}

TestCategory testCategoryFromString(const QString &text)
{
    const QString normalized = text.trimmed().toLower();
    if (normalized == QStringLiteral("function")) return TestCategory::Function;
    if (normalized == QStringLiteral("faultmode")) return TestCategory::FaultMode;
    return TestCategory::Signal;
}

QJsonObject GeneratedTest::toJson() const
{
    QJsonObject obj;
    if (!id.isEmpty()) obj.insert(QStringLiteral("id"), id);
    obj.insert(QStringLiteral("category"), testCategoryToString(category));
    if (!name.isEmpty()) obj.insert(QStringLiteral("name"), name);
    if (!description.isEmpty()) obj.insert(QStringLiteral("description"), description);
    if (!targetId.isEmpty()) obj.insert(QStringLiteral("targetId"), targetId);
    if (!prerequisites.isEmpty()) obj.insert(QStringLiteral("prerequisites"), QJsonArray::fromStringList(prerequisites));
    if (!detectableFaults.isEmpty()) obj.insert(QStringLiteral("detectableFaults"), QJsonArray::fromStringList(detectableFaults));
    if (!isolatableFaults.isEmpty()) obj.insert(QStringLiteral("isolatableFaults"), QJsonArray::fromStringList(isolatableFaults));
    if (!metrics.isEmpty()) obj.insert(QStringLiteral("metrics"), QJsonObject::fromVariantMap(metrics));
    if (!qFuzzyIsNull(estimatedCost)) obj.insert(QStringLiteral("estimatedCost"), estimatedCost);
    if (!qFuzzyIsNull(estimatedDuration)) obj.insert(QStringLiteral("estimatedDuration"), estimatedDuration);
    return obj;
}

GeneratedTest GeneratedTest::fromJson(const QJsonObject &object)
{
    GeneratedTest test;
    test.id = object.value(QStringLiteral("id")).toString();
    test.category = testCategoryFromString(object.value(QStringLiteral("category")).toString());
    test.name = object.value(QStringLiteral("name")).toString();
    test.description = object.value(QStringLiteral("description")).toString();
    test.targetId = object.value(QStringLiteral("targetId")).toString();
    const QJsonArray prereqArray = object.value(QStringLiteral("prerequisites")).toArray();
    for (const QJsonValue &value : prereqArray)
        test.prerequisites.append(value.toString());
    const QJsonArray detectArray = object.value(QStringLiteral("detectableFaults")).toArray();
    for (const QJsonValue &value : detectArray)
        test.detectableFaults.append(value.toString());
    const QJsonArray isolateArray = object.value(QStringLiteral("isolatableFaults")).toArray();
    for (const QJsonValue &value : isolateArray)
        test.isolatableFaults.append(value.toString());
    if (object.contains(QStringLiteral("metrics")))
        test.metrics = object.value(QStringLiteral("metrics")).toObject().toVariantMap();
    if (object.contains(QStringLiteral("estimatedCost")))
        test.estimatedCost = object.value(QStringLiteral("estimatedCost")).toDouble();
    if (object.contains(QStringLiteral("estimatedDuration")))
        test.estimatedDuration = object.value(QStringLiteral("estimatedDuration")).toDouble();
    return test;
}
