#include "demo_runner.h"

#include <QTextStream>

#include "BO/systementity.h"
#include "DO/model.h"
#include "sqlitedatabase.h"
#include "testability/d_matrix_builder.h"
#include "testability/function_catalog.h"
#include "testability/smt_facade.h"

namespace testability {

namespace {

QString readModelLog(const QString &message)
{
    QTextStream stream(stdout);
    stream << message << endl;
    return message;
}

}

bool runHydroDemo(SQliteDatabase *database, QString *log)
{
    if (!database) {
        return false;
    }

    if (!database->connect()) {
        if (log) {
            *log = QString("数据库连接失败");
        }
        return false;
    }

    model hydroModel = database->selectModelByName(QString("Hydro"));
    if (hydroModel.getSystemDescription().isEmpty()) {
        if (log) {
            *log = QString("未找到 Hydro 模型");
        }
        return false;
    }

    SystemEntity systemEntity(database);
    systemEntity.setCurrentModel(&hydroModel);

    auto functionMap = FunctionCatalog::parse(hydroModel.getFunctionDiscription());
    systemEntity.setFunctionInfoMap(functionMap);

    SmtFacade smt = SmtFacade::fromSystemDescription(systemEntity, hydroModel.getSystemDescription());

    DMatrixBuilder builder(&systemEntity);
    builder.setFunctionInfoMap(functionMap);

    QVector<FaultDefinition> faults = builder.collectFunctionFaults();
    QVector<TestDefinition> tests = builder.collectFunctionTests();

    if (faults.isEmpty() || tests.isEmpty()) {
        if (log) {
            *log = QString("功能故障或测试为空");
        }
        return false;
    }

    const FaultDefinition *targetFault = nullptr;
    const TestDefinition *targetTest = nullptr;

    for (const auto &fault : faults) {
        for (const auto &test : tests) {
            // 通过关联功能匹配，而不是测试显示名称（名称已增加前缀）
            if (!fault.relatedFunction.isEmpty()
                && fault.relatedFunction == test.relatedFunction
                && test.kind == TestKind::Function) {
                targetFault = &fault;
                targetTest = &test;
                break;
            }
        }
        if (targetFault && targetTest) {
            break;
        }
    }

    if (!targetFault || !targetTest) {
        if (log) {
            *log = QString("未找到匹配的功能故障与测试");
        }
        return false;
    }

    DMatrixBuildOptions opts;
    DetectabilityResult result = builder.detectability(*targetFault, *targetTest,
                                                       DetectMode::Guaranteed, smt, opts);

    QString message = QString("[Hydro示例] 功能：%1\n  - 测试: %2\n  - 判定: %3\n  - 说明: %4")
            .arg(targetFault->name)
            .arg(result.method)
            .arg(result.detected ? QString("检测") : QString("未检测"))
            .arg(result.detail);

    if (log) {
        *log = message;
    } else {
        readModelLog(message);
    }

    return result.guaranteed;
}

} // namespace testability
