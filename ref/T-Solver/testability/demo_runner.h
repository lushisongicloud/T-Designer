#ifndef TESTABILITY_DEMO_RUNNER_H
#define TESTABILITY_DEMO_RUNNER_H

#include <QString>

class SQliteDatabase;

namespace testability {

bool runHydroDemo(SQliteDatabase *database, QString *log = nullptr);

}

#endif // TESTABILITY_DEMO_RUNNER_H
