#ifndef TESTABILITY_FUNCTION_CATALOG_H
#define TESTABILITY_FUNCTION_CATALOG_H

#include <QMap>
#include <QString>

#include "BO/function/functioninfo.h"

namespace testability {

class FunctionCatalog
{
public:
    static QMap<QString, FunctionInfo> parse(const QString &functionDescriptionXml);
};

} // namespace testability

#endif // TESTABILITY_FUNCTION_CATALOG_H
