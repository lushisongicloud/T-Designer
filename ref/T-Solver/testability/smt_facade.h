#ifndef TESTABILITY_SMT_FACADE_H
#define TESTABILITY_SMT_FACADE_H

#include <QString>
#include <QStringList>

#include "testability/testability_types.h"

class SystemEntity;

namespace testability {

class SmtFacade
{
public:
    struct CodeParts {
        QString prefix;
        QString components;
        QString extra;
    };

    SmtFacade() = default;
    explicit SmtFacade(ModelFragments fragments);

    static SmtFacade fromSystemDescription(SystemEntity &systemEntity,
                                           const QString &systemDescription);

    CodeParts renderNormalCodeParts(const QStringList &extraAssertions = {}) const;
    CodeParts renderFaultCodeParts(const QStringList &faultAssertions,
                                   const QList<ComponentOverride> &overrides,
                                   const QStringList &extraAssertions = {}) const;

    QString buildNormalCode(const QStringList &extraAssertions = {}) const;
    QString buildFaultCode(const QStringList &faultAssertions,
                           const QList<ComponentOverride> &overrides,
                           const QStringList &extraAssertions = {}) const;

    bool isSat(const QString &smtCode, int timeoutMs = -1) const;

    const ModelFragments &fragments() const { return fragments_; }

private:
    QString joinAssertions(const QStringList &assertions) const;
    QString renderComponentBlocks(const QList<ComponentOverride> &overrides) const;

    ModelFragments fragments_;
};

} // namespace testability

#endif // TESTABILITY_SMT_FACADE_H
