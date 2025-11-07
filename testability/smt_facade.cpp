#include "testability/smt_facade.h"

#include <QHash>

#include "BO/systementity.h"
#include "solverrunnable.h"

namespace testability {

SmtFacade::SmtFacade(ModelFragments fragments)
    : fragments_(std::move(fragments))
{
}

SmtFacade SmtFacade::fromSystemDescription(SystemEntity &systemEntity,
                                           const QString &systemDescription)
{
    auto components = systemEntity.prepareModel(systemDescription);
    systemEntity.updateObsVarsMap(components);

    ModelFragments fragments;
    fragments.prefixCode = systemEntity.getUnchangingCode();
    fragments.components.reserve(components.size());

    for (const auto &component : components) {
        ModelFragments::ComponentBlock block;
        block.name = component.getName();
        block.normalAssertions = component.getDescription();
        block.failureModes = component.getFailMode();
        fragments.components.append(block);
    }

    return SmtFacade(std::move(fragments));
}

SmtFacade::CodeParts SmtFacade::renderNormalCodeParts(const QStringList &extraAssertions) const
{
    CodeParts parts;
    parts.prefix = fragments_.prefixCode;
    QString componentCode;
    for (const auto &component : fragments_.components) {
        componentCode += component.normalAssertions;
    }
    parts.components = componentCode;
    parts.extra = joinAssertions(extraAssertions);
    return parts;
}

SmtFacade::CodeParts SmtFacade::renderFaultCodeParts(const QStringList &faultAssertions,
                                                     const QList<ComponentOverride> &overrides,
                                                     const QStringList &extraAssertions) const
{
    CodeParts parts;
    parts.prefix = fragments_.prefixCode;
    QString componentCode = renderComponentBlocks(overrides);
    componentCode += joinAssertions(faultAssertions);
    parts.components = componentCode;
    parts.extra = joinAssertions(extraAssertions);
    return parts;
}

QString SmtFacade::buildNormalCode(const QStringList &extraAssertions) const
{
    CodeParts parts = renderNormalCodeParts(extraAssertions);
    return parts.prefix + parts.components + parts.extra;
}

QString SmtFacade::buildFaultCode(const QStringList &faultAssertions,
                                  const QList<ComponentOverride> &overrides,
                                  const QStringList &extraAssertions) const
{
    CodeParts parts = renderFaultCodeParts(faultAssertions, overrides, extraAssertions);
    return parts.prefix + parts.components + parts.extra;
}

bool SmtFacade::isSat(const QString &smtCode, int timeoutMs) const
{
    return z3Solve(smtCode, timeoutMs, nullptr);
}

QString SmtFacade::joinAssertions(const QStringList &assertions) const
{
    QString code;
    for (const auto &assertion : assertions) {
        const QString trimmed = assertion.trimmed();
        if (trimmed.isEmpty()) {
            continue;
        }
        if (trimmed.startsWith(QStringLiteral("(assert"))) {
            code += trimmed;
        } else {
            code += QStringLiteral("(assert %1)").arg(trimmed);
        }
    }
    return code;
}

QString SmtFacade::renderComponentBlocks(const QList<ComponentOverride> &overrides) const
{
    QString code;
    QHash<QString, ComponentOverride> overrideMap;
    for (const auto &overrideItem : overrides) {
        overrideMap.insert(overrideItem.componentName, overrideItem);
    }

    for (const auto &component : fragments_.components) {
        if (overrideMap.contains(component.name)) {
            const auto &overrideItem = overrideMap[component.name];
            if (!overrideItem.replaceNormal) {
                code += component.normalAssertions;
            }
            code += joinAssertions(overrideItem.assertions);
        } else {
            code += component.normalAssertions;
        }
    }

    return code;
}

} // namespace testability
