#include "BO/behavior/z3simplifier.h"

#include <QRegularExpression>
#include <QTextStream>

#include <z3++.h>

namespace {
QString joinExpressions(const QStringList &expressions)
{
    QStringList sanitized;
    sanitized.reserve(expressions.size());
    for (const QString &expr : expressions) {
        const QString trimmed = expr.trimmed();
        if (!trimmed.isEmpty())
            sanitized.append(trimmed);
    }
    return sanitized.join(QStringLiteral("\n"));
}

QString wrapWithAssert(const QString &expression)
{
    const QString trimmed = expression.trimmed();
    if (trimmed.startsWith(QStringLiteral("(assert")))
        return trimmed;
    if (trimmed.startsWith(QStringLiteral("(declare")))
        return trimmed;
    if (trimmed.isEmpty())
        return QString();
    return QStringLiteral("(assert %1)").arg(trimmed);
}

QString makeConjunction(const QStringList &expressions)
{
    QStringList parts;
    for (const QString &expr : expressions) {
        const QString trimmed = expr.trimmed();
        if (trimmed.isEmpty()) continue;
        parts.append(trimmed);
    }
    if (parts.isEmpty())
        return QStringLiteral("true");
    if (parts.size() == 1)
        return parts.first();
    return QStringLiteral("(and %1)").arg(parts.join(QStringLiteral(" ")));
}
}

Z3Simplifier::Z3Simplifier() = default;

Z3SimplificationResult Z3Simplifier::simplifyConjunction(const QStringList &expressions,
                                                         const QStringList &eliminateSymbols) const
{
    Z3SimplificationResult result;
    QStringList cleanedExpressions;
    cleanedExpressions.reserve(expressions.size());
    for (const QString &expression : expressions) {
        const QString sanitized = sanitizeExpression(expression);
        if (!sanitized.isEmpty())
            cleanedExpressions.append(sanitized);
    }

    if (cleanedExpressions.isEmpty()) {
        result.success = true;
        result.simplifiedExpression = QStringLiteral("true");
        result.log = QStringLiteral("Z3Simplifier: 输入为空，返回 true。");
        return result;
    }

    QString conjunction = makeConjunction(cleanedExpressions);
    QString script = QStringLiteral("(set-logic ALL)\n(assert %1)").arg(conjunction);

    try {
        z3::context ctx;
        z3::solver solver(ctx);
        solver.from_string(script.toUtf8().constData());

        z3::expr_vector assertions(ctx);
        solver.assertions(assertions);
        z3::expr combined = ctx.bool_val(true);
        if (assertions.size() == 1) {
            combined = assertions[0];
        } else if (assertions.size() > 1) {
            combined = z3::mk_and(assertions);
        }

        z3::goal goal(ctx);
        goal.add(combined);

        z3::tactic simplify(ctx, "simplify");
        z3::tactic solveEqs(ctx, "solve-eqs");
        z3::tactic ctxSolve(ctx, "ctx-solver-simplify");
        z3::tactic pipeline = simplify & solveEqs & ctxSolve;
        z3::apply_result applyResult = pipeline(goal);

        QStringList eliminated;
        if (!eliminateSymbols.isEmpty()) {
            for (const QString &symbol : eliminateSymbols) {
                const QString trimmed = symbol.trimmed();
                if (!trimmed.isEmpty())
                    eliminated.append(trimmed);
            }
        }

        QString simplified;
        if (applyResult.size() > 0) {
            const z3::goal &subGoal = applyResult[0];
            if (subGoal.size() == 0) {
                simplified = QStringLiteral("true");
            } else if (subGoal.size() == 1) {
                simplified = QString::fromUtf8(subGoal[0].to_string());
            } else {
                QStringList parts;
                for (unsigned i = 0; i < subGoal.size(); ++i)
                    parts.append(QString::fromUtf8(subGoal[i].to_string()));
                simplified = QStringLiteral("(and %1)").arg(parts.join(QStringLiteral(" ")));
            }
        } else {
            simplified = QStringLiteral("true");
        }

        QTextStream stream(&result.log);
        stream << "Z3Simplifier: 输入表达式数量=" << cleanedExpressions.size() << "\n";
        stream << "原始合取: " << conjunction << "\n";
        stream << "化简后: " << simplified << "\n";
        if (!eliminated.isEmpty()) {
            stream << "已尝试消元的符号: " << eliminated.join(QStringLiteral(", ")) << "\n";
            result.eliminatedSymbols = eliminated;
        }

        result.success = true;
        result.simplifiedExpression = simplified.trimmed();

        Z3_finalize_memory();
    } catch (const z3::exception &ex) {
        result.success = false;
        result.simplifiedExpression = conjunction;
        result.log = QStringLiteral("Z3Simplifier: Z3 异常 %1").arg(QString::fromUtf8(ex.msg()));
        Z3_finalize_memory();
    }

    return result;
}

bool Z3Simplifier::isUnsat(const QStringList &assertions) const
{
    QString script = buildScriptFromExpressions(assertions);
    if (script.trimmed().isEmpty())
        return false;

    try {
        z3::context ctx;
        z3::solver solver(ctx);
        solver.from_string(script.toUtf8().constData());
        const z3::check_result res = solver.check();
        Z3_finalize_memory();
        return res == z3::unsat;
    } catch (const z3::exception &) {
        Z3_finalize_memory();
        return false;
    }
}

QString Z3Simplifier::sanitizeExpression(const QString &expression) const
{
    QString trimmed = expression.trimmed();
    if (trimmed.isEmpty())
        return QString();

    static const QRegularExpression unsupportedPattern(QStringLiteral("[\\";]"));
    if (unsupportedPattern.match(trimmed).hasMatch())
        return QString();

    return trimmed;
}

QString Z3Simplifier::buildScriptFromExpressions(const QStringList &expressions) const
{
    QStringList commands;
    commands.append(QStringLiteral("(set-logic ALL)"));
    for (const QString &expression : expressions) {
        const QString sanitized = sanitizeExpression(expression);
        if (sanitized.isEmpty())
            continue;
        const QString wrapped = wrapWithAssert(sanitized);
        if (!wrapped.isEmpty())
            commands.append(wrapped);
    }
    return joinExpressions(commands);
}
