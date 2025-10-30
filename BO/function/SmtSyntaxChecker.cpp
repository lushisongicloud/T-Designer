#include "BO/function/SmtSyntaxChecker.h"

#include <QByteArray>
#include <QRegularExpression>
#include <QStringList>
#include <QtGlobal>

#include <z3++.h>

namespace {
thread_local bool g_syntaxErrorTriggered = false;
thread_local QString g_syntaxErrorMessage;

void syntaxCheckerErrorHandler(Z3_context ctx, Z3_error_code code)
{
    Q_UNUSED(ctx);
    const char *raw = Z3_get_error_msg(ctx, code);
    g_syntaxErrorMessage = QString::fromUtf8(raw ? raw : "unknown z3 error");
    g_syntaxErrorTriggered = true;
}

SmtSyntaxChecker::CheckResult buildFailureResult(const QString &rawMessage)
{
    SmtSyntaxChecker::CheckResult result;
    result.success = false;

    QString normalized = rawMessage;
    if (normalized.isEmpty()) {
        normalized = QStringLiteral("未知的 Z3 语法错误");
    }

    static const QRegularExpression mainPattern(
        QStringLiteral("line\\s+(\\d+)\\s+column\\s+(\\d+)\\s*:\\s*(.*)"),
        QRegularExpression::CaseInsensitiveOption | QRegularExpression::DotMatchesEverythingOption);

    auto tryApplyPattern = [&](const QString &text) -> bool {
        const QRegularExpressionMatch match = mainPattern.match(text);
        if (!match.hasMatch())
            return false;
        result.errorLine = match.captured(1).toInt();
        result.errorColumn = match.captured(2).toInt();
        const QString tail = match.captured(3).trimmed();
        if (!tail.isEmpty())
            result.errorMessage = tail;
        return true;
    };

    if (!tryApplyPattern(normalized)) {
        const QStringList lines = normalized.split(QRegularExpression(QStringLiteral("[\\r\\n]+")), QString::SkipEmptyParts);
        for (const QString &line : lines) {
            if (tryApplyPattern(line))
                break;
        }
    }

    if (result.errorMessage.isEmpty())
        result.errorMessage = normalized.trimmed();

    if (result.errorMessage.isEmpty())
        result.errorMessage = QStringLiteral("Z3 返回错误但未给出详细信息");

    return result;
}
} // namespace

SmtSyntaxChecker::CheckResult SmtSyntaxChecker::check(const QString &smtText) const
{
    CheckResult result;
    const QString script = smtText;

    if (script.trimmed().isEmpty()) {
        result.success = true;
        return result;
    }

    g_syntaxErrorTriggered = false;
    g_syntaxErrorMessage.clear();

    try {
        z3::context ctx;
        Z3_set_error_handler(ctx, syntaxCheckerErrorHandler);
        z3::solver solver(ctx);
        QByteArray utf8 = script.toUtf8();
        solver.from_string(utf8.constData());
    } catch (const z3::exception &ex) {
        const QString message = QString::fromUtf8(ex.msg());
        return buildFailureResult(message.isEmpty() ? g_syntaxErrorMessage : message);
    }

    if (g_syntaxErrorTriggered) {
        return buildFailureResult(g_syntaxErrorMessage);
    }

    result.success = true;
    return result;
}
