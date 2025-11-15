#include "BO/function/SmtSyntaxChecker.h"

#include <QByteArray>
#include <QRegularExpression>
#include <QStringList>
#include <QtGlobal>
#include <QDebug>

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
        normalized = QString("未知的 Z3 语法错误");
    }

    static const QRegularExpression mainPattern(
        QString("line\\s+(\\d+)\\s+column\\s+(\\d+)\\s*:\\s*(.*)"),
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
        const QStringList lines = normalized.split(QRegularExpression(QString("[\\r\\n]+")), QString::SkipEmptyParts);
        for (const QString &line : lines) {
            if (tryApplyPattern(line))
                break;
        }
    }

    if (result.errorMessage.isEmpty())
        result.errorMessage = normalized.trimmed();

    if (result.errorMessage.isEmpty())
        result.errorMessage = QString("Z3 返回错误但未给出详细信息");

    return result;
}
} // namespace

// 预扫描：括号与占位符
static QStringList preflightScan(const QString &script)
{
    QStringList hints;
    int line = 1;
    int column = 0; // 我们在发现错误时+1补偿为人类列号
    struct ParenInfo { QChar ch; int line; int col; };
    QVector<ParenInfo> stack;
    auto pushParen = [&](QChar ch){ stack.push_back({ch, line, column+1}); };
    auto popParen = [&](QChar ch){
        if (stack.isEmpty()) {
            hints << QString("预扫描: 在 %1:%2 发现多余的右括号 '%3'").arg(line).arg(column+1).arg(ch);
            return;
        }
        ParenInfo top = stack.last();
        if ((top.ch == '(' && ch == ')') || (top.ch == '[' && ch == ']')) {
            stack.pop_back();
        } else {
            hints << QString("预扫描: 在 %1:%2 发现不匹配的右括号 '%3' (与 %4:%5 '%6')")
                        .arg(line).arg(column+1).arg(ch)
                        .arg(top.line).arg(top.col).arg(top.ch);
            stack.pop_back();
        }
    };

    for (int i=0;i<script.size();++i) {
        QChar c = script.at(i);
        if (c == '\n') { line++; column = 0; continue; }
        column++;
        if (c == '(' || c == '[') pushParen(c);
        else if (c == ')' || c == ']') popParen(c);
    }
    for (const ParenInfo &pi : stack) {
        hints << QString("预扫描: 未闭合的左括号 '%1' (位置 %2:%3)").arg(pi.ch).arg(pi.line).arg(pi.col);
    }

    // 剩余占位符（未被替换的 %CONST%）
    static const QRegularExpression placeholderRe(QString("%[A-Za-z_][A-Za-z0-9_]*%"));
    QSet<QString> placeholders;
    auto it = placeholderRe.globalMatch(script);
    while (it.hasNext()) {
        const QRegularExpressionMatch m = it.next();
        placeholders.insert(m.captured());
    }
    if (!placeholders.isEmpty()) {
        hints << QString("预扫描: 检测到未替换占位符: %1").arg(QStringList(placeholders.values()).join(", "));
    }
    return hints;
}

static void debugDumpScript(const QString &script)
{
    // 控制输出长度，避免刷屏
    const int maxLines = 400; // 足够调试
    QStringList lines = script.split('\n');
    qDebug() << "[SmtSyntaxChecker] 最终传入 Z3 的脚本 (行数=" << lines.size() << ")";
    for (int i=0;i<lines.size() && i<maxLines; ++i) {
        qDebug().noquote() << QString("%1 | %2").arg(i+1, 4).arg(lines.at(i));
    }
    if (lines.size() > maxLines) {
        qDebug() << "[SmtSyntaxChecker] ... 截断后续";
    }
}

SmtSyntaxChecker::CheckResult SmtSyntaxChecker::check(const QString &smtText) const
{
    CheckResult result;
    const QString script = smtText;

    if (script.trimmed().isEmpty()) {
        result.success = true;
        return result;
    }

    // 预扫描（不影响是否调用 Z3，仅提供附加提示）
    const QStringList preflightHints = preflightScan(script);
    if (!preflightHints.isEmpty()) {
        // 将预扫描提示合并到最终错误信息中（仅在出现语法错误时显示）
        result.errorMessage = preflightHints.join("\n"); // 暂存，可被后续覆盖
    }

    // 调试输出完整脚本
    debugDumpScript(script);

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
        QString primary = message.isEmpty() ? g_syntaxErrorMessage : message;
        if (!result.errorMessage.isEmpty()) {
            primary.append("\n" + result.errorMessage); // 追加预扫描提示
        }
        return buildFailureResult(primary);
    }

    if (g_syntaxErrorTriggered) {
        QString primary = g_syntaxErrorMessage;
        if (!result.errorMessage.isEmpty()) {
            primary.append("\n" + result.errorMessage);
        }
        return buildFailureResult(primary);
    }

    result.success = true;
    return result;
}
