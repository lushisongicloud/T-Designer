#include "BO/function/tmodelcheckservice.h"

#include <algorithm>

#include "BO/function/SmtSyntaxChecker.h"
#include "widget/codecheckdialog.h"

namespace {

QString formatLocation(int line, int column)
{
    if (line <= 0)
        return QString();
    if (column <= 0)
        return QString::number(line);
    return QString("%1:%2").arg(line).arg(column);
}

CodeCheckDialog::Entry makeEntry(CodeCheckDialog::Severity severity,
                                 const QString &message,
                                 const QString &location = QString())
{
    CodeCheckDialog::Entry entry;
    entry.severity = severity;
    entry.location = location;
    entry.message = message;
    return entry;
}

QStringList bindingPreview(const QVector<PortVariableBinding> &bindings)
{
    QStringList preview;
    for (const PortVariableBinding &binding : bindings) {
        QStringList dirs = binding.declaredDirections.values();
        std::sort(dirs.begin(), dirs.end());
        const QString displayName = binding.port.functionBlock.trimmed().isEmpty()
                ? binding.port.connNum
                : QString("%1.%2").arg(binding.port.functionBlock.trimmed(),
                                       binding.port.connNum);
        const QString joined = dirs.isEmpty() ? QStringLiteral("-")
                                              : dirs.join(QStringLiteral("/"));
        preview << QString("%1 (%2)").arg(displayName, joined);
        if (preview.size() >= 6)
            break;
    }
    return preview;
}

} // namespace

void TModelCheckService::run(QWidget *parent,
                             const QString &modelText,
                             const QList<PortInfo> &ports)
{
    QList<CodeCheckDialog::Entry> entries;
    QString summary;

    SmtSyntaxChecker syntaxChecker;
    const SmtSyntaxChecker::CheckResult syntaxResult = syntaxChecker.check(modelText);
    if (!syntaxResult.success) {
        entries << makeEntry(CodeCheckDialog::Severity::Error,
                             syntaxResult.errorMessage,
                             formatLocation(syntaxResult.errorLine, syntaxResult.errorColumn));
        summary = QObject::tr("SMT 语法校验失败");
        CodeCheckDialog dialog(parent);
        dialog.setSummary(summary);
        dialog.setEntries(entries);
        dialog.exec();
        return;
    }

    TModelValidator validator;
    const TModelValidationResult validationResult = validator.validate(modelText, ports);

    int errorCount = 0;
    for (const QString &msg : validationResult.formatErrors) {
        entries << makeEntry(CodeCheckDialog::Severity::Error, msg);
        ++errorCount;
    }

    for (const QString &symbol : validationResult.missingDeclarations) {
        entries << makeEntry(CodeCheckDialog::Severity::Error,
                             QObject::tr("缺少声明: %1").arg(symbol));
        ++errorCount;
    }

    for (const QString &token : validationResult.undefinedVariables) {
        entries << makeEntry(CodeCheckDialog::Severity::Error,
                             QObject::tr("未匹配的端口变量: %1").arg(token));
        ++errorCount;
    }

    if (!validationResult.unusedPorts.isEmpty()) {
        entries << makeEntry(CodeCheckDialog::Severity::Warning,
                             QObject::tr("以下端号在模型中未使用: %1")
                                 .arg(validationResult.unusedPorts.join(QStringLiteral(", "))));
    }

    for (const QString &hint : validationResult.hints) {
        entries << makeEntry(CodeCheckDialog::Severity::Info, hint);
    }

    if (entries.isEmpty()) {
        entries << makeEntry(CodeCheckDialog::Severity::Info,
                             QObject::tr("语法与端口一致性校验均通过。"));
    } else {
        // append preview info even when errors exist
        const QStringList preview = bindingPreview(validationResult.bindings);
        if (!preview.isEmpty()) {
            entries << makeEntry(CodeCheckDialog::Severity::Info,QObject::tr("端口映射预览: %1").arg(preview.join(QString("，"))));
        }
    }

    const int portCount = ports.size();
    summary = QObject::tr("共检查端号 %1 个，错误 %2 条。").arg(portCount).arg(errorCount);

    CodeCheckDialog dialog(parent);
    dialog.setSummary(summary);
    dialog.setEntries(entries);
    dialog.exec();
}
