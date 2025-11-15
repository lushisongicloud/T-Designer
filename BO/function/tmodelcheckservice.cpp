#include "BO/function/tmodelcheckservice.h"

#include <algorithm>
#include <QRegularExpression>
#include <QPointer>

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
        // 新规范：不再显示功能子块层级，仅展示端号
        const QString displayName = binding.port.connNum;
        const QString joined = dirs.isEmpty() ? QString("-")
                                              : dirs.join(QString("/"));
        preview << QString("%1 (%2)").arg(displayName, joined);
        if (preview.size() >= 6)
            break;
    }
    return preview;
}

// 复用单例式非模态校验窗口
static QPointer<CodeCheckDialog> g_codeCheckDialog;
static CodeCheckDialog *ensureDialog(QWidget *parent)
{
    if (!g_codeCheckDialog) {
        g_codeCheckDialog = new CodeCheckDialog(parent);
        g_codeCheckDialog->setAttribute(Qt::WA_DeleteOnClose);
        QObject::connect(g_codeCheckDialog, &QObject::destroyed, [](){ g_codeCheckDialog = nullptr; });
    }
    return g_codeCheckDialog;
}

} // namespace

void TModelCheckService::run(QWidget *parent,
                             const QString &modelText,
                             const QList<PortInfo> &ports,
                             const TModelValidationContext &context)
{
    QList<CodeCheckDialog::Entry> entries;
    QString summary;

    // 1. 占位符与常量替换预处理
    QString expanded = modelText;
    QStringList unresolvedPlaceholders; // 未解析的 %...% 列表

    // a) 替换 %Name%
    if (!context.componentName.trimmed().isEmpty()) {
        expanded.replace(QString("%Name%"), context.componentName.trimmed());
    } else {
        // 组件名称为空时记录警告（不直接报错，允许用户后续填写）
        entries << makeEntry(CodeCheckDialog::Severity::Warning,
                              QObject::tr("未提供器件名称，%Name% 未被替换"));
    }

    // b) 直接用常量表进行替换：对每个常量键生成占位符 %key% 替换一次
    for (auto itConst = context.constants.constBegin(); itConst != context.constants.constEnd(); ++itConst) {
        const QString ph = QString("%") + itConst.key() + QString("%");
        if (expanded.contains(ph)) {
            expanded.replace(ph, itConst.value());
        }
    }

    // c) 二次扫描剩余占位符（除 %Name%），全部视为未定义常量
    static const QRegularExpression leftoverRe(QString("%([^%\n\r]+)%"));
    QRegularExpressionMatchIterator it2 = leftoverRe.globalMatch(expanded);
    while (it2.hasNext()) {
        const QRegularExpressionMatch m = it2.next();
        const QString full = m.captured();
        if (full == QString("%Name%")) // 已替换或等待组件名填写
            continue;
        unresolvedPlaceholders << full;
    }

    if (!unresolvedPlaceholders.isEmpty()) {
        // 报告未定义常量，占位符列出；此类错误将阻止后续语法解析，否则Z3会产生级联错误
        for (const QString &ph : unresolvedPlaceholders) {
            entries << makeEntry(CodeCheckDialog::Severity::Error,
                                  QObject::tr("未定义的常量占位符: %1").arg(ph));
        }
        summary = QObject::tr("常量替换阶段发现 %1 个未定义常量，占位符替换失败")
                    .arg(unresolvedPlaceholders.size());
        CodeCheckDialog *dlg = ensureDialog(parent);
        dlg->setSummary(summary);
        dlg->setEntries(entries);
        dlg->show();
        dlg->raise();
        dlg->activateWindow();
        return; // 直接返回，不再做语法与后续校验
    }

    // 2. 使用替换后的文本做语法校验（Z3只看到展开文本）
    const QString syntaxSource = expanded;

    SmtSyntaxChecker syntaxChecker;
    const SmtSyntaxChecker::CheckResult syntaxResult = syntaxChecker.check(syntaxSource);
    if (!syntaxResult.success) {
        entries << makeEntry(CodeCheckDialog::Severity::Error,
                             syntaxResult.errorMessage,
                             formatLocation(syntaxResult.errorLine, syntaxResult.errorColumn));
        summary = QObject::tr("SMT 语法校验失败");
        CodeCheckDialog *dlg = ensureDialog(parent);
        dlg->setSummary(summary);
        dlg->setEntries(entries);
        dlg->show();
        dlg->raise();
        dlg->activateWindow();
        return;
    }

    // 语义校验使用原始文本（保持 %Name% 与常量占位符形态，以便占位符规则与端口映射正则正确匹配）
    TModelValidator validator;
    const TModelValidationResult validationResult = validator.validate(modelText, ports, context);

    int errorCount = 0;
    int warningCount = 0;
    
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

    // 处理warnings（如故障模式概率未定义）
    for (const QString &warning : validationResult.warnings) {
        entries << makeEntry(CodeCheckDialog::Severity::Warning, warning);
        ++warningCount;
    }

    if (!validationResult.unusedPorts.isEmpty()) {
        entries << makeEntry(CodeCheckDialog::Severity::Warning,
                             QObject::tr("以下端号在模型中未使用: %1")
                                 .arg(validationResult.unusedPorts.join(QString(", "))));
        ++warningCount;
    }

    for (const QString &hint : validationResult.hints) {
        entries << makeEntry(CodeCheckDialog::Severity::Info, hint);
    }

    if (entries.isEmpty()) {
        entries << makeEntry(CodeCheckDialog::Severity::Info,
                             QObject::tr("所有校验项均通过"));
    } else if (errorCount == 0 && warningCount == 0) {
        // append preview info when no errors or warnings
        const QStringList preview = bindingPreview(validationResult.bindings);
        if (!preview.isEmpty()) {
            entries << makeEntry(CodeCheckDialog::Severity::Info,
                               QObject::tr("端口映射预览: %1").arg(preview.join(QString("，"))));
        }
    }

    const int portCount = ports.size();
    if (warningCount > 0) {
        summary = QObject::tr("共检查端号 %1 个，错误 %2 条，警告 %3 条")
            .arg(portCount).arg(errorCount).arg(warningCount);
    } else {
        summary = QObject::tr("共检查端号 %1 个，错误 %2 条")
            .arg(portCount).arg(errorCount);
    }

    CodeCheckDialog *dlg = ensureDialog(parent);
    dlg->setSummary(summary);
    dlg->setEntries(entries);
    dlg->show();
    dlg->raise();
    dlg->activateWindow();
}
