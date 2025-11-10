#include "widget/codecheckdialog.h"
#include "ui_codecheckdialog.h"

#include <QBrush>
#include <QColor>
#include <QTreeWidgetItem>
#include <QStringList>

CodeCheckDialog::CodeCheckDialog(QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::CodeCheckDialog)
{
    ui->setupUi(this);
    setWindowTitle(tr("模型校验结果"));
    ui->treeResults->setColumnCount(3);
    QStringList headers;
    headers << tr("级别") << tr("位置") << tr("信息");
    ui->treeResults->setHeaderLabels(headers);
    ui->treeResults->setRootIsDecorated(false);
    ui->treeResults->setUniformRowHeights(true);
    ui->treeResults->setAlternatingRowColors(true);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &CodeCheckDialog::accept);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &CodeCheckDialog::reject);
}

CodeCheckDialog::~CodeCheckDialog()
{
    delete ui;
}

void CodeCheckDialog::setSummary(const QString &summary)
{
    ui->labelSummary->setText(summary);
}

void CodeCheckDialog::setEntries(const QList<Entry> &entries)
{
    ui->treeResults->clear();
    for (const Entry &entry : entries) {
        auto *item = new QTreeWidgetItem(ui->treeResults);
        item->setText(0, severityToText(entry.severity));
        item->setText(1, entry.location);
        item->setText(2, entry.message);
        const QColor color = severityToColor(entry.severity);
        if (color.isValid()) {
            item->setForeground(0, QBrush(color));
            item->setForeground(1, QBrush(color));
            item->setForeground(2, QBrush(color));
        }
    }
    for (int col = 0; col < ui->treeResults->columnCount(); ++col)
        ui->treeResults->resizeColumnToContents(col);
}

QString CodeCheckDialog::severityToText(Severity severity) const
{
    switch (severity) {
    case Severity::Error:
        return tr("错误");
    case Severity::Warning:
        return tr("警告");
    case Severity::Info:
    default:
        return tr("提示");
    }
}

QColor CodeCheckDialog::severityToColor(Severity severity) const
{
    switch (severity) {
    case Severity::Error:
        return QColor(200, 45, 45);
    case Severity::Warning:
        return QColor(200, 140, 35);
    case Severity::Info:
    default:
        return QColor();
    }
}
