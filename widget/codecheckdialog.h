#ifndef CODECHECKDIALOG_H
#define CODECHECKDIALOG_H

#include <QDialog>
#include <QList>
#include <QString>

namespace Ui {
class CodeCheckDialog;
}

class CodeCheckDialog : public QDialog
{
    Q_OBJECT
public:
    enum class Severity {
        Info,
        Warning,
        Error
    };

    struct Entry
    {
        Severity severity = Severity::Info;
        QString location;
        QString message;
    };

    explicit CodeCheckDialog(QWidget *parent = nullptr);
    ~CodeCheckDialog() override;

    void setSummary(const QString &summary);
    void setEntries(const QList<Entry> &entries);

private:
    QString severityToText(Severity severity) const;
    QColor severityToColor(Severity severity) const;

    Ui::CodeCheckDialog *ui;
};

#endif // CODECHECKDIALOG_H
