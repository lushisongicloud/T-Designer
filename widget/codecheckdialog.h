#ifndef CODECHECKDIALOG_H
#define CODECHECKDIALOG_H

#include "common.h"
#include <QDialog>
#include <QTextBrowser>
#include <QVBoxLayout>
#include <QLabel>
#include <QPushButton>
#include <QScrollArea>

struct CodeError {
    int lineNumber;
    QString codeSegment;
    QString reason;
};
class CodeCheckDialog : public QDialog
{
    Q_OBJECT

public:
    explicit CodeCheckDialog(QWidget *parent = nullptr);
    void setCheckResult(const QVector<CodeError> &errors);

private:
    QLabel *m_summaryLabel;
    QPushButton *m_detailsButton, *m_okButton;
    QScrollArea *m_scrollArea;
    QTextBrowser *m_textBrowser;
    bool m_detailsShown;

private slots:
    void toggleDetails();
};

#include <QString>
#include <QVector>
#include <QRegExp>
#include <QSet>
#include <QStringList>
#include <QStack>

class CodeChecker {
public:
    CodeChecker(const QString& code);

    QVector<CodeError> check();

private:
    QString code_;
    QSet<QString> keywords_;
    QRegExp portDefRegex_, variateDefRegex_, functionDefRegex_;

    void checkBrackets(const QString &code, QVector<CodeError> &errors) ;
    void collectVariables(const QString &line, QSet<QString> &definedVariables);
};



#endif // CODECHECKDIALOG_H
