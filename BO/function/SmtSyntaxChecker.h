#ifndef SMT_SYNTAX_CHECKER_H
#define SMT_SYNTAX_CHECKER_H

#include <QString>

class SmtSyntaxChecker
{
public:
    struct CheckResult
    {
        bool success = false;
        QString errorMessage;
        int errorLine = -1;
        int errorColumn = -1;
    };

    SmtSyntaxChecker() = default;

    CheckResult check(const QString &smtText) const;
};

#endif // SMT_SYNTAX_CHECKER_H
