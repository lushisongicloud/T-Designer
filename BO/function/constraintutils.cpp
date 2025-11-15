#include "BO/function/constraintutils.h"

#include <QDebug>
#include <QRegularExpression>

namespace functionconstraints {

QString negateRange(const QString &input)
{
    QRegularExpression re;
    QRegularExpressionMatch match;

    const QString trimmed = input.trimmed();
    if (trimmed.compare(QString("true"), Qt::CaseInsensitive) == 0) {
        return QString("false");
    }
    if (trimmed.compare(QString("false"), Qt::CaseInsensitive) == 0) {
        return QString("true");
    }

    re.setPattern(R"(^\s*(-?\d+(\.\d+)?)\s*$)");
    match = re.match(trimmed);
    if (match.hasMatch()) {
        const QString valueText = match.captured(1);
        QString result = QString("smt(or (< %1 %2) (> %1 %2))");
        result.replace(QString("%2"), valueText);
        return result;
    }

    re.setPattern(R"(^\s*(\(|\[)\s*(-?\d+(\.\d+)?)\s*,\s*(-?\d+(\.\d+)?)\s*(\)|\])\s*$)");
    match = re.match(trimmed);
    if (match.hasMatch()) {
        const QString leftBracket = match.captured(1);
        const QString rightBracket = match.captured(6);
        const QString leftValue = match.captured(2);
        const QString rightValue = match.captured(4);
        const QString leftOp = (leftBracket == QLatin1String("(")) ? QString("<=") : QString("<");
        const QString rightOp = (rightBracket == QLatin1String(")")) ? QString(">=") : QString(">");

        QString result = QString("smt(or (%1 %5 %2) (%3 %5 %4))");
        result.replace(QString("%1"), leftOp);
        result.replace(QString("%2"), leftValue);
        result.replace(QString("%3"), rightOp);
        result.replace(QString("%4"), rightValue);
        result.replace(QString("%5"), QString("%1"));
        return result;
    }

    re.setPattern(R"(^\s*(>|>=|<|<=)\s*(-?\d+(\.\d+)?)\s*$)");
    match = re.match(trimmed);
    if (match.hasMatch()) {
        const QString op = match.captured(1);
        const QString valueText = match.captured(2);
        QString newOp;
        if (op == QLatin1String(">")) newOp = QString("<=");
        else if (op == QLatin1String(">=")) newOp = QString("<");
        else if (op == QLatin1String("<")) newOp = QString(">=");
        else if (op == QLatin1String("<=")) newOp = QString(">");
        return QString("%1 %2").arg(newOp, valueText);
    }

    re.setPattern(R"(^\s*smt\(\s*=\s*(.+?)\s+(.+?)\s*\)\s*$)");
    match = re.match(trimmed);
    if (match.hasMatch()) {
        const QString left = match.captured(1).trimmed();
        const QString right = match.captured(2).trimmed();
        return QString("smt(not (= %1 %2))").arg(left, right);
    }

    re.setPattern(R"(^\s*smt\(or\s*\((.*?)\)\s*\((.*?)\)\s*\)\s*$)");
    match = re.match(trimmed);
    if (match.hasMatch()) {
        QString condition = match.captured(0);
        condition.replace("> ", "#1 ");
        condition.replace("< ", "#2 ");
        condition.replace(">=", "#3 ");
        condition.replace("<=", "#4 ");
        condition.replace("#1 ", "<= ");
        condition.replace("#2 ", ">= ");
        condition.replace("#3 ", "< ");
        condition.replace("#4 ", "> ");
        condition.replace(QString("smt(or"), QString("smt(and"));
        return condition;
    }

    qDebug() << "negateRange: unexpected input" << input;
    return input;
}

} // namespace functionconstraints
