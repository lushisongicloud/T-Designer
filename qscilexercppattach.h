#ifndef QSCILEXERCPPATTACH_H
#define QSCILEXERCPPATTACH_H

#include <QObject>
#include "Qsci/qscilexercpp.h"
class QscilexerCppAttach : public QsciLexerCPP
{

    //Q_OBJECT
public:
    QscilexerCppAttach(QObject *parent = 0, bool caseInsensitiveKeywords = false);
    ~QscilexerCppAttach();
public:
    const char *keywords(int set) const;
};

#endif // QSCILEXERCPPATTACH_H
