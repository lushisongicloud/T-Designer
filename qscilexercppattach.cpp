#include "qscilexercppattach.h"

QscilexerCppAttach::QscilexerCppAttach(QObject *parent, bool caseInsensitiveKeywords)
{
  QsciLexerCPP(parent,caseInsensitiveKeywords);
}

QscilexerCppAttach::~QscilexerCppAttach()
{
  //~QsciLexerCPP();
}
const char * QscilexerCppAttach::keywords(int set) const
{
    //if(set == 1 || set == 3)
    //    return QsciLexerCPP::keywords(set);
    if(set == 1)
       return "TEST  VAR DEF  OF WHEN ";
    if(set == 3)
      return QsciLexerCPP::keywords(set);
    if(set == 2)
        return "PORT  VARCONNECT WITH  CONNECT ";
    return "";
}
