#include "z3solverthread.h"

Z3SolverThread::Z3SolverThread(QObject *parent)
{

}

Z3SolverThread::~Z3SolverThread()
{

}
//QMutex mutex;
void Z3SolverThread::run()
{
    z3::context c;
    z3::solver s(c);

    s.from_string(const_cast<char*>(code.toStdString().c_str()));

    switch (s.check()) {
    case z3::check_result::unsat:
        ans = false;
        break;
    case z3::check_result::sat:
        ans = true;
        break;
    case z3::unknown:
        ans = true;
        break;
    }

    Z3_finalize_memory();
}

