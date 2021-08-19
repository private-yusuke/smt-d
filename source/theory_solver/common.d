module smtd.theory_solver.common;

import smtd.statement;

class TheorySolver
{
    EqualExpression[] eqConstraints;
    EqualExpression[] neqConstraints;
    TheorySolverResult solve()
    {
        assert(0);
    };
}

class TheorySolverResult
{
    /// SAT だったら真、UNSAT だったら偽
    bool ok;

    /// UNSAT だったときに SAT ソルバに新規に追加してほしい制約
    Expression[] newConstraints;
}
