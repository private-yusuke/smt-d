module smtd.theory_solver.common;

import smtd.expression;

/**
 * すべての理論ソルバの基底クラス
 */
class TheorySolver
{
    EqualExpression[] eqConstraints;
    EqualExpression[] neqConstraints;
    TheorySolverResult solve()
    {
        import std.string : format;

        assert(0, "You must implement `solve()` for this theory solver: %s".format(typeid(this)));
    };
}

/**
 * 理論ソルバの solve() の返り値
 */
class TheorySolverResult
{
    /// SAT だったら真、UNSAT だったら偽
    bool ok;

    /// UNSAT だったときに SAT ソルバに新規に追加してほしい制約
    Expression[] newConstraints;

    this(bool ok, Expression[] newConstraints)
    {
        this.ok = ok;
        this.newConstraints = newConstraints;
    }
}
