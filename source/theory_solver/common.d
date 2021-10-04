module smtd.theory_solver.common;

import smtd.expression;

/**
 * すべての理論ソルバの基底クラス
 */
class TheorySolver
{
    // SAT ソルバーによって真が割り当てられた制約
    private Expression[] trueConstraints;
    // SAT ソルバーによって偽が割り当てられた制約
    private Expression[] falseConstraints;

    /**
     * SAT ソルバーで真偽が定まっている制約をそれぞれ与えて初期化します。
     */
    this(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        setConstraints(trueConstraints, falseConstraints);
    }

    /**
     * 制約を持たない状態で初期化します。
     */
    this()
    {
    }

    /**
     * 理論ソルバで扱う制約を設定します。
     */
    void setConstraints(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        this.trueConstraints = trueConstraints;
        this.falseConstraints = falseConstraints;
    }

    /**
     * 理論ソルバで、設定された制約を満たすような解を求めます。解が存在する場合は返り値の ok フィールドが真になります。
     * 解が存在しない場合は返り値の ok フィールドが false になり、newConstraints に新規に追加できる制約が格納されます。
     */
    TheorySolverResult solve()
    {
        import std.string : format;

        assert(0, "You must implement `solve()` for this theory solver: %s".format(typeid(this)));
    }
}

/**
 * 理論ソルバの solve() の返り値
 */
struct TheorySolverResult
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
