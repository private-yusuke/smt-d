module smtd.theory_solver.common;

import smtd.expression;
import smtd.smt_solver : SMTSolver;

/**
 * すべての理論ソルバの基底クラス
 */
class TheorySolver
{
    // SAT ソルバーによって真が割り当てられた制約
    private Expression[] trueConstraints;
    // SAT ソルバーによって偽が割り当てられた制約
    private Expression[] falseConstraints;
    // 呼び出し元の SMT ソルバーのインスタンス
    SMTSolver smtSolver;

    /**
     * SAT ソルバーで真偽が定まっている制約をそれぞれ与えて初期化します。
     */
    this(Expression[] trueConstraints, Expression[] falseConstraints, SMTSolver smtSolver)
    {
        setConstraints(trueConstraints, falseConstraints);
        this.smtSolver = smtSolver;
    }

    /**
     * 制約を持たない状態で初期化します。
     */
    this(SMTSolver smtSolver)
    {
        this.smtSolver = smtSolver;
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

/**
 * 理論によって指定できる前処理用クラス
 */
interface TheorySolverPreprocessor {
    /// 与えられた式を置換等によって前処理したものを返します。返す式は元のものでない可能性があります。
    Expression preprocess(Expression expr);
}