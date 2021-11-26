module smtd.theory_solver.lra_solver.lra_solver;

import smtd.theory_solver.common;
import smtd.expression;
import smtd.rational;
import smtd.theory_solver.lra_solver.lra_polynomial;
import smtd.theory_solver.lra_solver.rational_with_infinity;
import std.container : redBlackTree, RedBlackTree;
import std.algorithm : map, filter;
import std.range : array;

/**
 * 実数の線形算術に関する理論のソルバ
 */
class QF_LRA_Solver : TheorySolver
{
    /// 等号に関する制約
    private Expression[] eqConstraints;
    /// 不等号に関する制約
    private Expression[] neqConstraints;

    /// 置いた項からスラック変数へのマッピング
    private Expression[Expression] termToSlackVar;

    this(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        super(trueConstraints, falseConstraints);
    }

    this()
    {
        super();
    }

    override void setConstraints(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        super.setConstraints(trueConstraints, falseConstraints);

        // TODO: 実数の線形算術に関する制約を抽出したものを保持する
        this.eqConstraints = trueConstraints.filter!(c => c).array;
        this.neqConstraints = falseConstraints.filter!(c => c).array;
    }
}


/**
 * Simplex ソルバー
 * 型引数 T には、内部の計算で用いる Rational の型引数となるものを渡す（BigInt 推奨）
 */
class SimplexSolver(T)
{
    alias R = Rational!T;
    alias RWI = RationalWithInfinity!T;

    /// TODO: Specify appropriate type
    alias Variable = int;
    /**
     * スラック変数として導入されたものを含む、問題に現れるすべての変数（n 個）と、
     * スラック変数として導入された m 個の変数について、
     * ... ∧ (s_i = a_{0,i} x_0 + ... + a_{n-1,i}  x_{n-1}) ∧ ...
     * で表すことのできる Φ_A は、m × n の、成分がすべて有理数な行列 A を用いて Ax = 0 という形式で書くことができる。
     * ここで、x は \mathbb{R}^n の要素である。
     *
     * A の各行は線形独立なので、rank A = m である。
     * 与えられた問題が充足可能というのは、ここでいう Ax = 0 を満足し、かつ x が Φ' を充足する x が存在するということである。
     * Φ' は、与えられた問題 Φ の各項について、対応するスラック変数があれば、それで置き換えたものである。
     * tableau は A を表している訳ではない（A は fixed）が、tableau の初期値を定めるのに利用される。
     */
    R[Variable][Variable] tableau;

    /// 各変数の現在の値
    R[Variable] variableValue;

    /// 各変数の下限
    RWI[Variable] lowerBound;
    /// 各変数の上限
    RWI[Variable] upperBound;

    RedBlackTree!Variable basicVariables;
    RedBlackTree!Variable nonbasicVariables;

    this()
    {
        this.basicVariables = redBlackTree!Variable;
        this.nonbasicVariables = redBlackTree!Variable;
    }

    void pivot(Variable basic, Variable nonbasic)
    {
        assert(tableau[basic][nonbasic] != R(0));

        this.basicVariables.removeKey(basic);
        this.nonbasicVariables.removeKey(nonbasic);

        this.basicVariables.insert(nonbasic);
        this.nonbasicVariables.insert(basic);

    }

    void pivotAndUpdate(Variable i, Variable j, R v)
    {
        R theta = (v - variableValue[i]) / tableau[i][j];
        variableValue[i] = v;
        variableValue[j] = variableValue[j] + theta;
        foreach (k; basicVariables.filter!(v => v != i))
        {
            variableValue[k] = variableValue[k] + tableau[basicToTableauIndex[k]][j] * theta;
        }
    }

    bool assertUpper(variableValue i, R ci)
    {
        if (upperBound[i].isLessThanOrEqual(ci))
            return true;
        if (lowerBound[i].isMoreThan(ci))
            return false;
        upperBound[i] = RWI(ci);
        if (i in this.nonbasicVariables && variableValue[i] > ci)
        {
            // update(i, ci);
        }
        return true;
    }

    bool assertLower(variableValue i, R ci)
    {
        if (lowerBound[i].isMoreThanOrEqual(ci))
            return true;
        if (upperBound[i].isLessThan(ci))
            return false;
        lowerBound[i] = RWI(ci);
        if (i in this.nonbasicVariables && variableValue[i] > ci)
        {
            // update(i, ci);
        }
        return true;
    }
}
