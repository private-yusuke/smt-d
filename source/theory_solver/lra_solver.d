module smtd.theory_solver.lra_solver;

import smtd.theory_solver.common;
import smtd.expression;
import smtd.rational;
import std.container : redBlackTree, RedBlackTree;
import std.algorithm : map, filter;
import std.range : array;

/**
 * 未解釈関数と等号に関する理論のソルバ
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

struct RationalWithInfinity(T)
{
    alias R = Rational!T;

    private R value;
    private bool _isPositiveInfinity;
    private bool _isNegativeInfinity;

    enum positiveInfinity = {
        RationalWithInfinity!T res = RationalWithInfinity!T();
        res.setPositiveInfinity();
        return res;
    }();

    enum negativeInfinity = {
        RationalWithInfinity!T res = RationalWithInfinity!T();
        res.setPositiveInfinity();
        return res;
    }();

    this(R value)
    {
        this.value = value;
    }

    void setPositiveInfinity()
    {
        this.isNegativeInfinity = false;
        this.isPositiveInfinity = true;
    }

    void setNegativeInfinity()
    {
        this.isPositiveInfinity = false;
        this.isNegativeInfinity = true;
    }

    bool isPositiveInfinity()
    {
        return this._isPositiveInfinity;
    }

    bool isNegativeInfinity()
    {
        return this._isNegativeInfinity;
    }

    bool isInfinity()
    {
        return this._isPositiveInfinity || this._isNegativeInfinity;
    }

    R getValue()
    {
        if (this.isInfinity())
        {
            throw new Exception("You can't get value from infinite ones. This is %s infinity".format(
                    this._isPositiveInfinity ? "positive" : "negative"));
        }
        return this.value;
    }

    void setValue(R value)
    {
        this.value = value;
        this._isPositiveInfinity = false;
        this._isNegativeInfinity = false;
    }

    bool isMoreThan(R r)
    {
        if (!this.isInfinity())
        {
            return this.getValue() > r;
        }
        else
            return this.isPositiveInfinity();
    }

    bool isMoreThanOrEqual(R r)
    {
        return this.isMoreThan(r) || (!this.isInfinity() && this.getValue == r);
    }

    bool isLessThan(R r)
    {
        if (!this.isInfinity())
        {
            return this.getValue() < r;
        }
        else
            return this.isNegativeInfinity();
    }

    bool isLessThanOrEqual(R r)
    {
        return this.isLessThan(r) || (!this.isInfinity() && this.getValue == r);
    }
}

/**
 * LRA の内部計算で用いる、項のデータ構造
 * a_0x_0 + ... + a_ix_i + ... の形の多項式を表現する
 * 型引数 T には、内部の計算で用いる Rational の型引数となるものを渡す（BigInt 推奨）
 */
class LRAPolynomial(T)
{
    import std.traits : Unqual;

    alias R = Rational!T;

    /// 変数名から有理数の係数へのマッピング
    /// terms[x_i] = a_i
    R[string] terms;

    this()
    {
    }

    /// 複数の項を与えて初期化
    this(R[string] terms)
    {
        this.terms = terms;
    }

    /**
     * 与えられた変数名 varName の係数を設定します。
     */
    void setCoefficient(string varName, const R coefficient)
    {
        this.terms[varName] = new R(coefficient);
    }

    /**
     * 与えられた変数名 varName の係数に値 coefficient を足します。
     */
    void addCoefficient(S)(string varName, S coefficient)
    {
        auto ptr = varName in this.terms;
        if (varName !in this.terms)
        {
            setCoefficient(varName, new R(coefficient));
        }
        else
        {
            setCoefficient(varName, this.terms[varName] + coefficient);
        }
    }

    private T addPolynomial(this T)(T rhs)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            import std.conv : to;

            newTerms[varName] = new R(coefficient);
        }
        foreach (varName, coefficient; rhs.terms)
        {
            if (varName !in newTerms)
            {
                newTerms[varName] = new R(coefficient);
            }
            else
            {
                newTerms[varName] += new R(coefficient);
            }
        }
        return new T(newTerms);
    }

    private T subtractPolynomial(this T)(T rhs)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            import std.conv : to;

            newTerms[varName] = new R(coefficient);
        }
        foreach (varName, coefficient; rhs.terms)
        {
            if (varName !in newTerms)
            {
                newTerms[varName] = new R(-coefficient);
            }
            else
            {
                newTerms[varName] -= new R(coefficient);
            }
        }
        return new T(newTerms);
    }

    private T multiplyPolynomial(this T, S)(S value)
    {
        auto res = new typeof(this);
        foreach (varName, coefficient; this.terms)
        {
            res.setCoefficient(varName, coefficient * value);
        }
        return res;
    }

    private T dividePolynomial(this T, S)(S value)
    {
        auto res = new typeof(this);
        foreach (varName, coefficient; this.terms)
        {
            res.setCoefficient(varName, coefficient / value);
        }
        return res;
    }

    /**
     * 多項式同士の加算・減算を二項演算子で行うための関数定義
     */
    auto opBinary(string op, S)(const S rhs)
            if (is(Unqual!S == Unqual!(typeof(this))))
    {
        if (op == "+")
            return this.addPolynomial(rhs);
        if (op == "-")
            return this.subtractPolynomial(rhs);
        assert(0);
    }

    /**
     * 多項式と有理数の乗算・除算を二項演算子で行うための関数定義
     */
    auto opBinary(string op, S)(const S rhs) const
    if (is(Unqual!S == Unqual!(Rational!T)))
    {
        if (op == "*")
            return this.multiplyPolynomial(rhs);
        if (op == "/")
            return this.dividePolynomial(rhs);
        assert(0);
    }

    override bool opEquals(Object other) const
    {
        auto rhs = cast(typeof(this)) other;
        return rhs && this.terms == rhs.terms;
    }

    override string toString() const
    {
        import std.string : format;
        import std.array : byPair;

        return format("%-(%s %)", this.terms.byPair.map!(
                p => format("%s[%s]", p[1], p[0])));
    }
}

@("LRAPolynomial initialization with terms returns the same object as manually initializing it")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(1),
            "b": new R(2),
            "c": new R(5),
        ]);
    L b = new L();
    b.setCoefficient("a", new R(1));
    b.setCoefficient("b", new R(2));
    b.setCoefficient("c", new R(5));

    assert(a == b);
}

@("LRAPolynomial plus LRAPolynomial returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);
    L b = new L([
            "b": new R(2),
            "c": new R(3),
            "d": new R(4),
        ]);

    assert(a + b == b + a);

    L expected = new L([
        "a": new R(2),
        "b": new R(5),
        "c": new R(7),
        "d": new R(4),
    ]);

    assert(a + b == expected);
}

@("LRAPolynomial minus LRAPolynomial returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);
    L b = new L([
            "b": new R(2),
            "c": new R(3),
            "d": new R(4),
        ]);

    assert(a - b != b - a);
    assert(a - b != a + b);

    L expected1 = new L([
        "a": new R(2),
        "b": new R(1),
        "c": new R(1),
        "d": new R(-4),
    ]);
    L expected2 = new L([
        "a": new R(-2),
        "b": new R(-1),
        "c": new R(-1),
        "d": new R(4),
    ]);

    assert(a - b == expected1);
    assert(b - a == expected2);
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
