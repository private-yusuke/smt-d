module smtd.theory_solver.lra_solver.lra_solver;

import smtd.theory_solver.common;
import smtd.smt_solver : SMTSolver;
import smtd.expression;
import smtd.rational;
import smtd.theory_solver.lra_solver.lra_polynomial;
import smtd.theory_solver.lra_solver.rational_with_infinity;
import std.container : redBlackTree, RedBlackTree;
import std.algorithm : map, filter;
import std.range : array;
import std.bigint : BigInt;

/**
 * LRA ソルバ内で不等式を表すためのデータ構造
 */
class Inequality(T) {
    alias L = LRAPolynomial!T;

    /// 左辺
    L lhs;
    /// 右辺
    L rhs;
    /// このインスタンスを生成するために使用したオリジナルの式
    Expression originalExpr;

    this(L lhs, L rhs, Expression originalExpr) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.originalExpr = originalExpr;
    }

    /**
     * 左辺に変数を、右辺に定数を集めます。
     */
    void gatherVariablesToLhs() {
        // 左辺へ全てを移項
        this.lhs.minus(this.rhs);

        // 左辺に定数項があるなら、それを右辺に持ってくる
        if(this.lhs.coefficientExists(L.CONSTANT_TERM_NAME)) {
            auto coefficient = this.lhs.getCoefficient(L.CONSTANT_TERM_NAME);
            // 左辺から定数項を消す
            this.lhs.setCoefficient(L.CONSTANT_TERM_NAME, new Rational!T(0));

            // 右辺に定数項を持ってくる
            this.rhs = new L([
                L.CONSTANT_TERM_NAME: coefficient.additiveInverse(),
            ]);
        } else {
            this.rhs = new L([
                L.CONSTANT_TERM_NAME: new Rational!T(0),
            ]);
        }
    }

    @("Inequality.gatherVariablesToLhs with no constant term")
    unittest {
        alias R = Rational!BigInt;
        alias L = LRAPolynomial!BigInt;

        auto sa = new SymbolExpression("a");
        auto sb = new SymbolExpression("b");
        auto sc = new SymbolExpression("c");
        auto sd = new SymbolExpression("d");
        auto se = new SymbolExpression("e");

        auto b2 = new MultiplicationExpression(sb, new IntegerExpression(2));
        auto c3 = new MultiplicationExpression(sc, new IntegerExpression(3));
        auto c4 = new MultiplicationExpression(sc, new IntegerExpression(4));
        auto d5 = new MultiplicationExpression(sd, new IntegerExpression(5));
        auto e6 = new MultiplicationExpression(se, new IntegerExpression(6));

        auto lhs = new AdditionExpression(sa, new AdditionExpression(b2, c3));
        auto rhs = new AdditionExpression(c4, new AdditionExpression(d5, e6));
        // a + 2b + 3c < 4c + 5d + 6e
        auto lt = new LessThanExpression(lhs, rhs);

        auto ineq = toInequality!BigInt(lt);

        ineq.gatherVariablesToLhs();

        // a + 2b - c - 5d - 6e < 0
        auto expected = new LTInequality!BigInt(
            new L([
                "a": new R(1),
                "b": new R(2),
                "c": new R(-1),
                "d": new R(-5),
                "e": new R(-6),
            ]),
            new L([
                L.CONSTANT_TERM_NAME: new R(0),
            ]),
            lt
        );

        assert(ineq == expected);
    }

    @("Inequality.gatherVariablesToLhs with constant term")
    unittest {
        alias R = Rational!BigInt;
        alias L = LRAPolynomial!BigInt;

        auto sa = new SymbolExpression("a");
        auto sb = new SymbolExpression("b");

        auto b2 = new MultiplicationExpression(sb, new IntegerExpression(2));

        auto lhs = new AdditionExpression(sa, new IntegerExpression(2));
        auto rhs = new AdditionExpression(b2, new IntegerExpression(5));
        // a + 2 < 2b + 5
        auto lt = new LessThanExpression(lhs, rhs);

        auto ineq = toInequality!BigInt(lt);

        ineq.gatherVariablesToLhs();

        // a - 2b - 3 < 0
        auto expected = new LTInequality!BigInt(
            new L([
                "a": new R(1),
                "b": new R(-2),
                L.CONSTANT_TERM_NAME: new R(-3),
            ]),
            new L([
                L.CONSTANT_TERM_NAME: new R(0),
            ]),
            lt
        );

        assert(ineq == expected);
    }

    override bool opEquals(Object other) const
    {
        auto o = cast(typeof(this)) other;
        return o && this.lhs == o.lhs && this.rhs == o.rhs && this.originalExpr == o.originalExpr;
    }
}

/**
 * LRA ソルバ内で lhs > rhs を表すためのデータ構造
 */
class GTInequality(T) : Inequality!T {
    this(L lhs, L rhs, Expression originalExpr) {
        super(lhs, rhs, originalExpr);
    }

    override string toString() {
        import std.string : format;
        return format("%s > %s", this.lhs, this.rhs);
    }
}

/**
 * LRA ソルバ内で lhs < rhs を表すためのデータ構造
 */
class LTInequality(T) : Inequality!T {
    this(L lhs, L rhs, Expression originalExpr) {
        super(lhs, rhs, originalExpr);
    }

    override string toString() {
        import std.string : format;
        return format("%s < %s", this.lhs, this.rhs);
    }
}

/**
 * LRA ソルバ内で lhs >= rhs を表すためのデータ構造
 */
class LEInequality(T) : Inequality!T {
    this(L lhs, L rhs, Expression originalExpr) {
        super(lhs, rhs, originalExpr);
    }

    override string toString() {
        import std.string : format;
        return format("%s >= %s", this.lhs, this.rhs);
    }
}

/**
 * LRA ソルバ内で lhs <= rhs を表すためのデータ構造
 */
class GEInequality(T) : Inequality!T {
    this(L lhs, L rhs, Expression originalExpr) {
        super(lhs, rhs, originalExpr);
    }

    override string toString() {
        import std.string : format;
        return format("%s <= %s", this.lhs, this.rhs);
    }
}

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
    private Expression[LRAPolynomial!BigInt] termToSlackVar;

    this(Expression[] trueConstraints, Expression[] falseConstraints, SMTSolver smtSolver)
    {
        super(trueConstraints, falseConstraints, smtSolver);
    }

    this(SMTSolver smtSolver)
    {
        super(smtSolver);
    }

    // TODO: Expression から LRAPolynomial に変換する
    // TODO: 前処理を書く（LRAPolynomial からスラック変数への mapping を用意する）
    // TODO: SimplexSolver へ前処理された入力を渡して動かすようにする
    override void setConstraints(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        // 実数の線形算術に関する制約を抽出したものを保持
        // Bool 型の返り値を持つ関数など、LRA に関係ない制約はここでは扱わない
        this.eqConstraints = trueConstraints.filter!doesExpressionMatterToLRA.array;
        this.neqConstraints = falseConstraints.filter!doesExpressionMatterToLRA.array;
    }

    override TheorySolverResult solve()
    {
        import std.string : format;

        assert(0, "You must implement `solve()` for this theory solver: %s".format(typeid(this)));
    }

    /**
    * 与えられた Expression が LRA Solver で扱うべきものなら true を、そうでないなら false を返します。
    */
    private static bool doesExpressionMatterToLRA(Expression expr) {
        return cast(GreaterThanExpression) expr ||
                cast(LessThanExpression) expr ||
                cast(GreaterThanOrEqualExpression) expr ||
                cast(LessThanOrEqualExpression) expr;
    }
    @("QF_LRA_Solver.doesExpressionMatterToLRA")
    unittest {
        SymbolExpression sa = new SymbolExpression("a");
        SymbolExpression sb = new SymbolExpression("b");

        // (= a b)
        Expression a = new EqualExpression(sa, sb);
        assert(!doesExpressionMatterToLRA(a));

        // (> a b)
        Expression b = new GreaterThanExpression(sa, sb);
        assert(doesExpressionMatterToLRA(b));

        // (< a b)
        Expression c = new LessThanExpression(sa, sb);
        assert(doesExpressionMatterToLRA(c));

        // (>= a b)
        Expression d = new GreaterThanOrEqualExpression(sa, sb);
        assert(doesExpressionMatterToLRA(d));

        // (<= a b)
        Expression e = new LessThanOrEqualExpression(sa, sb);
        assert(doesExpressionMatterToLRA(e));
    }
}

/**
 * 与えられた Expression を有理数の形式に変換します。
 * IntegerExpression または FloatExpression のみ許容されます。
 * それ以外の Expression が与えられた場合には例外が発生します。
 */
static Rational!T toRational(T)(Expression expr) {
    import std.string : format;

    alias R = Rational!T;

    if(auto iExpr = cast(IntegerExpression) expr) {
        return new R(iExpr.value);
    }

    if(auto fExpr = cast(FloatExpression) expr) {
		import std.math : pow, floor;
		import std.conv : to;

		int k = 0;
		while(k <= 64) {
			float denominator = fExpr.value * pow(10, k);
			if(denominator == floor(denominator)) {
				return new Rational!T(denominator.to!long.to!T, pow(10, k).to!long.to!T);
			}
			k++;
		}
		throw new Exception("Unable to convert float value %f to Rational".format(fExpr.value));
    }
    throw new Exception("Unable to convert to Rational; unsupported type: %s".format(expr));
}

@("Convertion from IntegerExpression to Rational")
unittest {
	import std.bigint : BigInt;

	auto ie = new IntegerExpression(42);
	assert(toRational!BigInt(ie) == new Rational!BigInt(42));
}

@("Convertion from FloatExpression to Rational")
unittest {
	import std.bigint : BigInt;

	auto ie = new FloatExpression(0.325);
	assert(toRational!BigInt(ie) == new Rational!BigInt(13, 40));
}

@("Conversion from unsupported expression to Rational throws Expression")
unittest {
    import std.exception : assertThrown;
    assertThrown(toRational!BigInt(new SymbolExpression("a")));
}

/**
 * 与えられた式を再帰的に探索し、LRAPolynomial の形式に変換します。
 */
static auto toLRAPolynomial(T)(const Expression expr) {
    alias L = LRAPolynomial!T;

    import std.string : format;

    if(auto symbol = cast(SymbolExpression) expr) {
        return new L([symbol.name: new Rational!T(1)]);
    }
    if(auto iExpr = cast(IntegerExpression) expr) {
        return new L([L.CONSTANT_TERM_NAME: toRational!T(iExpr)]);
    }
    if(auto fExpr = cast(FloatExpression) expr) {
        return new L([L.CONSTANT_TERM_NAME: toRational!T(fExpr)]);
    }
    if(auto additionExpr = cast(AdditionExpression) expr) {
        auto lhs = toLRAPolynomial!T(additionExpr.lhs);
        auto rhs = toLRAPolynomial!T(additionExpr.rhs);
        return lhs.plus(rhs);
    }
    if(auto subtractionExpr = cast(SubtractionExpression) expr) {
        auto lhs = toLRAPolynomial!T(subtractionExpr.lhs);
        auto rhs = toLRAPolynomial!T(subtractionExpr.rhs);
        return lhs.minus(rhs);
    }
    if(auto multiplicationExpr = cast(MultiplicationExpression) expr) {
        auto lhs = toLRAPolynomial!T(multiplicationExpr.lhs);
        auto rhs = toLRAPolynomial!T(multiplicationExpr.rhs);

        if(lhs.containsOnlyConstant()) {
            return rhs.times(lhs.getCoefficient(L.CONSTANT_TERM_NAME));
        }
        if(rhs.containsOnlyConstant()) {
            return lhs.times(rhs.getCoefficient(L.CONSTANT_TERM_NAME));
        }
        throw new Exception("Invalid multiplication; both terms contain variable: %s and %s".format(lhs, rhs));
    }
    if(auto divisionExpr = cast(DivisionExpression) expr) {
        auto lhs = toLRAPolynomial!T(divisionExpr.lhs);
        auto rhs = toLRAPolynomial!T(divisionExpr.rhs);

        if(rhs.containsOnlyConstant()) {
            return lhs.dividedBy(rhs.getCoefficient(L.CONSTANT_TERM_NAME));
        }
        throw new Exception("Dividing a term with a term containing variable is not allowed: %s / %s".format(lhs, rhs));
    }

    throw new Exception("This expression can not be converted to LRAPolynomial: %s".format(expr));
    assert(0);
}

@("toLRAPolynomial AdditionExpression")
unittest {
    import std.bigint : BigInt;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    auto a = new AdditionExpression(
        new SymbolExpression("x"),
        new IntegerExpression(10)
    );

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    assert(toLRAPolynomial!BigInt(a) == new L(["x": new R(1), CONSTANT_TERM_NAME: new R(10)]));
}

@("toLRAPolynomial SubtractionExpression")
unittest {
    import std.bigint : BigInt;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    auto a = new SubtractionExpression(
        new SymbolExpression("x"),
        new IntegerExpression(10)
    );

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    assert(toLRAPolynomial!BigInt(a) == new L(["x": new R(1), CONSTANT_TERM_NAME: new R(-10)]));
}

@("toLRAPolynomial MultiplicationExpression")
unittest {
    import std.bigint : BigInt;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    auto a = new MultiplicationExpression(
        new SymbolExpression("x"),
        new IntegerExpression(10)
    );
    assert(toLRAPolynomial!BigInt(a) == new L(["x": new R(10)]));

    auto b = new MultiplicationExpression(
        new IntegerExpression(10),
        new SymbolExpression("x")
    );
    assert(toLRAPolynomial!BigInt(b) == new L(["x": new R(10)]));

    auto c = new MultiplicationExpression(
        new IntegerExpression(10),
        new FloatExpression(10.25)
    );
    assert(toLRAPolynomial!BigInt(c) == new L([CONSTANT_TERM_NAME: new R(205, 2)]));

    auto d = new MultiplicationExpression(
        new SymbolExpression("x"),
        new SymbolExpression("x")
    );
    import std.exception : assertThrown;
    assertThrown(toLRAPolynomial!BigInt(d));
}

@("toLRAPolynomial DivisionExpression")
unittest {
    import std.bigint : BigInt;
    import std.exception : assertThrown;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    auto a = new DivisionExpression(
        new SymbolExpression("x"),
        new IntegerExpression(10)
    );
    assert(toLRAPolynomial!BigInt(a) == new L(["x": new R(1, 10)]));

    auto b = new DivisionExpression(
        new IntegerExpression(10),
        new SymbolExpression("x")
    );
    assertThrown(toLRAPolynomial!BigInt(b));

    auto c = new DivisionExpression(
        new IntegerExpression(10),
        new FloatExpression(1.25)
    );
    assert(toLRAPolynomial!BigInt(c) == new L([CONSTANT_TERM_NAME: new R(8)]));

    auto d = new DivisionExpression(
        new SymbolExpression("x"),
        new SymbolExpression("x")
    );
    assertThrown(toLRAPolynomial!BigInt(d));
}

@("toLRAPolynomial with complicated expression")
unittest {
    import std.bigint : BigInt;
    import std.exception : assertThrown;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    auto as = new SymbolExpression("a");
    auto bs = new SymbolExpression("b");

    auto i2 = new IntegerExpression(2);
    auto i3 = new IntegerExpression(3);

    auto a2 = new MultiplicationExpression(i2, as);
    auto b3 = new MultiplicationExpression(bs, i3);

    // 2a + 3b
    auto plus1 = new AdditionExpression(a2, b3);

    // 3(2a + 3b)
    auto mult1 = new MultiplicationExpression(i3, plus1);

    // 3 - 3(2a + 3b)
    auto minus1 = new SubtractionExpression(i3, mult1);

    // 3 - 6a - 9b
    L expected1 = new L([
        CONSTANT_TERM_NAME: new R(3),
        "a": new R(-6),
        "b": new R(-9),
    ]);

    assert(toLRAPolynomial!BigInt(minus1) == expected1);

    // (3 - 6a - 9b) / 2 = 3/2 - 3a - 9/2b
    auto div1 = new DivisionExpression(minus1, i2);
    // (3/2 - 3a - 9/2b) / 3 = 1/2 - a - 3/2b
    auto div2 = new DivisionExpression(div1, i3);

    // 1/2 - a - 3/2b
    L expected2 = new L([
        CONSTANT_TERM_NAME: new R(1, 2),
        "a": new R(-1),
        "b": new R(-3, 2),
    ]);

    assert(toLRAPolynomial!BigInt(div2) == expected2);
}

/**
 * 不等式を表す Expression を Inequality を継承したクラスのインスタンスに変換します。
 */
static Inequality!T toInequality(T)(Expression expr) {
    if (auto gtExpr = cast(GreaterThanExpression) expr) {
        auto lhs = toLRAPolynomial!T(gtExpr.lhs);
        auto rhs = toLRAPolynomial!T(gtExpr.rhs);

        return new GTInequality!T(lhs, rhs, expr);
    }
    if (auto ltExpr = cast(LessThanExpression) expr) {
        auto lhs = toLRAPolynomial!T(ltExpr.lhs);
        auto rhs = toLRAPolynomial!T(ltExpr.rhs);

        return new LTInequality!T(lhs, rhs, expr);
    }
    if (auto geExpr = cast(GreaterThanOrEqualExpression) expr) {
        auto lhs = toLRAPolynomial!T(geExpr.lhs);
        auto rhs = toLRAPolynomial!T(geExpr.rhs);

        return new GEInequality!T(lhs, rhs, expr);
    }
    if (auto leExpr = cast(LessThanOrEqualExpression) expr) {
        auto lhs = toLRAPolynomial!T(leExpr.lhs);
        auto rhs = toLRAPolynomial!T(leExpr.rhs);

        return new LEInequality!T(lhs, rhs, expr);
    }

    import std.string : format;
    throw new Exception("This expression is not representing inequality: %s".format(expr));
}

@("toInequality")
unittest {
    import std.bigint : BigInt;
    import std.exception : assertThrown;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    const string CONSTANT_TERM_NAME = L.CONSTANT_TERM_NAME;

    auto as = new SymbolExpression("a");
    auto bs = new SymbolExpression("b");

    auto a3 = new MultiplicationExpression(new IntegerExpression(3), as);
    auto b2 = new MultiplicationExpression(new IntegerExpression(2), bs);

    // 3a < 2b
    {
        auto le = new LessThanExpression(a3, b2);
        auto expected = new LTInequality!BigInt(
            new L([
                "a": new R(3),
            ]),
            new L([
                "b": new R(2),
            ]),
            le
        );
        assert(toInequality!BigInt(le) == expected);
    }
    // 3a > 2b
    {
        auto gt = new GreaterThanExpression(a3, b2);
        auto expected = new GTInequality!BigInt(
            new L([
                "a": new R(3),
            ]),
            new L([
                "b": new R(2),
            ]),
            gt
        );
        assert(toInequality!BigInt(gt) == expected);
    }
    // 3a <= 2b
    {
        auto le = new LessThanOrEqualExpression(a3, b2);
        auto expected = new LEInequality!BigInt(
            new L([
                "a": new R(3),
            ]),
            new L([
                "b": new R(2),
            ]),
            le
        );
        assert(toInequality!BigInt(le) == expected);
    }
    // 3a >= 2b
    {
        auto ge = new GreaterThanOrEqualExpression(a3, b2);
        auto expected = new GEInequality!BigInt(
            new L([
                "a": new R(3),
            ]),
            new L([
                "b": new R(2),
            ]),
            ge
        );
        assert(toInequality!BigInt(ge) == expected);
    }

    // Wrong argument
    import std.exception : assertThrown;
    assertThrown(toInequality!BigInt(new EqualExpression(as, bs)));
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
