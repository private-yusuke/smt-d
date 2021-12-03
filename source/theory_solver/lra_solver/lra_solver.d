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

    // TODO: Expression から LRAPolynomial に変換する
    // TODO: 前処理を書く（LRAPolynomial からスラック変数への mapping を用意する）
    // TODO: SimplexSolver へ前処理された入力を渡して動かすようにする
    override void setConstraints(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        // TODO: 実数の線形算術に関する制約を抽出したものを保持する
        this.eqConstraints = trueConstraints.filter!(c => c).array;
        this.neqConstraints = falseConstraints.filter!(c => c).array;
    }

    override TheorySolverResult solve()
    {
        import std.string : format;

        assert(0, "You must implement `solve()` for this theory solver: %s".format(typeid(this)));
    }
}

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

@("ExpressionToLRAPolynomialConverter toLRAPolynomial AdditionExpression")
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

@("ExpressionToLRAPolynomialConverter toLRAPolynomial SubtractionExpression")
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

@("ExpressionToLRAPolynomialConverter toLRAPolynomial MultiplicationExpression")
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

@("ExpressionToLRAPolynomialConverter toLRAPolynomial DivisionExpression")
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
