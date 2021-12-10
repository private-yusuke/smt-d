module smtd.expression;

import smtd.rational;
import std.string;
import std.range;
import std.conv;

bool instanceOf(T)(Object obj)
{
	return typeid(obj) == typeid(T);
}

class Function
{
	string name;
	/// 関数の第1引数、第2引数、…… の sort
	Sort[] inTypes;
	/// 関数の返り値の sort
	Sort outType;

	this(string name, Sort[] inTypes, Sort outType)
	{
		this.name = name;
		this.inTypes = inTypes;
		this.outType = outType;
	}

	override string toString()
	{
		return this.name;
	}
}

class Sort
{
	string name;
	ulong arity;

	this(string name, ulong arity)
	{
		this.name = name;
		this.arity = arity;
	}

	override string toString()
	{
		return this.name;
	}

	override int opCmp(Object other)
	{
		auto sort = cast(Sort) other;
		return sort && name == sort.name && arity == sort.arity;
	}
}

/// ソルバー内で入力から起こされるような式すべての基底クラス
class Expression
{
	override size_t toHash() @safe nothrow
	{
		return typeid(this).name.hashOf();
	}

	override bool opEquals(Object other)
	{
		return true;
	}
}

/*
 * 文字列を表すような式
 */
interface ExpressionWithString
{
	string stringValue();
}

/// 空リストを表す式
class EmptyExpression : Expression
{
}

@("Expression and EmptyExpression obtains hash values that only depends on the content")
unittest
{
	auto a = new Expression;
	auto b = new EmptyExpression;

	assert(a.hashOf() != b.hashOf());
	assert(a.hashOf() == (new Expression).hashOf());
	assert(b.hashOf() == (new EmptyExpression).hashOf());
}

/// 関数適用を表す式
class FunctionExpression : Expression
{
	/// 適用する関数
	Function applyingFunction;
	/// 関数の第1引数、第2引数、…… となる式
	Expression[] arguments;

	this(Function applyingFunction)
	{
		this(applyingFunction, []);
	}

	this(Function applyingFunction, Expression[] arguments)
	{
		this.applyingFunction = applyingFunction;
		this.arguments = arguments;
	}

	override string toString()
	{
		if (this.arguments.empty)
			return this.applyingFunction.toString();
		else
			return format("%s(%(%s %))", this.applyingFunction, this.arguments);
	}

	override size_t toHash() @safe nothrow
	{
		size_t argumentsHash = 0;
		foreach (arg; arguments)
		{
			argumentsHash = arg.hashOf(argumentsHash);
		}
		return applyingFunction.hashOf(argumentsHash.hashOf(typeid(this).name.hashOf()));
	}

	override bool opEquals(Object other)
	{
		FunctionExpression fExpr = cast(FunctionExpression) other;
		return fExpr && this.applyingFunction == fExpr.applyingFunction
			&& this.arguments == fExpr.arguments;
	}
}

@("FunctionExpression obtains hash values that only depends on the content")
unittest
{
	auto sortA = new Sort("A", 0);
	auto sortB = new Sort("B", 0);

	auto funcA = new Function("a", [], sortA);
	auto funcB = new Function("b", [], sortB);
	auto a = new FunctionExpression(funcA);
	auto b = new FunctionExpression(funcB);

	assert(a.hashOf() != b.hashOf());
	assert(a == new FunctionExpression(funcA));
	assert(b == new FunctionExpression(funcB));
	assert(a.hashOf() == (new FunctionExpression(funcA)).hashOf());
	assert(b.hashOf() == (new FunctionExpression(funcB)).hashOf());
}

/// sort を表す式
class SortExpression : Expression
{
	Sort sort;

	this(Sort sort)
	{
		this.sort = sort;
	}

	override bool opEquals(Object other)
	{
		auto sExpr = cast(SortExpression) other;
		return sExpr && this.sort == sExpr.sort;
	}
}

/// リストを表す式（空リストは EmptyExpression）
class ListExpression : Expression
{
	Expression[] elements;

	this(Expression[] elements)
	{
		this.elements = elements;
	}

	override string toString()
	{
		return format("(%(%s %))", elements);
	}

	override size_t toHash() @safe nothrow
	{
		import std.algorithm : reduce;

		size_t hash;
		foreach (elem; elements)
		{
			hash = elem.hashOf(hash);
		}
		return hash.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto lExpr = cast(ListExpression) other;
		return lExpr && this.elements == lExpr.elements;
	}
}

/// let 式内の変数束縛の部分を表す式
class BindExpression : Expression
{
	SymbolExpression symbol;
	Expression expr;

	this(SymbolExpression symbol, Expression expr)
	{
		this.symbol = symbol;
		this.expr = expr;
	}

	override string toString()
	{
		return format("%s := %s", this.symbol, this.expr);
	}
}

/// 既に定義された関数や sort を表すための symbol を表す式
class SymbolExpression : Expression, ExpressionWithString
{
	string name;

	this(string name)
	{
		this.name = name;
	}

	string stringValue()
	{
		return this.name;
	}

	override string toString()
	{
		return this.name;
	}

	override size_t toHash() @safe nothrow
	{
		return name.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto sExpr = cast(SymbolExpression) other;
		return sExpr && this.name == sExpr.name;
	}
}

@("SymbolExpression is capable of determining equality")
unittest
{
	auto a = new SymbolExpression("a");
	auto b = new SymbolExpression("b");

	assert(a == new SymbolExpression("a"));
	assert(b == new SymbolExpression("b"));
	assert(a != b);
}

@("SymbolExpression obtains hash values that only depends on the content")
unittest
{
	auto a = new SymbolExpression("a");
	auto b = new SymbolExpression("b");

	assert(a.hashOf() == (new SymbolExpression("a")).hashOf());
	assert(b.hashOf() == (new SymbolExpression("b")).hashOf());
	assert(a.hashOf() != b.hashOf());
}

/// 予約語の式
class KeywordExpression : Expression, ExpressionWithString
{
	string keyword;

	this(string keyword)
	{
		this.keyword = keyword;
	}

	string stringValue()
	{
		return this.keyword;
	}

	override size_t toHash() @safe nothrow
	{
		return keyword.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto kExpr = cast(KeywordExpression) other;
		return kExpr && this.keyword == kExpr.keyword;
	}
}

/// 整数値を表す式
class IntegerExpression : Expression
{
	long value;

	this(long value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto iExpr = cast(IntegerExpression) other;
		return iExpr && this.value == iExpr.value;
	}

	Rational!T toRational(T)() {
		return new Rational!T(this.value.to!T);
	}
}

/// 有理数を表す式
class RationalExpression(T) : Expression
{
	Rational!T value;

	this(Rational!T value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto rExpr = cast(RationalExpression) other;
		return rExpr && this.value == rExpr.value;
	}
}

/// 浮動小数点数を表す式
class FloatExpression : Expression
{
	float value;

	this(float value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto fExpr = cast(FloatExpression) other;
		return fExpr && this.value == fExpr.value;
	}
}

/// 文字列を表す式
class StringExpression : Expression, ExpressionWithString
{
	/// 入力されたときにどのように与えられた文字列であるか
	enum InputType
	{
		DOUBLEQUOTED,
		WYSIWYG,
		GENERATED, // 内部で生成された Expression である
	}

	string value;

	InputType inputType;

	this(string value)
	{
		this.value = value;
		this.inputType = InputType.GENERATED;
	}

	this(string value, InputType inputType)
	{
		this.value = value;
		this.inputType = inputType;
	}

	string stringValue()
	{
		return this.value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf(inputType.hashOf(typeid(this).name.hashOf()));
	}

	override bool opEquals(Object other)
	{
		auto sExpr = cast(StringExpression) other;
		return sExpr && this.value == sExpr.value && this.inputType == sExpr.inputType;
	}
}

/// 単一の引数のみ持つような関数呼び出しに見えて、その関数が予約語であった場合を表す式
class UnaryOpExpression : Expression
{
	Expression child;

	this(Expression child)
	{
		this.child = child;
	}

	override size_t toHash() @safe nothrow
	{
		return child.hashOf(typeid(this).name.hashOf());
	}

	override bool opEquals(Object other)
	{
		auto uExpr = cast(UnaryOpExpression) other;
		return uExpr && this.child == uExpr.child;
	}
}

/// 予約語 not を使った場合を表す式
class NotExpression : UnaryOpExpression
{
	this(Expression child)
	{
		super(child);
	}

	override string toString()
	{
		return format("~(%s)", this.child);
	}

	override bool opEquals(Object other)
	{
		auto nExpr = cast(NotExpression) other;
		return nExpr && this.child == nExpr.child;
	}
}

/// 2つの引数のみ持つような関数呼び出しに見えて、その関数が予約語であった場合を表す式
class BinaryOpExpression : Expression
{
	Expression lhs, rhs;

	this(Expression lhs, Expression rhs)
	{
		this.lhs = lhs;
		this.rhs = rhs;
	}

	override size_t toHash() @safe nothrow
	{
		return lhs.hashOf(rhs.hashOf(typeid(this).name.hashOf()));
	}

	override bool opEquals(Object other)
	{
		auto bExpr = cast(BinaryOpExpression) other;
		return bExpr && this.lhs == bExpr.lhs && this.rhs == bExpr.rhs;
	}
}

/**
 * 与えられた引数の位置が交換可能なアリティ2の演算子を表す式（=, and, or など）
 * このような式を特別に考えたくなるのは、= や and, or の引数の順序は実際のところ真偽に関係しないので、
 * (= x y) を (= y x) といつでも同等に考えたいという需要があるため
 * そのため、hash 値を用いて (= x y) または (= y x) のどちらかが一方の式に自動的に書き変わるようにしたい
 */
class CommutativeBinaryOpExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		if (lhs.hashOf() < rhs.hashOf())
		{
			super(lhs, rhs);
		}
		else
		{
			super(rhs, lhs);
		}
	}

	override bool opEquals(Object other)
	{
		auto cExpr = cast(CommutativeBinaryOpExpression) other;
		return cExpr && this.lhs == cExpr.lhs && this.rhs == cExpr.rhs;
	}
}

/**
 * 引数が可変長な予約済みの関数を表す式
 */
class VariadicArgumentsFunctionExpression : Expression
{
	Expression[] arguments;

	this(Expression[] arguments)
	{
		this.arguments = arguments;
	}

	override size_t toHash() @safe nothrow
	{
		import std.algorithm : reduce;

		size_t hash = 0;
		foreach (expr; this.arguments)
		{
			hash = expr.hashOf(hash);
		}
		return typeid(this).name.hashOf(hash);
	}

	override bool opEquals(Object other)
	{
		auto cExpr = cast(VariadicArgumentsFunctionExpression) other;
		return cExpr && this.arguments == cExpr.arguments;
	}
}

/**
 * 引数が可変長で交換可能な予約済みの関数を表す式
 */
class CommutativeVariadicArgumentsFunctionExpression : VariadicArgumentsFunctionExpression
{
	this(Expression[] arguments)
	{
		import std.algorithm : sort;
		import std.range : array;

		super(arguments.sort!((a, b) => a.hashOf() < b.hashOf()).array);
	}
}

/// (and lhs rhs) を表す式
class AndExpression : CommutativeVariadicArgumentsFunctionExpression
{
	this(Expression[] arguments)
	{
		super(arguments);
	}

	override string toString()
	{
		return format("%-(%s && %)", this.arguments);
	}
}

/// (or lhs rhs) を表す式
class OrExpression : CommutativeVariadicArgumentsFunctionExpression
{
	this(Expression[] arguments)
	{
		super(arguments);
	}

	override string toString()
	{
		return format("%-(%s || %)", this.arguments);
	}
}

/// (=> lhs rhs) を表す式
class ImpliesExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s => %s", this.lhs, this.rhs);
	}
}

interface ExpressionConvertibleForLRA {
	Expression toExpressionForLRA();
}

/// (= lhs rhs) を表す式
class EqualExpression : CommutativeBinaryOpExpression, ExpressionConvertibleForLRA
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s = %s", lhs.toString(), rhs.toString());
	}

	override size_t toHash() @safe nothrow
	{
		return lhs.hashOf(rhs.hashOf(typeid(this).name.hashOf()));
	}

	Expression toExpressionForLRA() {
		return new AndExpression([
			new LessThanOrEqualExpression(this.lhs, this.rhs),
			new GreaterThanOrEqualExpression(this.lhs, this.rhs),
		]);
	}
}

@("EqualExpression obtains hash values that only depends on the content")
unittest
{
	auto a = new EqualExpression(new SymbolExpression("x"), new SymbolExpression("y"));
	assert(a.hashOf() == (new EqualExpression(new SymbolExpression("x"),
			new SymbolExpression("y"))).hashOf());
	assert(a.hashOf() != (new EqualExpression(new SymbolExpression("x"),
			new SymbolExpression("z"))).hashOf());
}

@("EqualExpression with swapped expressions are considered as the same")
unittest
{
	auto a = new EqualExpression(new SymbolExpression("x"), new SymbolExpression("y"));
	auto b = new EqualExpression(new SymbolExpression("y"), new SymbolExpression("x"));
	auto c = new EqualExpression(new SymbolExpression("z"), new SymbolExpression("x"));
	assert(a == b);
	assert(a != c);
	assert(b != c);
	assert(a.hashOf() == b.hashOf());
}

@("EqualExpression implements ExpressionConvertibleForLRA")
unittest
{
	auto x = new SymbolExpression("x");
	auto y = new SymbolExpression("y");

	// (= y x)
	auto a = new EqualExpression(y, x);
	// (and (<= y x) (>= y x))
	auto b = new AndExpression([
		new LessThanOrEqualExpression(y, x),
		new GreaterThanOrEqualExpression(y, x),
	]);

	assert(a.toExpressionForLRA() == b);
}

@("AndExpression and OrExpression obtains hash values that only depends on the content")
unittest
{
	auto a = new AndExpression([new Expression, new Expression]);
	auto b = new OrExpression([new Expression, new Expression]);

	assert(a.hashOf() != b.hashOf());
	assert(a.hashOf() == (new AndExpression([new Expression, new Expression])).hashOf());
	assert(b.hashOf() == (new OrExpression([new Expression, new Expression])).hashOf());
}

/// (+ lhs rhs) を表す式
class AdditionExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s + %s", lhs.toString(), rhs.toString());
	}
}

/// (- lhs rhs) を表す式
class SubtractionExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s - %s", lhs.toString(), rhs.toString());
	}
}

/**
 * (* lhs rhs) を表す式
 * 理論によっては可換性がないかもしれない？
 */
class MultiplicationExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s * %s", lhs.toString(), rhs.toString());
	}
}

/// (/ lhs rhs) を表す式
class DivisionExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s / %s", lhs.toString(), rhs.toString());
	}
}

/// (< lhs rhs) を表す式
class LessThanExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s < %s", lhs.toString(), rhs.toString());
	}
}

/// (> lhs rhs) を表す式
class GreaterThanExpression : BinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s > %s", lhs.toString(), rhs.toString());
	}

	LessThanExpression toLessThanExpression()
	{
		return new LessThanExpression(rhs, lhs);
	}
}

// OrExpression の形に変換できるようなもの
interface OrExpressionConvertible
{
	OrExpression toOrExpression();
}

/// (<= lhs rhs) を表す式
class LessThanOrEqualExpression : BinaryOpExpression, OrExpressionConvertible
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s <= %s", lhs.toString(), rhs.toString());
	}

	OrExpression toOrExpression()
	{
		return new OrExpression([
				new LessThanExpression(lhs, rhs), new EqualExpression(lhs, rhs)
				]);
	}
}

/// (>= lhs rhs) を表す式
class GreaterThanOrEqualExpression : BinaryOpExpression, OrExpressionConvertible
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s >= %s", lhs.toString(), rhs.toString());
	}

	OrExpression toOrExpression()
	{
		return new OrExpression([
				new GreaterThanExpression(lhs, rhs), new EqualExpression(lhs, rhs)
				]);
	}

	LessThanOrEqualExpression toLessThanOrEqualExpression()
	{
		return new LessThanOrEqualExpression(rhs, lhs);
	}
}

@("Conversion from <=, >= to (< or =), (> or =)")
unittest
{
	import smtd.rational;
	import std.bigint : BigInt;

	alias RE = RationalExpression!BigInt;
	alias R = Rational!BigInt;

	auto rExpr1 = new RE(new R(5));
	auto rExpr2 = new RE(new R(3));

	auto ltExpr = new LessThanExpression(rExpr1, rExpr2);
	auto eExpr = new EqualExpression(rExpr1, rExpr2);
	auto leExpr = new LessThanOrEqualExpression(rExpr1, rExpr2);

	assert(leExpr.toOrExpression() == new OrExpression([ltExpr, eExpr]));
	assert(leExpr.toOrExpression() == new OrExpression([eExpr, ltExpr]));

	auto gtExpr = new GreaterThanExpression(rExpr1, rExpr2);
	auto geExpr = new GreaterThanOrEqualExpression(rExpr1, rExpr2);

	assert(geExpr.toOrExpression() == new OrExpression([gtExpr, eExpr]));
	assert(geExpr.toOrExpression() == new OrExpression([eExpr, gtExpr]));
}
