module smtd.expression;

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
		return fExpr && applyingFunction == fExpr.applyingFunction && arguments == fExpr.arguments;
	}
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
		return sExpr && sort == sExpr.sort;
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
		return name.hashOf(typeid(this).hashOf());
	}

	override int opCmp(Object other)
	{
		auto sExpr = cast(SymbolExpression) other;
		return sExpr && name == sExpr.name;
	}
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
}

/// 文字列を表す式
class StringExpression : Expression, ExpressionWithString
{
	/// 入力されたときにどのように与えられた文字列であるか
	enum InputType
	{
		DOUBLEQUOTED,
		WYSIWYG
	}

	string value;

	InputType inputType;

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
}

/// (and lhs rhs) を表す式
class AndExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("(%s and %s)", lhs, rhs);
	}

}

/// (or lhs rhs) を表す式
class OrExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("(%s or %s)", lhs, rhs);
	}

}

/// (= lhs rhs) を表す式
class EqualExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override string toString()
	{
		return format("%s = %s", lhs.toString(), rhs.toString());
	}
}
