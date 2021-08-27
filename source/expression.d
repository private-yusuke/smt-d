module smtd.expression;

import smtd.app;
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
	Sort[] inTypes;
	Sort outType;

	this(string name, Sort[] inTypes, Sort outType)
	{
		this.name = name;
		this.inTypes = inTypes;
		this.outType = outType;
	}

	override string toString()
	{
		// return format("%s(%(%s, %) -> %s)", name, inTypes, outType);
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

// ソルバー内で扱われる形式
class Expression
{
	override size_t toHash() @safe nothrow
	{
		return 0;
	}

	override bool opEquals(Object other)
	{
		return true;
	}
}

class EmptyExpression : Expression
{
	override size_t toHash() @safe nothrow
	{
		return 1;
	}
}

class FunctionExpression : Expression
{
	Function applyingFunction;
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
		return applyingFunction.hashOf(argumentsHash);
	}

	override bool opEquals(Object other)
	{
		FunctionExpression fExpr = cast(FunctionExpression) other;
		return fExpr && applyingFunction == fExpr.applyingFunction && arguments == fExpr.arguments;
	}
}

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
		return hash;
	}
}

class SymbolExpression : Expression
{
	string name;

	this(string name)
	{
		this.name = name;
	}

	Sort toSort(SMTSolver solver)
	{
		return solver.sorts[name];
	}

	override string toString()
	{
		return this.name;
	}

	override size_t toHash() @safe nothrow
	{
		return name.hashOf();
	}

	override int opCmp(Object other)
	{
		auto sExpr = cast(SymbolExpression) other;
		return sExpr && name == sExpr.name;
	}
}

class AttributeExpression : Expression
{
	string attribution;

	this(string attribution)
	{
		this.attribution = attribution;
	}

	override size_t toHash() @safe nothrow
	{
		return attribution.hashOf();
	}
}

class IntegerExpression : Expression
{
	long value;

	this(long value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf();
	}
}

class FloatExpression : Expression
{
	float value;

	this(float value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf();
	}
}

class StringExpression : Expression
{
	string value;

	this(string value)
	{
		this.value = value;
	}

	override size_t toHash() @safe nothrow
	{
		return value.hashOf();
	}
}

class UnaryOpExpression : Expression
{
	Expression child;

	this(Expression child)
	{
		this.child = child;
	}

	override size_t toHash() @safe nothrow
	{
		return child.hashOf() + 1;
	}
}

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

	override size_t toHash() @safe nothrow
	{
		return child.hashOf() + 2;
	}
}

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
		return lhs.hashOf(rhs.hashOf());
	}
}

/// 与えられた引数の位置が交換可能なアリティ2の演算子を表すデータ構造
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

	override size_t toHash() @safe nothrow
	{
		return lhs.hashOf(rhs.hashOf()) + 1;
	}
}

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

	override size_t toHash() @safe nothrow
	{
		return lhs.hashOf(rhs.hashOf()) + 2;
	}
}

class EqualExpression : CommutativeBinaryOpExpression
{
	this(Expression lhs, Expression rhs)
	{
		super(lhs, rhs);
	}

	override size_t toHash() @safe nothrow
	{
		return lhs.hashOf(rhs.hashOf()) + 2;
	}

	override string toString()
	{
		return format("%s = %s", lhs.toString(), rhs.toString());
	}
}