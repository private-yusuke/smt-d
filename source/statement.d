module smtd.statement;

import smtd.app;
import std.string;
import std.range;
import std.conv;

bool instanceOf(T)(Object obj) {
	return typeid(obj) == typeid(T);
}

class Function {
	string name;
	Sort[] inTypes;
	Sort outType;

	this(string name, Sort[] inTypes, Sort outType) {
		this.name = name;
		this.inTypes = inTypes;
		this.outType = outType;
	}

	override string toString() {
		return format("Function %s(%(%s, %) -> %s)", name, inTypes, outType);
	}
}

class Sort {
	string name;
	ulong arity;

	this(string name, ulong arity) {
		this.name = name;
		this.arity = arity;
	}
}

// ソルバー内で扱われる形式
class Statement {
	// Function applyingFunction;
	// Statement[] arguments;
	// string name;
	// long intValue;
	// float floatValue;

	// override string toString() {
	// 	if(!name.empty) return name;
	// 	if(applyingFunction) {
	// 		return format("%s (%(%s %))", applyingFunction.name, arguments);
	// 	}
	// 	if(intValue) return intValue.to!string;
	// 	if(floatValue) return floatValue.to!string;
	// 	return "<empty>";
	// }
}

class EmptyStatement : Statement {
}

class FunctionStatement : Statement {
	Function applyingFunction;
	Statement[] arguments;

	this(Function applyingFunction) {
		this(applyingFunction, []);
	}

	this(Function applyingFunction, Statement[] arguments) {
		this.applyingFunction = applyingFunction;
		this.arguments = arguments;
	}
}

class SortStatement : Statement {
	Sort sort;

	this(Sort sort) {
		this.sort = sort;
	}
}

class ListStatement : Statement {
	Statement[] elements;

	this(Statement[] elements) {
		this.elements = elements;
	}
}

class SymbolStatement : Statement {
	string name;

	this(string name) {
		this.name = name;
	}

	Sort toSort(SMTSolver solver) {
		return solver.sorts[name];
	}
}

class AttributeStatement : Statement {
	string attribution;

	this(string attribution) {
		this.attribution = attribution;
	}
}

class IntegerStatement : Statement {
	long value;

	this(long value) {
		this.value = value;
	}
}

class FloatStatement : Statement {
	float value;

	this(float value) {
		this.value = value;
	}
}

class StringStatement : Statement {
	string value;

	this(string value) {
		this.value = value;
	}
}

class UnaryOpStatement : Statement {
	Statement child;

	this(Statement child) {
		this.child = child;
	}
}

class NotStatement : Statement {
}

class BinaryOpStatement : Statement {
	Statement lhs, rhs;

	this(Statement lhs, Statement rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}
}

class AndStatement : BinaryOpStatement {
	this(Statement lhs, Statement rhs) {
		super(lhs, rhs);
	}
}

class OrStatement : BinaryOpStatement {
	this(Statement lhs, Statement rhs) {
		super(lhs, rhs);
	}
}

class EqualStatement : BinaryOpStatement {
	this(Statement lhs, Statement rhs) {
		super(lhs, rhs);
	}
}
