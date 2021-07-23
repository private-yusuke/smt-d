import std.stdio;
import std.string;
import std.range;
import std.algorithm;
import std.conv;
import std.typecons : Tuple;
import std.exception : basicExceptionCtors;
import pegged.grammar;

mixin(grammar(`
SExpression:
	SExpr   <  Keyword / UnaryOp / Symbol / Attribute / Float / Integer / SpecialString / String / List
	Integer <~ '0' / [1-9][0-9]*
	Float   <~ ('0' / [1-9][0-9]*) '.' [0-9]*
	String  <~ '\"' [^\"]* '\"'
	SpecialString  <~ '|' .* '|'
	Symbol  <~ [a-zA-Z_$\-][a-zA-Z0-9_$\-]*
	Attribute  <~ ':' [a-zA-Z_\-][a-zA-Z0-9_\-]*
	List    < '(' SExpr* ')'

	Keyword < "set-option" / "assert" / "not"
	UnaryOp < '=' / '+' / '-'
`));

void main() {
 	auto solver = new SMTSolver();

	char[] buf;
	while (stdin.readln(buf)) {
		auto parseTree = SExpression(buf.to!string);
		auto stmt = solver.parseTree(parseTree);
		solver.runStatement(stmt);
	}

	writeln("===== eqConstraints =====");
	solver.eqConstraints.each!writeln;
	writeln("===== neqConstraints =====");
	solver.neqConstraints.each!writeln;
}

class Function {
	string name;
	string[] inTypes;
	string outType;

	this(string name, string[] inTypes, string outType) {
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
	Function applyingFunction;
	Statement[] arguments;
	string name;
	long intValue;
	float floatValue;

	override string toString() {
		if(!name.empty) return name;
		if(applyingFunction) {
			return format("%s (%(%s %))", applyingFunction.name, arguments);
		}
		if(intValue) return intValue.to!string;
		if(floatValue) return floatValue.to!string;
		return "<empty>";
	}
}

alias Pair(T) = Tuple!(T, "fst", T, "snd");

class SMTSolver {
	string logic;
	string[string] attributes;

	Sort[string] sorts;
	Function[string] functions;
	Pair!(Statement)[] eqConstraints;
	Pair!(Statement)[] neqConstraints;


	this() {
		initialize();
	}

	void initialize() {
		const string[] keywords = ["declare-sort", "declare-fun", "assert", "=", "not", "set-info", "set-logic", "check-sat", "exit"];
		foreach(keyword; keywords) {
			functions[keyword] = new Function(keyword, null, null);
		}
	}

	/**
	 * 与えられた parse tree から Statement に変換します。
	 * [WIP] このとき、その Statement 中の式での関数適用について、ソルバーの持つ関数や sort のそれに適しているものであるか判定し、正しくなければ例外が投げられます。
	 */
	Statement parseTree(T)(T tree) {
		switch(tree.name) {
			case "SExpression.SExpr", "SExpression":
				return parseTree(tree.children[0]);
			case "SExpression.List":
				if(tree.children.length > 1) {
					auto res = new Statement;
					string functionKey = tree.children.front.matches.front;
					if(functionKey in functions) {
						res.applyingFunction = functions[functionKey];
						res.arguments = tree.children[1..$].map!(child => parseTree(child)).array;
						return res;
					}
					throw new Exception("No such function: %s".format(functionKey));
				}
				if(tree.children.length == 1) {
					auto res = new Statement;
					res.name = tree.children.front.matches.front;
					return res;
				}

				// returns empty Statement
				return new Statement;
			case "SExpression.Symbol":
				auto res = new Statement;
				res.name = tree.matches.front;
				return res;
			case "SExpression.Integer":
				auto res = new Statement;
				res.intValue = tree.matches.front.to!long;
				return res;
			case "SExpression.Float":
				auto res = new Statement;
				res.floatValue = tree.matches.front.to!float;
				return res;
			case "SExpression.Attribute":
				auto res = new Statement;
				res.name = tree.matches.front[1..$];
				return res;
			default:
				throw new Exception("Unknown node: %s".format(tree.name));
		}
	}

	/**
	 * 与えられた Statement をソルバー上で処理します。
	 */
	bool runStatement(Statement stmt) {
		switch(stmt.applyingFunction.name) {
			case "assert":
				return addAssertion(stmt.arguments[0]);
			case "declare-sort":
				return declareSort(stmt.arguments[0].name, stmt.arguments[1].intValue);
			case "declare-fun":
				return declareFunction(stmt.arguments[0].name, stmt.arguments[1].arguments.map!(v => v.name).array, stmt.arguments[2].name);
			case "set-logic":
				return setLogic(stmt.arguments[0].name);
			case "set-info":
				return setInfo(stmt.arguments[0].name, stmt.arguments[1].name);
			case "check-sat":
				return checkSat();
			case "exit":
				return exitSolver();
			default:
				assert(0);
		}
	}

	/**
	 * 新しい sort を定義します。
	 * [WIP] arity が 0 以外の場合はまだサポートされていません。
	 */
	bool declareSort(string name, ulong arity) {
		if(name in sorts) {
			throw new Exception("Sort name duplicated; consider renaming it");
		}
		if(arity != 0) {
			throw new Exception("sort arith other than 0 is not yet supported");
		}
		auto s = new Sort(name, arity);
		sorts[name] = s;
		return true;
	}

	/**
	 * 新しい関数を定義します。
	 */
	bool declareFunction(string name, string[] inTypes, string outType) {
		if(name in functions) {
			throw new Exception("Function name duplicated; consider renaming it");
		}

		// Check whether all types in inTypes are actual types
		foreach(type; inTypes) {
			if(type !in sorts) {
				throw new Exception("Unknown type: %s".format(type));
			}
		}

		// Check whether outType is an actual type
		if(outType !in sorts) {
			throw new Exception("Unknown type: %s".format(outType));
		}

		auto f = new Function(name, inTypes, outType);
		functions[name] = f;
		return true;
	}

	/**
	 * ソルバーで利用する理論を設定します。
	 */
	bool setLogic(string logic) {
		if(logic != "QF_UF")
			throw new Exception("Logic other than QF_UF is not yet supported: %s".format(logic));

		this.logic = logic;
		return true;
	}

	/**
	 * ソルバーに伝達したい補助的な情報を設定します。
	 */
	bool setInfo(string attribute, string content) {
		this.attributes[attribute] = content;
		return true;
	}

	/**
	 * 現在の制約を充足するような assignment が存在するか判定します。
	 */
	bool checkSat() {
		throw new Exception("check-sat is not yet supported");
	}


	/**
	 * ソルバーを終了します。
	 */
	bool exitSolver() {
		// TODO: ソルバーが完全に入力まで handle するようになったらここで main 関数に戻って return 0; する
		return true;
	}

	/**
	 * 与えられた assertion に関する Statement を見てソルバーに制約を追加します。
	 */
	bool addAssertion(Statement stmt) {
		if(stmt.applyingFunction.name == "=") {
			eqConstraints ~= Pair!Statement(stmt.arguments[0], stmt.arguments[1]);
		} else if(stmt.applyingFunction.name == "not" && stmt.arguments[0].applyingFunction.name == "=") {
			stmt = stmt.arguments[0];
			neqConstraints ~= Pair!Statement(stmt.arguments[0], stmt.arguments[1]);
		} else throw new Exception("This statement is not yet supported for assertion: %s".format(stmt));
		return false;
	}
}

