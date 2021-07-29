module smtd.app;

import smtd.statement;

import std.stdio;
import std.string;
import std.range;
import std.algorithm : map, each;
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

	Keyword < "set-option" / "not" / "and" / "or"
	UnaryOp < '='
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

alias Pair(T) = Tuple!(T, "fst", T, "snd");

/// SMT Solver
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

	/// ソルバーを初期化します。
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
				auto statements = tree.children.map!(child => parseTree(child)).array;
				if(statements.length == 0) return new EmptyStatement;
				string head = tree.children.front.matches.front;
				if(head == "=") {
					return new EqualStatement(statements[1], statements[2]);
				}
				if(head == "and") {
					return new AndStatement(statements[1], statements[2]);
				}
				if(head == "or") {
					return new OrStatement(statements[1], statements[2]);
				}
				if(head == "not") {
					return new NotStatement(statements[1]);
				}
				if(head in functions) {
					return new FunctionStatement(functions[head], statements[1..$]);
				} else {
					return new ListStatement(statements);
				}

				// if(tree.children.length > 1) {
				// 	auto res = new Statement;
				// 	string functionKey = tree.children.front.matches.front;
				// 	if(functionKey in functions) {
				// 		res.applyingFunction = functions[functionKey];
				// 		res.arguments = tree.children[1..$].map!(child => parseTree(child)).array;
				// 		return res;
				// 	}
				// 	throw new Exception("No such function: %s".format(functionKey));
				// }
				// if(tree.children.length == 1) {
				// 	auto res = new Statement;
				// 	res.name = tree.children.front.matches.front;
				// 	return res;
				// }

				// // returns empty Statement
				// return new Statement;
			case "SExpression.Symbol":
				string name = tree.matches.front;
				if(name in sorts) {
					return new SortStatement(sorts[name]);
				}
				if(name in functions) {
					return new FunctionStatement(functions[name]);
				}
				return new SymbolStatement(name);
			case "SExpression.Integer":
				return new IntegerStatement(tree.matches.front.to!long);
			case "SExpression.Float":
				return new FloatStatement(tree.matches.front.to!float);
			case "SExpression.Attribute":
				return new AttributeStatement(tree.matches.front);
			case "SExpression.UnaryOp", "SExpression.Keyword":
				return new SymbolStatement(tree.matches.front);
			default:
				throw new Exception("Unknown node: %s (%s)".format(tree.name, tree.matches.front));
		}
	}

	/**
	 * 与えられた Statement をソルバー上で処理します。
	 */
	bool runStatement(Statement stmt) {
		if(auto fstmt = cast(FunctionStatement)stmt) {
			switch(fstmt.applyingFunction.name) {
				case "assert":
					return addAssertion(fstmt.arguments[0]);
				case "declare-sort":
					auto symbolStmt = cast(SymbolStatement)fstmt.arguments[0];
					auto intStmt = cast(IntegerStatement)fstmt.arguments[1];
					return declareSort(symbolStmt.name, intStmt.value);
				case "declare-fun":
					string funcName = (cast(SymbolStatement)fstmt.arguments[0]).name;
					Sort outType = (cast(SortStatement)fstmt.arguments[2]).sort;

					// declaring a constant
					if(auto estmt = cast(EmptyStatement)fstmt.arguments[1]) {
						return declareFunction(funcName, [], outType);
					}
					if(auto lstmt = cast(ListStatement)fstmt.arguments[1]) {
						Sort[] inTypes = lstmt.elements.map!(s => (cast(SortStatement)s).sort).array;
						return declareFunction(funcName, inTypes, outType);
					}
					throw new Exception("not a valid declare-fun");
					// return declareFunction(fstmt.arguments[0].name, fstmt.arguments[1].arguments.map!(v => v.name).array, stmt.arguments[2].name);
				case "set-logic":
					string logicName = (cast(SymbolStatement)fstmt.arguments[0]).name;
					return setLogic(logicName);
				case "set-info":
					string name = (cast(AttributeStatement)fstmt.arguments[0]).attribution;
					string content = (cast(StringStatement)fstmt.arguments[1]).value;
					return setInfo(name, content);
				case "check-sat":
					return checkSat();
				case "exit":
					return exitSolver();
				default:
					assert(0);
			}
		}
		return false;
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
	bool declareFunction(string name, Sort[] inTypes, Sort outType) {
		if(name in functions) {
			throw new Exception("Function name duplicated; consider renaming it");
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
		// TODO: implement
		SATBridge bridge = new SATBridge(stmt);
		string strFormula = bridge.parseAssertion(stmt);
		strFormula.writeln;
		stmt.writeln;

		return true;
	}
}

class SATBridge {
	Statement stmt;
	bool[Statement] truth;
	/// SAT ソルバーに渡した変数の名前から元の Statement への対応を保持
	Statement[string] SATVarToStmt;

	this(Statement stmt) {
		this.stmt = stmt;
	}
	
	/**
	 * 与えられた Statement を命題論理式を表した文字列に変換します。
	 */
	string parseAssertion(Statement stmt) {
		if(auto eqStmt = cast(EqualStatement)stmt) {
			// eq に入ったら、その中の木を hash として考えられるようにする
			string varName = format("EQ%d", stmt.toHash());
			SATVarToStmt[varName] = eqStmt;
			return varName;
		}
		if(auto neqStmt = cast(NotStatement)stmt) {
			// neq に入ったら、その中にあるであろう eq な Statement を期待する
			return format("~(%s)", this.parseAssertion(neqStmt.child));
		}
		if(auto andStmt = cast(AndStatement)stmt) {
			return format("(%s) /\\ (%s)", this.parseAssertion(andStmt.lhs), this.parseAssertion(andStmt.rhs));
		}
		if(auto orStmt = cast(OrStatement)stmt) {
			return format("(%s) \\/ (%s)", this.parseAssertion(orStmt.lhs), this.parseAssertion(orStmt.rhs));
		}
		throw new Exception("Unknown statement while parsing assertion: %s (%s)".format(stmt, typeid(stmt)));
	}
}
