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

void main()
{
	auto solver = new SMTSolver();

	char[] buf;
	while (stdin.readln(buf))
	{
		auto parseTree = SExpression(buf.to!string);
		auto expr = solver.parseTree(parseTree);
		solver.runExpression(expr);
	}

	writeln("===== eqConstraints =====");
	solver.eqConstraints.each!writeln;
	writeln("===== neqConstraints =====");
	solver.neqConstraints.each!writeln;
}

alias Pair(T) = Tuple!(T, "fst", T, "snd");

/// SMT Solver
class SMTSolver
{
	string logic;
	string[string] attributes;

	Sort[string] sorts;
	Function[string] functions;
	Pair!(Expression)[] eqConstraints;
	Pair!(Expression)[] neqConstraints;

	this()
	{
		initialize();
	}

	/// ソルバーを初期化します。
	void initialize()
	{
		const string[] keywords = [
			"declare-sort", "declare-fun", "assert", "=", "not", "set-info",
			"set-logic", "check-sat", "exit"
		];
		foreach (keyword; keywords)
		{
			functions[keyword] = new Function(keyword, null, null);
		}
	}

	/**
	 * 与えられた parse tree から Expression に変換します。
	 * [WIP] このとき、その Expression 中の式での関数適用について、ソルバーの持つ関数や sort のそれに適しているものであるか判定し、正しくなければ例外が投げられます。
	 */
	Expression parseTree(T)(T tree)
	{
		switch (tree.name)
		{
		case "SExpression.SExpr", "SExpression":
			return parseTree(tree.children[0]);
		case "SExpression.List":
			auto statements = tree.children.map!(child => parseTree(child)).array;
			if (statements.length == 0)
				return new EmptyExpression;
			string head = tree.children.front.matches.front;
			if (head == "=")
			{
				return new EqualExpression(statements[1], statements[2]);
			}
			if (head == "and")
			{
				return new AndExpression(statements[1], statements[2]);
			}
			if (head == "or")
			{
				return new OrExpression(statements[1], statements[2]);
			}
			if (head == "not")
			{
				return new NotExpression(statements[1]);
			}
			if (head in functions)
			{
				return new FunctionExpression(functions[head], statements[1 .. $]);
			}
			else
			{
				return new ListExpression(statements);
			}

			// if(tree.children.length > 1) {
			// 	auto res = new Expression;
			// 	string functionKey = tree.children.front.matches.front;
			// 	if(functionKey in functions) {
			// 		res.applyingFunction = functions[functionKey];
			// 		res.arguments = tree.children[1..$].map!(child => parseTree(child)).array;
			// 		return res;
			// 	}
			// 	throw new Exception("No such function: %s".format(functionKey));
			// }
			// if(tree.children.length == 1) {
			// 	auto res = new Expression;
			// 	res.name = tree.children.front.matches.front;
			// 	return res;
			// }

			// // returns empty Expression
			// return new Expression;
		case "SExpression.Symbol":
			string name = tree.matches.front;
			if (name in sorts)
			{
				return new SortExpression(sorts[name]);
			}
			if (name in functions)
			{
				return new FunctionExpression(functions[name]);
			}
			return new SymbolExpression(name);
		case "SExpression.Integer":
			return new IntegerExpression(tree.matches.front.to!long);
		case "SExpression.Float":
			return new FloatExpression(tree.matches.front.to!float);
		case "SExpression.Attribute":
			return new AttributeExpression(tree.matches.front);
		case "SExpression.UnaryOp",
				"SExpression.Keyword":
				return new SymbolExpression(tree.matches.front);
		default:
			throw new Exception("Unknown node: %s (%s)".format(tree.name, tree.matches.front));
		}
	}

	/**
	 * 与えられた Expression をソルバー上で処理します。
	 */
	bool runExpression(Expression expr)
	{
		if (auto fexpr = cast(FunctionExpression) expr)
		{
			switch (fexpr.applyingFunction.name)
			{
			case "assert":
				return addAssertion(fexpr.arguments[0]);
			case "declare-sort":
				auto symbolExpr = cast(SymbolExpression) fexpr.arguments[0];
				auto intExpr = cast(IntegerExpression) fexpr.arguments[1];
				return declareSort(symbolExpr.name, intExpr.value);
			case "declare-fun":
				string funcName = (cast(SymbolExpression) fexpr.arguments[0]).name;
				Sort outType = (cast(SortExpression) fexpr.arguments[2]).sort;

				// declaring a constant
				if (auto eexpr = cast(EmptyExpression) fexpr.arguments[1])
				{
					return declareFunction(funcName, [], outType);
				}
				if (auto lexpr = cast(ListExpression) fexpr.arguments[1])
				{
					Sort[] inTypes = lexpr.elements.map!(s => (cast(SortExpression) s).sort).array;
					return declareFunction(funcName, inTypes, outType);
				}
				throw new Exception("not a valid declare-fun");
				// return declareFunction(fexpr.arguments[0].name, fexpr.arguments[1].arguments.map!(v => v.name).array, expr.arguments[2].name);
			case "set-logic":
				string logicName = (cast(SymbolExpression) fexpr.arguments[0]).name;
				return setLogic(logicName);
			case "set-info":
				string name = (cast(AttributeExpression) fexpr.arguments[0]).attribution;
				string content = (cast(StringExpression) fexpr.arguments[1]).value;
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
	bool declareSort(string name, ulong arity)
	{
		if (name in sorts)
		{
			throw new Exception("Sort name duplicated; consider renaming it");
		}
		if (arity != 0)
		{
			throw new Exception("sort arith other than 0 is not yet supported");
		}
		auto s = new Sort(name, arity);
		sorts[name] = s;
		return true;
	}

	/**
	 * 新しい関数を定義します。
	 */
	bool declareFunction(string name, Sort[] inTypes, Sort outType)
	{
		if (name in functions)
		{
			throw new Exception("Function name duplicated; consider renaming it");
		}

		auto f = new Function(name, inTypes, outType);
		functions[name] = f;
		return true;
	}

	/**
	 * ソルバーで利用する理論を設定します。
	 */
	bool setLogic(string logic)
	{
		if (logic != "QF_UF")
			throw new Exception("Logic other than QF_UF is not yet supported: %s".format(logic));

		this.logic = logic;
		return true;
	}

	/**
	 * ソルバーに伝達したい補助的な情報を設定します。
	 */
	bool setInfo(string attribute, string content)
	{
		this.attributes[attribute] = content;
		return true;
	}

	/**
	 * 現在の制約を充足するような assignment が存在するか判定します。
	 */
	bool checkSat()
	{
		throw new Exception("check-sat is not yet supported");
	}

	/**
	 * ソルバーを終了します。
	 */
	bool exitSolver()
	{
		// TODO: ソルバーが完全に入力まで handle するようになったらここで main 関数に戻って return 0; する
		return true;
	}

	/**
	 * 与えられた assertion に関する Expression を見てソルバーに制約を追加します。
	 */
	bool addAssertion(Expression expr)
	{
		import satd;

		// TODO: implement
		SATBridge bridge = new SATBridge(expr);
		string strFormula = bridge.parseAssertion(expr);

		strFormula.writeln;
		expr.writeln;

		auto solver = new CDCLSolver();
		auto tseytin = tseytinTransform(strFormula);
		solver.initialize(tseytin.parseResult);
		auto res = solver.solve();
		auto literals = res.peek!(Literal[]);
		auto assignemnt = resultToOriginalVarsAssignment(tseytin, *literals);

		return true;
	}
}

class SATBridge
{
	Expression expr;
	bool[Expression] truth;
	/// SAT ソルバーに渡した変数の名前から元の Expression への対応を保持
	Expression[string] SATVarToExpr;

	this(Expression expr)
	{
		this.expr = expr;
	}

	/**
	 * 与えられた Expression を命題論理式を表した文字列に変換します。
	 */
	string parseAssertion(Expression expr)
	{
		if (auto eqExpr = cast(EqualExpression) expr)
		{
			// eq に入ったら、その中の木を hash として考えられるようにする
			string varName = format("EQ%d", expr.toHash());
			SATVarToExpr[varName] = eqExpr;
			return varName;
		}
		if (auto neqExpr = cast(NotExpression) expr)
		{
			// neq に入ったら、その中にあるであろう eq な Expression を期待する
			return format("-(%s)", this.parseAssertion(neqExpr.child));
		}
		if (auto andExpr = cast(AndExpression) expr)
		{
			return format("(%s) /\\ (%s)", this.parseAssertion(andExpr.lhs),
					this.parseAssertion(andExpr.rhs));
		}
		if (auto orExpr = cast(OrExpression) expr)
		{
			return format("(%s) \\/ (%s)", this.parseAssertion(orExpr.lhs),
					this.parseAssertion(orExpr.rhs));
		}
		throw new Exception("Unknown statement while parsing assertion: %s (%s)".format(expr,
				typeid(expr)));
	}
}
