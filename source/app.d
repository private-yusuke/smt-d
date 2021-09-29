module smtd.app;

import smtd.expression;
import smtd.theory_solver;

import std.stdio;
import std.string;
import std.range;
import std.algorithm : map, each, filter;
import std.conv;
import std.typecons : Tuple;
import std.exception : basicExceptionCtors;
import pegged.grammar;
import satd.solvers.cdcl;
import satd.cnf : Literal;
import satd.tseytin : tseytinTransform, resultToOriginalVarsAssignment;

const string[] keywords = [
	"set-option", "not", "and", "or", "declare-sort", "declare-fun",
	"declare-const", "assert", "=", "not", "set-info", "set-logic", "check-sat",
	"exit"
];

mixin(grammar(`
SExpression:
	Grammar < SExpr+
	SExpr   <  ReservedWord / UnaryOp / Symbol / Keyword / Float / Integer / String / List
	Integer <- '0' / [1-9][0-9]*
	Float   <- ('0' / [1-9][0-9]*) '.' [0-9]*
	String  < DoublequotedString / WysiwygString
	DoublequotedString <~ :doublequote (!doublequote Char)* :doublequote
	WysiwygString <~ :'|' (!'|' WysiwygChar)* :'|'
	Symbol  <~ !ReservedWord [a-zA-Z_$\-][a-zA-Z0-9_$\-]*
	Keyword  <~ :':' !ReservedWord [a-zA-Z_\-][a-zA-Z0-9_\-]*
	List    <- '(' SExpr* ')'

	ReservedWord <  %-(%s / %)
	UnaryOp < '='
	Char    <~ backslash ( doublequote
					  / quote
					  / backslash
					  )
					  / .
	WysiwygChar <- . / ' ' / '\t' / '\r\n' / '\n' / '\r'
`.format(keywords.map!(s => `"` ~ s ~ `"`))));

const auto content = `(set-logic QF_UF)
(set-option :produce-models true)
(set-info :category "crafted")
(set-info :keyword |
test|)
(declare-sort |U| 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun f (U U) U)
(assert (= (f a b) a))
(check-sat)
(assert (not (= (f (f a b) b) a)))
(assert (let ((v1 (f a b))) (= v1 v1)))
(check-sat)`;

void main()
{
	auto solver = new SMTSolver();

	auto parseTree = SExpression(content);
	foreach (sExpr; parseTree.children.front.children)
	{
		auto expr = solver.parseTree(sExpr);
		solver.runExpression(expr);
	}
}

alias Pair(T) = Tuple!(T, "fst", T, "snd");

/// SMT Solver
class SMTSolver
{
	/// set-logic で与えられた、現在扱う理論
	string logic;
	/// set-info で与えられた補助的な情報
	string[string] info;

	Sort[string] sorts;
	Function[string] functions;
	Expression[] eqConstraints;
	Expression[] neqConstraints;
	SATBridge satBridge;
	TheorySolver tSolver;

	this()
	{
		initialize();
	}

	/// ソルバーを初期化します。
	void initialize()
	{
		const string[] keywords = [
			"declare-sort", "declare-fun", "declare-const", "assert", "=",
			"not", "set-info", "set-logic", "check-sat", "exit"
		];
		foreach (keyword; keywords)
		{
			functions[keyword] = new Function(keyword, null, null);
		}

		this.satBridge = new SATBridge();
	}

	/**
	 * 与えられた parse tree から Expression に変換します。
	 * [WIP] このとき、その Expression 中の式での関数適用について、ソルバーの持つ関数や sort のそれに適しているものであるか判定し、正しくなければ例外が投げられます。
	 */
	Expression parseTree(T)(T tree)
	{
		switch (tree.name)
		{
		case "SExpression.SExpr", "SExpression.Grammar",
				"SExpression":
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
			if (head == "let")
			{
				return expandLet(cast(ListExpression) statements[1], statements[2]);
			}
			if (head in functions)
			{
				return new FunctionExpression(functions[head], statements[1 .. $]);
			}
			else
			{
				return new ListExpression(statements);
			}
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
		case "SExpression.Keyword":
			return new KeywordExpression(tree.matches.front);
		case "SExpression.UnaryOp",
				"SExpression.ReservedWord":
				return new SymbolExpression(tree.matches.front);
		case "SExpression.String":
			return parseTree(tree.children[0]);
		case "SExpression.DoublequotedString":
			return new StringExpression(tree.matches.front, StringExpression.InputType.DOUBLEQUOTED);
		case "SExpression.WysiwygString":
			return new StringExpression(tree.matches.front.strip,
					StringExpression.InputType.WYSIWYG);
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
				auto exprWithString = cast(ExpressionWithString) fexpr.arguments[0];
				auto intExpr = cast(IntegerExpression) fexpr.arguments[1];
				return declareSort(exprWithString.stringValue, intExpr.value);
			case "declare-fun":
				string funcName = (cast(ExpressionWithString) fexpr.arguments[0]).stringValue;
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
				string name = (cast(KeywordExpression) fexpr.arguments[0]).keyword;
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
			throw new Exception("sort arity other than 0 is not yet supported");
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
		this.tSolver = getTheorySolver(logic);
		this.logic = logic;
		return true;
	}

	private TheorySolver getTheorySolver(string logic)
	{
		switch (logic)
		{
		case "QF_UF":
			return new QF_UF_Solver();
		default:
			throw new Exception("Logic other than QF_UF is not yet supported: %s".format(logic));
		}
	}

	/**
	 * ソルバーに伝達したい補助的な情報を設定します。
	 */
	bool setInfo(string keyword, string content)
	{
		this.info[keyword] = content;
		return true;
	}

	/**
	 * 現在の制約を充足するような assignment が存在するか判定します。
	 */
	bool checkSat()
	{
		// 現在の制約を充足するような assignment が存在したら真になる
		bool ok = false;
		while (!ok)
		{
			auto assignment = satBridge.getAssignmentFromSATSolver();
			// SAT ソルバが解いた結果、UNSAT だったら諦める
			if (assignment == null)
			{
				writeln("UNSAT by SAT Solver");
				break;
			}

			assignment.writeln;

			eqConstraints = assignment.byPair
				.filter!(p => p.value)
				.map!(p => p.key)
				.array;
			neqConstraints = assignment.byPair
				.filter!(p => !p.value)
				.map!(p => p.key)
				.array;

			writeln("===== eqConstraints =====");
			this.eqConstraints.each!writeln;
			writeln("===== neqConstraints =====");
			this.neqConstraints.each!writeln;

			tSolver.eqConstraints = cast(EqualExpression[]) eqConstraints;
			tSolver.neqConstraints = cast(EqualExpression[]) neqConstraints;

			auto res = tSolver.solve();

			// 理論ソルバで SAT だったら終了
			if (res.ok)
			{
				writeln("SAT by theory solver");
				ok = true;
				break;
			}

			writeln("UNSAT by theory solver");

			// 理論ソルバの結果を見て SATBridge に以降は偽としてほしい真偽の組合せを伝達する
			foreach (expr; res.newConstraints)
			{
				satBridge.addAssertion(new NotExpression(expr));
			}
		}
		return ok;
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
		/*
		 * TODO: 与えられた式の部分式の型が通っているか確認する。
		 * 現状では、
		 * (declare-fun f (U U) U)
		 * (declare-fun a () U)
		 * (declare-fun b () U)
		 * (assert (= (f a) (f b)))
		 * のような入力が普通に通ってしまう。QF_UF の世界では今は項の型は確認せずに
		 * 関数の名前だけ見て区別しており、かつ現在は結果が SAT であっても具体的な関数の
		 * assignment はソルバーから提供していないため問題にはなっていないが、今後のことを
		 * 考えると確認するような実装を入れた方が絶対に良いと思う（利用するベンチマーク用の
		 * 入力が必ず valid であるものだ、という保障があるならそこまでピリピリしなくてもまだ良いかも）
		 */
		satBridge.addAssertion(expr);
		return true;
	}

	/**
	 * let 式を展開します。
	 */
	Expression expandLet(ListExpression bindList, Expression expr)
	{
		if (!bindList)
		{
			throw new Exception("Invalid binds for let expression");
		}
		BindExpression[] binds = bindList.elements
			.map!(bind => cast(ListExpression) bind)
			.tee!(bind => typeid(bind.elements[0]).writeln)
			.tee!(bind => typeid(bind.elements[1]).writeln)
			.map!(lst => new BindExpression(cast(SymbolExpression) lst.elements[0], lst.elements[1]))
			.array;

		foreach (bind; binds)
		{
			expr = _expandLet(bind, expr);
		}

		return expr;
	}

	private Expression _expandLet(BindExpression bind, Expression expr)
	{
		if (auto fExpr = cast(FunctionExpression) expr)
		{
			return new FunctionExpression(fExpr.applyingFunction,
					fExpr.arguments.map!(e => _expandLet(bind, e)).array);
		}
		if (auto lExpr = cast(ListExpression) expr)
		{
			return new ListExpression(lExpr.elements.map!(e => _expandLet(bind, e)).array);
		}
		if (auto bExpr = cast(BindExpression) expr)
		{
			return new BindExpression(bExpr.symbol, _expandLet(bind, bExpr.expr));
		}
		if (auto nExpr = cast(NotExpression) expr)
		{
			return new NotExpression(_expandLet(bind, nExpr.child));
		}
		if (auto aExpr = cast(AndExpression) expr)
		{
			return new AndExpression(_expandLet(bind, aExpr.lhs), _expandLet(bind, aExpr.rhs));
		}
		if (auto oExpr = cast(OrExpression) expr)
		{
			return new OrExpression(_expandLet(bind, oExpr.lhs), _expandLet(bind, oExpr.rhs));
		}
		if (auto eExpr = cast(EqualExpression) expr)
		{
			return new EqualExpression(_expandLet(bind, eExpr.lhs), _expandLet(bind, eExpr.rhs));
		}
		if (auto sExpr = cast(SymbolExpression) expr)
		{
			if (sExpr == bind.symbol)
			{
				return bind.expr;
			}
			else
				return sExpr;
		}

		throw new Exception("Unknown expression: %s".format(expr));
	}

	/**
	 * SAT ソルバと SMT ソルバの間でやりとりをするためのクラス
	 */
	class SATBridge
	{
		/// SAT ソルバーに渡した変数の名前から元の Expression への対応を保持
		Expression[string] SATVarToExpr;
		CDCLSolver satSolver = new CDCLSolver();

		private string[] strAssertions;

		/**
	 	 * 与えられた Expression を制約として考慮します。
		 */
		void addAssertion(Expression expr)
		{
			strAssertions ~= this.parseAssertion(expr);
		}

		/**
		 * 現在の制約から SAT ソルバに必要条件を満たすような制約の真偽の割り当てを取得します。
		 * SAT ソルバの結果が UNSAT であったとき、null を返します。
		 */
		bool[Expression] getAssignmentFromSATSolver()
		{
			auto tmp = format("%-((%s) /\\ %))", strAssertions);
			auto tseytin = tseytinTransform(tmp);

			// TODO: sat-d で、現在の状態を維持したまま複数回 tseytin の結果を受け取れるようにする
			// そうしないといちいち new CDCLSolver(); でインスタンスを生成しなければ
			// 複数回 assert と check-sat が走ったときに処理ができない
			satSolver = new CDCLSolver();
			satSolver.initialize(tseytin.parseResult);
			auto literals = satSolver.solve().peek!(Literal[]);
			// UNSAT なら null を返す
			if (literals == null)
				return null;
			bool[string] assignment = resultToOriginalVarsAssignment(tseytin, *literals);

			// 制約を表す式と、それに対する真偽値
			bool[Expression] res;
			foreach (varName, value; assignment)
			{
				assert(varName in SATVarToExpr);
				res[SATVarToExpr[varName]] = value;
			}
			return res;
		}

		/**
		 * 与えられた Expression を命題論理式を表した文字列に変換します。
		 */
		private string parseAssertion(Expression expr)
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
}
