module smtd.smt_solver;

import smtd.expression;
import smtd.theory_solver;
import smtd.type_checker;
import smtd.type_environment;
import smtd.rational;

import std.stdio;
import std.string;
import std.range;
import std.algorithm : map, each, filter;
import std.conv;
import std.typecons : Tuple;
import std.exception : basicExceptionCtors;
import std.bigint : BigInt;
import pegged.grammar;
import satd.solvers.cdcl;
import satd.cnf : Literal;
import satd.tseytin : tseytinTransform, resultToOriginalVarsAssignment;

/// 予約語
const string[] reservedWords = [
    "set-option", "not", "and", "or", "declare-sort", "declare-fun",
    "declare-const", "assert", "not", "set-info", "set-logic", "check-sat",
    "exit", "+", "-", "*", "/", "<=", ">=", "<", ">", "="
];

mixin(grammar(`
SExpression:
	Grammar < SExpr+
	SExpr   <  UnaryOp / Symbol / Keyword / ReservedWord / Float / Integer / String / List
	Integer <- '0' / [1-9][0-9]*
	Float   <- ('0' / [1-9][0-9]*) '.' [0-9]*
	String  < DoublequotedString / WysiwygString
	DoublequotedString <~ :doublequote (!doublequote Char)* :doublequote
	WysiwygString <~ :'|' (!'|' WysiwygChar)* :'|'
	Symbol  <~ [a-zA-Z_$\-][a-zA-Z0-9_$\-]*
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
`.format(reservedWords.map!(s => `"` ~ s ~ `"`))));

enum SMTSolverStatus
{
    SAT,
    UNSAT,
    UNKNOWN
}

SMTSolverStatus toSMTSolverStatus(string s)
{
    import std.string : toLower;

    switch (s.toLower())
    {
    case "sat":
        return SMTSolverStatus.SAT;
    case "unsat":
        return SMTSolverStatus.UNSAT;
    case "unknown":
        return SMTSolverStatus.UNKNOWN;
    default:
        throw new Exception("Unknown input: %s".format(s));
    }
}

/// SMT Solver
class SMTSolver
{
    /// set-logic で与えられた、現在扱う理論
    string logic;
    /// set-info で与えられた補助的な情報
    private Expression[string] info;

    private SATBridge satBridge;
    private TheorySolver tSolver;
    private TypeEnvironment env;
    private SMTSolverStatus status;

    this()
    {
        initialize();
    }

    /// ソルバーを初期化します。
    void initialize()
    {
        this.env = new TypeEnvironment;
        env.declareSort("Bool", 0);
        env.declareSort("Real", 0);

        const string[] commands = [
            "declare-sort", "declare-fun", "declare-const", "assert",
            "set-info", "set-logic", "check-sat", "exit"
        ];
        foreach (command; commands)
        {
            env.declareFunction(command, null, null);
        }

        this.satBridge = new SATBridge(this.env);
        this.status = SMTSolverStatus.UNKNOWN;
        this.tSolver = null;
        this.logic = null;
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

            // 構文木の上では List として受け取るが、特殊な関数やユーザー定義の関数の呼び出しである場合はここで適切な Expression に変換する
            string head = tree.children.front.matches.front;

            switch (head)
            {
            case "=":
                return new EqualExpression(statements[1], statements[2]);
            case "and":
                return new AndExpression(statements[1 .. $]);
            case "or":
                return new OrExpression(statements[1 .. $]);
            case "not":
                return new NotExpression(statements[1]);
            case "+":
                return new AdditionExpression(statements[1], statements[2]);
            case "-":
                return new SubtractionExpression(statements[1], statements[2]);
            case "*":
                return new MultiplicationExpression(statements[1], statements[2]);
            case "/":
                return new DivisionExpression(statements[1], statements[2]);
            case "<":
                return new LessThanExpression(statements[1], statements[2]);
            case ">":
                return new GreaterThanExpression(statements[1], statements[2]);
            case "<=":
                return new LessThanOrEqualExpression(statements[1], statements[2]);
            case ">=":
                return new GreaterThanOrEqualExpression(statements[1], statements[2]);
            case "let":
                return expandLet(cast(ListExpression) statements[1], statements[2]);
            default:
                break;
            }
            if (env.functionExists(head))
            {
                return new FunctionExpression(env.getFunction(head), statements[1 .. $]);
            }
            else
            {
                return new ListExpression(statements);
            }
        case "SExpression.Symbol":
            string name = tree.matches.front;
            if (env.sortExists(name))
            {
                return new SortExpression(env.getSort(name));
            }
            if (env.functionExists(name))
            {
                return new FunctionExpression(env.getFunction(name));
            }
            return new SymbolExpression(name);
        case "SExpression.Integer":
            // return new RationalExpression!BigInt(new BigIntRational(BigInt(tree.matches.front)));
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
                return env.declareSort(exprWithString.stringValue, intExpr.value);
            case "declare-fun":
                string funcName = (cast(ExpressionWithString) fexpr.arguments[0]).stringValue;
                Sort outType = (cast(SortExpression) fexpr.arguments[2]).sort;

                // declaring a constant
                if (auto eexpr = cast(EmptyExpression) fexpr.arguments[1])
                {
                    return env.declareFunction(funcName, [], outType);
                }
                if (auto lexpr = cast(ListExpression) fexpr.arguments[1])
                {
                    Sort[] inTypes = lexpr.elements.map!(s => (cast(SortExpression) s).sort).array;
                    return env.declareFunction(funcName, inTypes, outType);
                }
                throw new Exception("not a valid declare-fun");
            case "set-logic":
                string logicName = (cast(SymbolExpression) fexpr.arguments[0]).name;
                return setLogic(logicName);
            case "set-info":
                string name = (cast(KeywordExpression) fexpr.arguments[0]).keyword;
                Expression content = fexpr.arguments[1];
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
    bool setInfo(string keyword, Expression content)
    {
        this.info[keyword] = content;
        return true;
    }

    /**
	 * ソルバーに伝達された補助的な情報を取得します。
	 */
    Expression getInfo(string keyword)
    {
        return this.info[keyword];
    }

    /**
	 * 与えられた keyword に対応する、ソルバーに伝達された補助的な情報が存在するなら true を、そうでないなら false を返します。
	 */
    bool infoExists(string keyword)
    {
        return (keyword in this.info) != null;
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
            const auto assignment = satBridge.getAssignmentFromSATSolver();
            // SAT ソルバが解いた結果、UNSAT だったら諦める
            if (assignment == null)
            {
                // writeln("UNSAT by SAT Solver");
                this.status = SMTSolverStatus.UNSAT;
                break;
            }

            // assignment.writeln;

            auto trueConstraints = assignment.byPair
                .filter!(p => p.value)
                .map!(p => p.key)
                .array;
            auto falseConstraints = assignment.byPair
                .filter!(p => !p.value)
                .map!(p => p.key)
                .array;

            // writeln("===== trueConstraints =====");
            // trueConstraints.each!writeln;
            // writeln("===== falseConstraints =====");
            // falseConstraints.each!writeln;

            tSolver.setConstraints(trueConstraints, falseConstraints);

            auto res = tSolver.solve();

            // 理論ソルバで SAT だったら終了
            if (res.ok)
            {
                // writeln("SAT by theory solver");
                ok = true;
                this.status = SMTSolverStatus.SAT;
                break;
            }

            // writeln("UNSAT by theory solver");

            // 制約からすぐに UNSAT が導かれてしまうとき
            if (res.newConstraints == [])
            {
                ok = false;
                this.status = SMTSolverStatus.UNSAT;
                break;
            }

            // 理論ソルバの結果を見て SATBridge に以降は偽としてほしい真偽の組合せを伝達する
            foreach (expr; res.newConstraints)
            {
                satBridge.addAssertion(new NotExpression(expr));
            }
        }
        return ok;
    }

    /**
     * ソルバーの状態を文字列にして返します。
     */
    string getStatusString()
    {
        switch (this.status)
        {
        case SMTSolverStatus.SAT:
            return "sat";
        case SMTSolverStatus.UNSAT:
            return "unsat";
        case SMTSolverStatus.UNKNOWN:
            return "unknown";
        default:
            assert(0);
        }
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
        if (TypeChecker.checkValidExpression(env, expr))
        {
            satBridge.addAssertion(expr);
            return true;
        }
        else
            throw new Exception("This expression is invalid: %s".format(expr));
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
            .map!(lst => new BindExpression(cast(SymbolExpression) lst.elements[0], lst.elements[1]))
            .array;

        foreach (bind; binds)
        {
            expr = _expandLet(bind, expr);
        }

        return expr;
    }

    /**
	 * let 式を展開します（実際に式の置換を行うメソッド）。
	 */
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
            return new AndExpression(aExpr.arguments.map!(expr => _expandLet(bind, expr)).array);
        }
        if (auto oExpr = cast(OrExpression) expr)
        {
            return new OrExpression(oExpr.arguments.map!(expr => _expandLet(bind, expr)).array);
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
        private Expression[string] SATVarToExpr;
        private CDCLSolver satSolver;
        private TypeEnvironment env;

        private string[] strAssertions;

        this(TypeEnvironment env)
        {
            this.env = env;
            this.satSolver = new CDCLSolver();
            SATVarToExpr = null;
        }

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
		 * 与えられた名前 varName で SAT ソルバーにて取り扱う Expression を登録します。与えられる Expression は原子論理式に対応するものであることを期待します。
		 */
        void registerSATVar(string varName, Expression expr)
        {
            const auto ptr = varName in SATVarToExpr;
            if (ptr != null)
                throw new Exception("SAT variable \"%s\" already exists".format(varName));
            SATVarToExpr[varName] = expr;
        }

        /**
		 * 与えられた名前 varName に対応する Expression を返します。存在しない場合は例外が投げられます。
		 */
        Expression getExprFromSATVar(string varName)
        {
            auto ptr = varName in SATVarToExpr;
            if (ptr == null)
                throw new Exception("Expression with name \"%s\" doesn\'t exist".format(varName));
            return *ptr;
        }

        /**
		 * 与えられた名前 varName に対応する Expression が存在する場合は真を、そうでない場合は偽を返します。
		 */
        bool SATVarExists(string varName)
        {
            return (varName in SATVarToExpr) != null;
        }

        /**
		 * 与えられた Expression を命題論理式を表した文字列に変換します。
		 */
        private string parseAssertion(Expression expr)
        {
            if (auto eqExpr = cast(EqualExpression) expr)
            {
                // eq に入ったら、その中の木を hash として考えられるようにする
                string varName = format("EQ%d", expr.hashOf());
                if (!SATVarExists(varName))
                    registerSATVar(varName, eqExpr);
                return varName;
            }
            if (auto notExpr = cast(NotExpression) expr)
            {
                return format("-(%s)", this.parseAssertion(notExpr.child));
            }
            if (auto andExpr = cast(AndExpression) expr)
            {
                return format("%-(%s /\\ %)", andExpr.arguments.map!(expr => format("(%s)",
                        this.parseAssertion(expr))).array);
            }
            if (auto orExpr = cast(OrExpression) expr)
            {
                return format("%-(%s \\/ %)", orExpr.arguments.map!(expr => format("(%s)",
                        this.parseAssertion(expr))).array);
            }
            if (auto fExpr = cast(FunctionExpression) expr)
            {
                auto sort = TypeChecker.getSortOfExpression(env, fExpr);
                if (sort == env.getSort("Bool"))
                {
                    string varName = format("BOOL%d", expr.hashOf());
                    if (!SATVarExists(varName))
                        registerSATVar(varName, fExpr);
                    return varName;
                }
                else
                    throw new Exception("Excepted return value to be a Bool, but got %s with %s".format(sort,
                            fExpr));
            }
            if (auto lExpr = cast(LessThanExpression) expr)
            {
                string varName = format("LT%d", lExpr.hashOf());
                if (!SATVarExists(varName))
                    registerSATVar(varName, lExpr);
                return varName;
            }

            if (auto gExpr = cast(GreaterThanExpression) expr)
            {
                return parseAssertion(gExpr.toLessThanExpression());
            }

            if (auto leExpr = cast(LessThanOrEqualExpression) expr)
            {
                return parseAssertion(leExpr.toOrExpression());
            }

            if (auto geExpr = cast(GreaterThanOrEqualExpression) expr)
            {
                return parseAssertion(geExpr.toLessThanOrEqualExpression());
            }
            throw new Exception("Unknown statement while parsing assertion: %s (%s)".format(expr,
                    typeid(expr)));
        }
    }
}

@("Check whether SMTSolver solves benchmark files appropriately")
unittest
{
    /**
     * 与えられたファイルの内容を読み取り、Pegged で提供されているパーサーに入力を与えた結果を返します。
     */
    auto parseInput(File f = stdin)
    {
        string content = f.byLineCopy(Yes.keepTerminator).join.array.to!string;
        return SExpression(content);
    }

    /**
     * テストケースとして利用するベンチマークのファイル一覧を取得します。
     */
    auto getBenchmarkFiles()
    {
        import std.file : dirEntries, SpanMode, getSize;
        import std.algorithm : sort;

        return dirEntries("testcase", SpanMode.depth).filter!(f => f.name.endsWith(".smt2"))
            .array
            .sort!((a, b) => getSize(a.name) < getSize(b.name))
            .map!(f => File(f));
    }

    /**
     * 与えられたパース済みの S 式の羅列で表現された問題について適切に解けているか検証します。
     */
    void checkForFile(File file)
    {
        auto parsedTree = parseInput(file);
        SMTSolver solver = new SMTSolver();

        foreach (sExpr; parsedTree.children.front.children)
        {
            auto expr = solver.parseTree(sExpr);
            solver.runExpression(expr);
        }
        if (solver.infoExists("status"))
        {
            SMTSolverStatus expected = (cast(ExpressionWithString) solver.getInfo("status"))
                .stringValue.toSMTSolverStatus();
            SMTSolverStatus actual = solver.status;
            if (actual != SMTSolverStatus.UNKNOWN)
            {
                assert(expected == actual, "Expected %s, but solved as %s".format(expected, actual));
            }
            else
            {
                import std.stdio : stderr;

                writeln("WARNING: solver's status was unknown for file %s, skipped".format(
                        file.name));
            }
        }
        else
            return;
    }

    foreach (file; getBenchmarkFiles())
    {
        file.name.writeln;
        checkForFile(file);
    }
}
