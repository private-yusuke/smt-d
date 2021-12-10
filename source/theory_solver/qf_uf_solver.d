module smtd.theory_solver.qf_uf_solver;

import smtd.theory_solver.common;
import smtd.smt_solver : SMTSolver;
import smtd.expression;
import smtd.util.unionfind;
import std.range : zip, array;
import std.container : RedBlackTree, redBlackTree;
import std.string : format;

import std.stdio;
import std.algorithm;

/**
 * 未解釈関数と等号に関する理論のソルバ
 */
class QF_UF_Solver : TheorySolver
{
    // 等号に関する制約
    private EqualExpression[] eqConstraints;
    // 不等号に関する制約
    private EqualExpression[] neqConstraints;

    this(Expression[] trueConstraints, Expression[] falseConstraints, SMTSolver smtSolver)
    {
        super(trueConstraints, falseConstraints, smtSolver);
    }

    this(SMTSolver smtSolver)
    {
        super(smtSolver);
    }

    override void setConstraints(Expression[] trueConstraints, Expression[] falseConstraints)
    {
        super.setConstraints(trueConstraints, falseConstraints);

        // 等号に関する制約を抽出したものを保持する
        this.eqConstraints = trueConstraints.map!(c => cast(EqualExpression) c)
            .filter!(c => c)
            .array;
        this.neqConstraints = falseConstraints.map!(c => cast(EqualExpression) c)
            .filter!(c => c)
            .array;
    }

    override TheorySolverResult solve()
    {
        CongruenceClosure congruenceClosure = new CongruenceClosure;

        import smtd.util.constants;

        string getInfoString(string infoName) {
            if (smtSolver.infoExists(infoName)) {
                Expression expr = smtSolver.getInfo(infoName);
                if(auto sExpr = cast(StringExpression) expr) {
                    return sExpr.value;
                }
            }

            return null;
        }
        
        // Congruence Closure を表す DAG を生成することを指示されているとき
        if (getInfoString(GENERATE_CONGRUENCE_CLOSURE_GRAPH_INFO) == "true") {
            // Congruence Closure を表す DAG の生成先ディレクトリが SMT solver で保持されている場合は
            // 出力先を CongruenceClosure のインスタンスに教える
            if (string destination = getInfoString(CONGRUENCE_CLOSURE_GRAPH_DESTINATION_INFO)) {
                congruenceClosure.graphsDestination = destination;
            }

            string inputFileName = getInfoString(INPUT_FILE_NAME_INFO);

            import std.array : replace;
            congruenceClosure.graphsDestination = format("%s-graphs", inputFileName.replace("/", "_"));
        }

        // 等号に関する制約のうちに含まれている式を congruence closure の中に入れる
        foreach (expr; eqConstraints ~ neqConstraints)
        {
            congruenceClosure.registerExpression(expr.lhs);
            congruenceClosure.registerExpression(expr.rhs);
        }

        foreach (eqExpr; eqConstraints)
        {
            auto u = congruenceClosure.getNodeOfExpression(eqExpr.lhs);
            auto v = congruenceClosure.getNodeOfExpression(eqExpr.rhs);
            u.reason.insert(eqExpr);
            v.reason.insert(eqExpr);
            congruenceClosure.merge(u, v);
        }

        foreach (neqExpr; neqConstraints)
        {
            auto u = congruenceClosure.getNodeOfExpression(neqExpr.lhs);
            auto v = congruenceClosure.getNodeOfExpression(neqExpr.rhs);

            if (congruenceClosure.same(u, v))
            {
                // UNSATISFIABLE
                return TheorySolverResult(false, cast(Expression[])(u.reason.array ~ v.reason.array));
            }
        }
        // SATISFIABLE
        return TheorySolverResult(true, []);
    }
}

private class CongruenceClosureNode
{
    Expression expr;
    RedBlackTree!(EqualExpression, "a.hashOf < b.hashOf") reason;
    string label;

    this(Expression expr)
    {
        this.expr = expr;
        if (auto fExpr = cast(FunctionExpression) expr)
        {
            this.label = fExpr.applyingFunction.name;
        }
        else if (auto sExpr = cast(SymbolExpression) expr)
        {
            this.label = sExpr.name;
        }
        else
            assert(0, "CongruenceClosureNode can only be instantiated with function or symbol");
        reason = new RedBlackTree!(EqualExpression, "a.hashOf < b.hashOf");
    }

    override size_t toHash() @safe nothrow
    {
        return expr.hashOf(label.hashOf());
    }

    override bool opEquals(Object other)
    {
        CongruenceClosureNode node = cast(CongruenceClosureNode) other;
        return node && expr == node.expr && label == node.label;
    }

    override string toString()
    {
        import std.string : format;
        import std.conv : to;

        return format("(%s, %s, %s (%s))", expr, reason, label, this.toHash());
    }
}

private class CongruenceClosure
{
    alias Node = CongruenceClosureNode;

    Node[][Node] successors;
    Node[][Node] predecessors;

    private UnionFind!long uf;

    /// 式から頂点への対応
    private Node[Expression] exprToNode;

    /// 頂点と非負整数を一対一に対応させたときの、頂点から非負整数への対応
    ulong[Node] nodeToIndex;
    /// 頂点と非負整数を一対一に対応させたときの、非負整数から頂点への対応
    Node[ulong] indexToNode;
    /// DAG の中に現れる頂点の数
    private ulong nodeCount = 0;
    /// Congruence Closure Algorithm の内部状態を表現する DAG を記述した DOT 言語のファイルを生成する先
    public string graphsDestination;
    /// すでに生成されたグラフの個数
    private ulong generatedGraphCount;

    this()
    {
        uf = new UnionFind!long(10000000);
    }

    /**
     * 与えられた頂点を DAG の頂点として追加します。
     */
    private void addNode(Node node)
    {
        if (node in nodeToIndex)
        {

            debug stderr.writefln("Node already exists: %s", node);
            return;
        }
        nodeToIndex[node] = nodeCount;
        indexToNode[nodeCount] = node;
        nodeCount++;
    }

    /**
     * 頂点 to が頂点 from の successor であるという関係を追加します。
     */
    private void addSuccessor(Node from, Node to)
    {
        if (from !in successors)
        {
            successors[from] = [];
        }
        successors[from] ~= to;
    }

    /**
     * 頂点 to が頂点 from の predecessor であるという関係を追加します。
     */
    private void addPredecessor(Node from, Node to)
    {
        if (from !in predecessors)
        {
            predecessors[from] = [];
        }
        predecessors[from] ~= to;
    }

    /**
     * 与えられた頂点の successor を返します。
     */
    private Node[] getSuccessors(Node node)
    {
        if (node !in successors)
            return [];
        else
            return successors[node];
    }

    /**
     * 与えられた頂点の predecessor を返します。
     */
    private Node[] getPredecessors(Node node)
    {
        if (node !in predecessors)
            return [];
        else
            return predecessors[node];
    }

    /**
     * 与えられた式に対応する congruence closure 内の頂点を返します。
     */
    Node getNodeOfExpression(Expression expr)
    {
        return exprToNode[expr];
    }

    /**
     * 与えられた式に対応する congruence closure 内の頂点が存在する場合は真を、そうでなければ偽を返します。
     */
    bool nodeOfExpressionExists(Expression expr)
    {
        return (expr in exprToNode) != null;
    }

    /**
     * 与えられた式を congruence closure 内の頂点として追加します。すでに追加されていたら偽を返します。
     */
    bool registerExpression(Expression expr)
    {
        // 与えられた式に対応する頂点がすでにグラフ内にあったら
        if (expr in exprToNode)
        {
            return false;
        }

        if (auto fExpr = cast(FunctionExpression) expr)
        {
            Node fNode = new Node(expr);

            foreach (argExpr; fExpr.arguments)
            {
                registerExpression(argExpr);
                Node argNode = getNodeOfExpression(argExpr);
                addSuccessor(fNode, argNode);
                addPredecessor(argNode, fNode);
            }

            addNode(fNode);
            exprToNode[expr] = fNode;

            // グラフ生成先があるなら生成する
            if (this.graphsDestination)
                writeDOTFile();
            
            return true;
        }
        else if (auto sExpr = cast(SymbolExpression) expr)
        {
            Node sNode = new Node(sExpr);
            addNode(sNode);
            exprToNode[expr] = sNode;

            // グラフ生成先があるなら生成する
            if (this.graphsDestination)
                writeDOTFile();

            return true;
        }
        else
            assert(0, "Only FunctionExpression or SymbolExpression can be added to the DAG");
    }

    auto root(Node u)
    {
        return uf.root(nodeToIndex[u]);
    }

    bool same(Node u, Node v)
    {
        return root(u) == root(v);
    }

    void unite(Node u, Node v)
    {
        uf.unite(nodeToIndex[u], nodeToIndex[v]);
    }

    bool congruent(Node u, Node v)
    {
        if (u.label != v.label || successors[u].length != successors[v].length)
            return false;
        foreach (i; 0 .. successors[u].length)
        {
            Node uSuccessor = successors[u][i];
            Node vSuccessor = successors[v][i];
            if (!same(uSuccessor, vSuccessor))
                return false;
        }

        return true;
    }

    void merge(Node u, Node v)
    {
        if (same(u, v))
            return;

        unite(u, v);
        foreach (p; zip(getPredecessors(u), getPredecessors(v)))
        {
            if (!same(p[0], p[1]) && congruent(p[0], p[1]))
            {
                p[0].reason.insert(u.reason.array);
                p[0].reason.insert(v.reason.array);
                p[1].reason.insert(u.reason.array);
                p[1].reason.insert(v.reason.array);
                merge(p[0], p[1]);
            }
        }
    }

    string toDOT()
    {
        import std.format : format;

        string res = "digraph congruenceclosure {\nnode[style=filled, fillcolor=white];\n";
        res ~= "graph [layout=dot];\n";

        foreach (index, node; indexToNode)
        {
            res ~= format(`"%s" [label="%s, %s"];` ~ '\n', node.toHash(), node.label, root(node));
        }
        foreach (from, tos; successors)
        {
            foreach (to; tos)
            {
                res ~= format(`"%s" -> "%s";` ~ '\n', from.toHash(), to.toHash());
            }
        }
        res ~= "}\n";
        return res;
    }

    /**
     * 呼び出された時点での DAG の状態を DOT 言語のファイルとして書き出します。
     */
    void writeDOTFile() {
        import std.file : exists, isDir, mkdir, write;

        string content = this.toDOT();
        string dirName = format("%s", this.graphsDestination);
        if (!dirName.exists) {
            mkdir(dirName);
        }
        if (!dirName.isDir) {
            throw new Exception("Graph destination %s is expected to be a directory, but it isn't.".format(dirName));
        }

        string filename = format("%s/%d.dot", dirName, this.generatedGraphCount);
        write(filename, content);

        this.generatedGraphCount++;
    }

    override string toString()
    {
        return "";
    }
}
