module smtd.theory_solver.qf_uf_solver;

import smtd.theory_solver.common;
import smtd.expression;
import smtd.util.unionfind;
import std.range : zip, array;
import std.container : RedBlackTree, redBlackTree;

import std.stdio;
import std.algorithm;

/**
 * 未解釈関数と等号に関する理論のソルバ
 */
class QF_UF_Solver : TheorySolver
{
    override TheorySolverResult solve()
    {
        CongruenceClosure congruenceClosure = new CongruenceClosure;
        foreach (expr; eqConstraints ~ neqConstraints)
        {
            congruenceClosure.getNodeOfExpr(expr.lhs);
            congruenceClosure.getNodeOfExpr(expr.rhs);
        }

        foreach (eqExpr; eqConstraints)
        {
            auto u = congruenceClosure.getNodeOfExpr(eqExpr.lhs);
            auto v = congruenceClosure.getNodeOfExpr(eqExpr.rhs);
            u.reason.insert(eqExpr);
            v.reason.insert(eqExpr);
            congruenceClosure.merge(u, v);
        }

        foreach (neqExpr; neqConstraints)
        {
            auto u = congruenceClosure.getNodeOfExpr(neqExpr.lhs);
            auto v = congruenceClosure.getNodeOfExpr(neqExpr.rhs);

            if (congruenceClosure.same(u, v))
            {
                // UNSATISFIABLE
                // TODO: reason を返すようにする
                return new TheorySolverResult(false,
                        cast(Expression[])(u.reason.array ~ v.reason.array));
            }
        }
        // SATISFIABLE
        return new TheorySolverResult(true, []);
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

    private UnionFind!long uf = new UnionFind!long(100);

    /// 式から頂点への対応
    Node[Expression] exprToNode;

    /// 頂点と非負整数を一対一に対応させたときの、頂点から非負整数への対応
    ulong[Node] nodeToIndex;
    /// 頂点と非負整数を一対一に対応させたときの、非負整数から頂点への対応
    Node[ulong] indexToNode;
    /// DAG の中に現れる頂点の数
    private ulong nodeCount = 0;

    this()
    {
        uf = new UnionFind!long(100);
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

    Node getNodeOfExpr(Expression expr)
    {
        // 与えられた式に対応する頂点がすでにグラフ内にあったら追加処理をしない
        if (expr in exprToNode)
        {
            return exprToNode[expr];
        }

        if (auto fExpr = cast(FunctionExpression) expr)
        {
            Node fNode = new Node(expr);

            foreach (argExpr; fExpr.arguments)
            {
                Node argNode = getNodeOfExpr(argExpr);
                addSuccessor(fNode, argNode);
                addPredecessor(argNode, fNode);
            }

            addNode(fNode);
            exprToNode[expr] = fNode;
            return fNode;
        }
        else if (auto sExpr = cast(SymbolExpression) expr)
        {
            Node sNode = new Node(sExpr);
            addNode(sNode);
            exprToNode[expr] = sNode;
            return sNode;
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

    override string toString()
    {
        return "";
    }
}
