module smtd.theory_solver.qf_uf_solver;

import smtd.theory_solver.common;
import smtd.statement;

/**
 * 未解釈関数と等号に関する理論のソルバ
 */
class QF_UF_Solver : TheorySolver
{
    override TheorySolverResult solve()
    {
        return new QF_UF_SolverResult();
    }
}

/**
 * 未解釈関数と等号に関する理論のソルバが返す結果
 */
class QF_UF_SolverResult : TheorySolverResult
{
    /// TODO: not implemented yet
    // 一度しくって次に SAT ソルバが UNSAT になるような結果を返すようにしている
    this()
    {
        ok = false;
        newConstraints = [
            new NotExpression(new EqualExpression(new SymbolExpression("x"), new SymbolExpression("x"))),
            new EqualExpression(new SymbolExpression("x"), new SymbolExpression("x"))
        ];
    }
}
