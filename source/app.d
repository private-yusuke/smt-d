module smtd.app;

import smtd.smt_solver : SExpression, SMTSolver;
import std.range : front;

/// テスト用の入力
const auto content = `(set-logic QF_UF)
(set-option :produce-models true)
(set-info :category "crafted")
(set-info :keyword |
test|)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (< a b))
(assert (> a b))
(assert (<= a b))
(assert (>= a b))
(check-sat)
`;

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
