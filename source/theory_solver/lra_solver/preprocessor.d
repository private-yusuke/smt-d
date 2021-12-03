module smtd.theory_solver.lra_solver.preprocessor;

import smtd.theory_solver.common;
import smtd.expression;
import std.algorithm : map;
import std.range : array;

class LRAPreprocessor : TheorySolverPreprocessor {
    Expression preprocess(Expression expr) {
        return _preprocess(expr);
    }

    private Expression _preprocess(Expression expr) {
        if (auto nExpr = cast(NotExpression) expr)
        {
            return new NotExpression(_preprocess(nExpr.child));
        }
        if (auto andExpr = cast(AndExpression) expr)
        {
            return new AndExpression(andExpr.arguments.map!(expr => _preprocess(expr)).array);
        }
        if (auto orExpr = cast(OrExpression) expr)
        {
            return new OrExpression(orExpr.arguments.map!(expr => _preprocess(expr)).array);
        }
        if (auto iExpr = cast(ImpliesExpression) expr)
        {
            return new ImpliesExpression(_preprocess(iExpr.lhs), _preprocess(iExpr.rhs));
        }
        if(auto eExpr = cast(EqualExpression) expr) {
            return eExpr.toExpressionForLRA();
        }
        return expr;
    }
}

@("LRAPreprocessor converts EqualExpression to appropriate form")
unittest {
    auto x = new SymbolExpression("x");
    auto y = new SymbolExpression("y");

    auto a = new EqualExpression(y, x);
    TheorySolverPreprocessor preprocessor = new LRAPreprocessor();

    assert(preprocessor.preprocess(a) ==
        new AndExpression([
            new LessThanOrEqualExpression(y, x),
            new GreaterThanOrEqualExpression(y, x)
        ])
    );

    auto b = new NotExpression(a);

    assert(preprocessor.preprocess(b) ==
        new NotExpression(new AndExpression([
            new LessThanOrEqualExpression(y, x),
            new GreaterThanOrEqualExpression(y, x)
        ]))
    );

    auto c = new OrExpression([a, b]);

    assert(preprocessor.preprocess(c) ==
        new OrExpression([
            new AndExpression([
                new LessThanOrEqualExpression(y, x),
                new GreaterThanOrEqualExpression(y, x)
            ]),
            new NotExpression(new AndExpression([
                new LessThanOrEqualExpression(y, x),
                new GreaterThanOrEqualExpression(y, x)
            ]))
        ])
    );
}