module smtd.type_checker;

import smtd.type_environment;
import smtd.expression;
import std.algorithm : map, all;
import std.range : array;
import std.string : format;

/// 型チェックを行うための関数が集まった静的クラス
static class TypeChecker
{
    /**
     * 与えられた式の型が通るか確認します。
     */
    static bool checkValidExpression(TypeEnvironment env, Expression expr)
    {
        auto boolSort = env.getSort("Bool");
        auto realSort = env.getSort("Real");

        if (auto fExpr = cast(FunctionExpression) expr)
        {
            auto f = fExpr.applyingFunction;
            auto argsSorts = fExpr.arguments.map!(arg => getSortOfExpression(env, arg)).array;

            return f.inTypes == argsSorts
                && fExpr.arguments.all!(arg => checkValidExpression(env, arg));
        }
        if (auto eExpr = cast(EqualExpression) expr)
        {
            return getSortOfExpression(env, eExpr.lhs) == getSortOfExpression(env, eExpr.rhs)
                && checkValidExpression(env, eExpr.lhs) && checkValidExpression(env, eExpr.rhs);
        }
        if (auto nExpr = cast(NotExpression) expr)
        {
            return getSortOfExpression(env, nExpr.child) == boolSort;
        }
        if (auto andExpr = cast(AndExpression) expr)
        {
            return getSortOfExpression(env, andExpr.lhs) == boolSort
                && getSortOfExpression(env, andExpr.rhs) == boolSort;
        }
        if (auto orExpr = cast(OrExpression) expr)
        {
            return getSortOfExpression(env, orExpr.lhs) == boolSort
                && getSortOfExpression(env, orExpr.rhs) == boolSort;
        }
        if (auto lExpr = cast(LessThanExpression) expr)
        {
            return getSortOfExpression(env, lExpr.lhs) == realSort
                && getSortOfExpression(env, lExpr.rhs) == realSort;
        }
        if (auto gExpr = cast(GreaterThanExpression) expr)
        {
            return getSortOfExpression(env, gExpr.lhs) == realSort
                && getSortOfExpression(env, gExpr.rhs) == realSort;
        }
        if (auto leExpr = cast(LessThanOrEqualExpression) expr)
        {
            return getSortOfExpression(env, leExpr.lhs) == realSort
                && getSortOfExpression(env, leExpr.rhs) == realSort;
        }
        if (auto geExpr = cast(GreaterThanOrEqualExpression) expr)
        {
            return getSortOfExpression(env, geExpr.lhs) == realSort
                && getSortOfExpression(env, geExpr.rhs) == realSort;
        }
        return true;
    }

    /**
     * 与えられた式が持つことを期待される sort を返します。
     */
    static Sort getSortOfExpression(TypeEnvironment env, Expression expr)
    {
        if (auto fExpr = cast(FunctionExpression) expr)
        {
            return fExpr.applyingFunction.outType;
        }
        if (auto sExpr = cast(ExpressionWithString) expr)
        {
            auto name = sExpr.stringValue;
            if (env.sortExists(name))
                return env.getSort(name);
            if (env.functionExists(name))
                return env.getFunction(name).outType;
        }
        if (auto sExpr = cast(SortExpression) expr)
        {
            return sExpr.sort;
        }
        if (auto eExpr = cast(EqualExpression) expr)
        {
            return env.getSort("Bool");
        }
        if (auto nExpr = cast(NotExpression) expr)
        {
            return env.getSort("Bool");
        }
        if (auto andExpr = cast(AndExpression) expr)
        {
            return env.getSort("Bool");
        }
        if (auto orExpr = cast(OrExpression) expr)
        {
            return env.getSort("Bool");
        }
        if (auto lExpr = cast(LessThanExpression) expr)
        {
            return env.getSort("Bool");
        }

        if (auto gExpr = cast(GreaterThanExpression) expr)
        {
            return env.getSort("Bool");
        }

        if (auto leExpr = cast(LessThanOrEqualExpression) expr)
        {
            return env.getSort("Bool");
        }

        if (auto geExpr = cast(GreaterThanOrEqualExpression) expr)
        {
            return env.getSort("Bool");
        }

        throw new Exception("Unknown expression %s: %s".format(typeid(expr), expr));
    }
}
