module smtd.type_environment;

import smtd.expression;
import std.string : format;

/// 型環境
class TypeEnvironment
{
    /// 型環境の中にある sort（名前でインデックスが張られている）
    private Sort[string] sorts;
    /// 型環境の中にある関数（名前でインデックスが張られている）
    private Function[string] functions;

    /**
     * 型環境を与えて初期化します。
     */
    this(Sort[string] sorts, Function[string] functions)
    {
        this.sorts = sorts;
        this.functions = functions;
    }

    this()
    {
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
	 * 与えられた文字列に対応する sort が存在する場合は true を、そうでなければ false を返します。
	 */
    bool sortExists(string name)
    {
        return (name in sorts) != null;
    }

    /**
	 * 与えられた文字列に対応する sort を返します。
	 */
    Sort getSort(string name)
    {
        if (auto sort = name in sorts)
        {
            return *sort;
        }
        throw new Exception("Sort with name \"%s\" does not exist".format(name));
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
	 * 与えられた文字列に対応する関数が存在する場合は true を、そうでなければ false を返します。
	 */
    bool functionExists(string name)
    {
        return (name in functions) != null;
    }

    /**
	 * 与えられた文字列に対応する関数を返します。
	 */
    Function getFunction(string name)
    {
        if (auto f = name in functions)
        {
            return *f;
        }
        throw new Exception("Function with name \"%s\" does not exist".format(name));
    }

    override string toString()
    {
        return format("[env] sorts: %-(%s, %), functions: %-(%s, %)",
                this.sorts.values, this.functions.values);
    }
}
