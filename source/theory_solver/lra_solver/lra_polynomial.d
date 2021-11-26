module smtd.theory_solver.lra_solver.lra_polynomial;

import smtd.rational;
import std.algorithm : map;

/**
 * LRA の内部計算で用いる、項のデータ構造
 * a_0x_0 + ... + a_ix_i + ... の形の多項式を表現する
 * 型引数 T には、内部の計算で用いる Rational の型引数となるものを渡す（BigInt 推奨）
 */
class LRAPolynomial(T)
{
    import std.traits : Unqual;

    alias R = Rational!T;

    /// 変数名から有理数の係数へのマッピング
    /// terms[x_i] = a_i
    R[string] terms;

    this()
    {
    }

    /// 複数の項を与えて初期化
    this(R[string] terms)
    {
        this.terms = terms;
    }

    /**
     * 与えられた変数名 varName の係数を設定します。
     */
    void setCoefficient(string varName, const R coefficient)
    {
        this.terms[varName] = new R(coefficient);
    }

    /**
     * 与えられた変数名 varName の係数に値 coefficient を足します。
     */
    void addCoefficient(S)(string varName, S coefficient)
    {
        auto ptr = varName in this.terms;
        if (varName !in this.terms)
        {
            setCoefficient(varName, new R(coefficient));
        }
        else
        {
            setCoefficient(varName, this.terms[varName] + coefficient);
        }
    }

    private T addPolynomial(this T)(T rhs)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            import std.conv : to;

            newTerms[varName] = new R(coefficient);
        }
        foreach (varName, coefficient; rhs.terms)
        {
            if (varName !in newTerms)
            {
                newTerms[varName] = new R(coefficient);
            }
            else
            {
                newTerms[varName] += new R(coefficient);
            }
        }
        return new T(newTerms);
    }

    private T subtractPolynomial(this T)(T rhs)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            import std.conv : to;

            newTerms[varName] = new R(coefficient);
        }
        foreach (varName, coefficient; rhs.terms)
        {
            if (varName !in newTerms)
            {
                newTerms[varName] = new R(-coefficient);
            }
            else
            {
                newTerms[varName] -= new R(coefficient);
            }
        }
        return new T(newTerms);
    }

    private T multiplyPolynomial(this T, S)(S value)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            newTerms[varName] = new R(coefficient * value);
        }
        return new T(newTerms);
    }

    private T dividePolynomial(this T, S)(S value)
    {
        R[string] newTerms;

        foreach (varName, coefficient; this.terms)
        {
            newTerms[varName] = new R(coefficient / value);
        }
        return new T(newTerms);
    }

    /**
     * 多項式同士の加算・減算を二項演算子で行うための関数定義
     */
    auto opBinary(string op, S)(const S rhs)
            if (is(Unqual!S == Unqual!(typeof(this))))
    {
        if (op == "+")
            return this.addPolynomial(rhs);
        if (op == "-")
            return this.subtractPolynomial(rhs);
        assert(0);
    }

    /**
     * 多項式と有理数の乗算・除算を二項演算子で行うための関数定義
     */
    auto opBinary(string op, S)(const S rhs) const
    if (is(Unqual!S == Unqual!(Rational!T)))
    {
        if (op == "*")
            return this.multiplyPolynomial(rhs);
        if (op == "/")
            return this.dividePolynomial(rhs);
        assert(0);
    }

    override bool opEquals(Object other) const
    {
        auto rhs = cast(typeof(this)) other;
        return rhs && this.terms == rhs.terms;
    }

    override string toString() const
    {
        import std.string : format;
        import std.array : byPair;

        return format("%-(%s %)", this.terms.byPair.map!(
                p => format("%s[%s]", p[1], p[0])));
    }
}

@("LRAPolynomial initialization with terms returns the same object as manually initializing it")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(1),
            "b": new R(2),
            "c": new R(5),
        ]);
    L b = new L();
    b.setCoefficient("a", new R(1));
    b.setCoefficient("b", new R(2));
    b.setCoefficient("c", new R(5));

    assert(a == b);
}

@("LRAPolynomial plus LRAPolynomial returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);
    L b = new L([
            "b": new R(2),
            "c": new R(3),
            "d": new R(4),
        ]);

    assert(a + b == b + a);

    L expected = new L([
        "a": new R(2),
        "b": new R(5),
        "c": new R(7),
        "d": new R(4),
    ]);

    assert(a + b == expected);
}

@("LRAPolynomial minus LRAPolynomial returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);
    L b = new L([
            "b": new R(2),
            "c": new R(3),
            "d": new R(4),
        ]);

    assert(a - b != b - a);
    assert(a - b != a + b);

    L expected1 = new L([
        "a": new R(2),
        "b": new R(1),
        "c": new R(1),
        "d": new R(-4),
    ]);
    L expected2 = new L([
        "a": new R(-2),
        "b": new R(-1),
        "c": new R(-1),
        "d": new R(4),
    ]);

    assert(a - b == expected1);
    assert(b - a == expected2);
}

@("LRAPolynomial times Rational returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);

    L expected = new L([
        "a": new R(10),
        "b": new R(15),
        "c": new R(20),
    ]);

    assert(a * new R(5) == expected);
}

@("LRAPolynomial divided by Rational returns correct values")
unittest
{
    import std.bigint;

    alias R = Rational!BigInt;
    alias L = LRAPolynomial!BigInt;

    L a = new L([
            "a": new R(2),
            "b": new R(3),
            "c": new R(4),
        ]);

    L expected = new L([
        "a": new R(1, 2),
        "b": new R(3, 4),
        "c": new R(1),
    ]);

    assert(a / new R(4) == expected);
}