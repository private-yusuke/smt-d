module smtd.rational;

import std.numeric : gcd;
import std.math : abs;
import std.traits : isIntegral;
import std.bigint : BigInt;

/**
 * 有理数を扱うためのデータ構造
 * 内部で保持する値の型を型引数で与えることができる
 */
class Rational(T) if (isIntegral!T || is(T : BigInt))
{
    /// 分子
    T numerator;
    /// 分母
    T denominator;

    /// 同じ型の値を2つ与えて初期化
    this(T numerator, T denominator)
    {
        if (denominator < 0)
        {
            numerator *= -1;
            denominator *= -1;
        }
        const T g = gcd(abs(numerator), denominator);
        this.numerator = numerator / g;
        this.denominator = denominator / g;
    }

    /// Rational であるような型の値だけ与えて初期化
    this(R)(R value) if (is(const R == const Rational!T))
    {
        auto rational = cast(Rational!T) value;
        this(rational.numerator, rational.denominator);
    }

    /// 分子の値だけ与えて初期化
    this(R)(R value) if (!is(const R == const Rational!T))
    {
        import std.conv : to;

        this(value.to!T, 1.to!T);
    }

    /// 別々の型の値を2つ与えて初期化
    this(R, S)(R numerator, S denominator)
    {
        import std.conv : to;

        this(numerator.to!T, denominator.to!T);
    }

    auto opBinary(string op, R)(const R rhs) const
    {
        static if (op == "+")
            return add(rhs);
        else static if (op == "-")
            return substract(rhs);
        else static if (op == "*")
            return multiply(rhs);
        else static if (op == "/")
            return divide(rhs);
        else
            static assert(0, "Operator " ~ op ~ " not implemented");
    }

    auto opOpAssign(string op, T)(Rational!T rhs)
    {
        T n, d;
        switch (op)
        {
        case "+":
            n = this.numerator * rhs.denominator + rhs.numerator * this.denominator;
            d = this.denominator * rhs.denominator;
            break;
        case "-":
            n = this.numerator * rhs.denominator + (-rhs.numerator) * this.denominator;
            d = this.denominator * rhs.denominator;
            break;
        case "*":
            n = this.numerator * rhs.numerator;
            d = this.denominator * rhs.denominator;
            break;
        case "/":
            n = this.numerator * rhs.denominator;
            d = this.denominator * rhs.numerator;
            break;
        default:
            assert(0);
        }
        if (d < 0)
        {
            n = -n;
            d = -d;
        }
        
        const T g = gcd(abs(n), d);
        this.numerator = n / g;
        this.denominator = d / g;
        return this;
    }

    auto opUnary(string op)() const
    {
        if (op == "+")
        {
            return this;
        }
        if (op == "-")
        {
            return new typeof(this)(-this.numerator, this.denominator);
        }
        assert(0);
    }

    /// 逆数を返します。
    T reciprocal(this T)()
    {
        return new T(this.denominator, this.numerator);
    }

    /// 加法の逆元を返します。
    T additiveInverse(this T) () {
        return new T(-this.numerator, this.denominator);
    }

    private T add(this T)(T rhs)
    {
        auto n = this.numerator * rhs.denominator + rhs.numerator * this.denominator;
        auto d = this.denominator * rhs.denominator;
        return new T(n, d);
    }

    private T substract(this T)(T rhs)
    {
        return add(new T(-rhs.numerator, rhs.denominator));
    }

    private T multiply(this T)(T rhs)
    {
        auto n = this.numerator * rhs.numerator;
        auto d = this.denominator * rhs.denominator;
        return new T(n, d);
    }

    private T divide(this T)(T rhs)
    {
        return multiply(rhs.reciprocal);
    }

    override string toString() const
    {
        import std.conv : to;

        return numerator.to!string ~ "/" ~ denominator.to!string;
    }

    override bool opEquals(Object other) const
    {
        auto o = cast(typeof(this)) other;
        return o && this.numerator == o.numerator && this.denominator == o.denominator;
    }

    override size_t toHash() @safe nothrow const
    {
        return numerator.hashOf(denominator.hashOf());
    }

    int opCmp(R)(Rational!R other)
    {
        T v1 = numerator * other.denominator;
        T v2 = other.numerator * denominator;

        return v1.opCmp(v2);
    }
}

@("Rational initializing with two arguments")
unittest
{
    alias R = Rational!long;
    assert(new R(1, 2) == new R(-1, -2));
    assert(new R(-1, 2) == new R(1, -2));

    assert(new R(100, 250) == new R(2, 5));
}

@("Rational initialization with two different type values")
unittest
{
    alias R = Rational!BigInt;

    // initialization check (both argument can take values of different types)
    assert(new R(1, 2) == new R(BigInt(1), 2));
    assert(new R(1, 2) == new R(1, BigInt(2)));
    assert(new R(1, 2) == new R(BigInt(1), BigInt(2)));
}

@("Rational initializing with non-Ratinal one argument")
unittest
{
    alias R = Rational!long;
    alias B = Rational!BigInt;
    assert(new R(2) == new R(2, 1));
    assert(new B(2) == new B(2, 1));
}

@("Rational initializing with one Rational argument")
unittest
{
    alias R = Rational!BigInt;
    const R a = new const R(1, 2);

    assert(new R(a) == new R(1, 2));
}

@("Rational opUnary")
unittest
{
    Rational!BigInt a = new Rational!BigInt(2);
    Rational!BigInt b = new Rational!BigInt(-2);

    assert(+a == a);
    assert(-a == b);
}

@("Rational opCmp")
unittest
{
    auto r1 = new Rational!BigInt(2, 3);
    auto r2 = new Rational!BigInt(3, 2);
    assert(r1 < r2);
    assert(r1 <= r2);
    assert(!(r1 > r2));
    assert(!(r1 >= r2));
}

@("Rational opCmp with big values")
unittest
{
    auto r1 = new Rational!BigInt(200, 2);
    auto r2 = new Rational!BigInt(100, 1);
    assert(!(r1 < r2));
    assert(r1 <= r2);
    assert(!(r1 > r2));
    assert(r1 >= r2);
}

@("Rational with BigInt handles big numbers")
unittest
{
    alias BigIntRational = Rational!BigInt;

    auto r1 = new BigIntRational(3, 4);
    auto r2 = new BigIntRational(4, 3); // opEquals check
    assert(r1 == new BigIntRational(6, 8));
    assert(r1 != new BigIntRational(5, 8));
    assert(r1 + r2 == new BigIntRational(25, 12));
    assert(r1 - r2 == new BigIntRational(-7, 12));
    assert(r1 * r2 == new BigIntRational(1, 1));
    assert(r1 / r2 == new BigIntRational(9, 16));
    import std.range : repeat, array;

    // Check for big numbers
    auto r3 = new BigIntRational(BigInt('1'.repeat(100).array), BigInt('2'.repeat(100).array));
    assert(r3 == new BigIntRational(1, 2));
    auto r4 = new BigIntRational(BigInt('9'.repeat(100).array), BigInt('7'.repeat(100).array));
    assert(r4 == new BigIntRational(9, 7));
}

@("Rational additionInverse")
unittest {
    auto r1 = new Rational!BigInt(3, 2);

    assert(r1.additiveInverse == new Rational!BigInt(-3, 2));
}