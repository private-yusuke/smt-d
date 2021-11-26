module smtd.theory_solver.lra_solver.rational_with_infinity;

import smtd.rational;

struct RationalWithInfinity(T)
{
    alias R = Rational!T;

    private R value;
    private bool _isPositiveInfinity;
    private bool _isNegativeInfinity;

    enum positiveInfinity = {
        RationalWithInfinity!T res = RationalWithInfinity!T();
        res.setPositiveInfinity();
        return res;
    }();

    enum negativeInfinity = {
        RationalWithInfinity!T res = RationalWithInfinity!T();
        res.setNegativeInfinity();
        return res;
    }();

    this(R value)
    {
        this.value = value;
    }

    void setPositiveInfinity()
    {
        this._isNegativeInfinity = false;
        this._isPositiveInfinity = true;
    }

    void setNegativeInfinity()
    {
        this._isPositiveInfinity = false;
        this._isNegativeInfinity = true;
    }

    bool isPositiveInfinity()
    {
        return this._isPositiveInfinity;
    }

    bool isNegativeInfinity()
    {
        return this._isNegativeInfinity;
    }

    bool isInfinity()
    {
        return this._isPositiveInfinity || this._isNegativeInfinity;
    }

    R getValue()
    {
        if (this.isInfinity())
        {
            import std.string : format;
            throw new Exception("You can't get value from infinite ones. This is %s infinity".format(
                    this._isPositiveInfinity ? "positive" : "negative"));
        }
        return this.value;
    }

    void setValue(R value)
    {
        this.value = value;
        this._isPositiveInfinity = false;
        this._isNegativeInfinity = false;
    }

    bool isMoreThan(R r)
    {
        if (!this.isInfinity())
        {
            return this.getValue() > r;
        }
        else
            return this.isPositiveInfinity();
    }

    bool isMoreThanOrEqual(R r)
    {
        return this.isMoreThan(r) || (!this.isInfinity() && this.getValue == r);
    }

    bool isLessThan(R r)
    {
        if (!this.isInfinity())
        {
            return this.getValue() < r;
        }
        else
            return this.isNegativeInfinity();
    }

    bool isLessThanOrEqual(R r)
    {
        return this.isLessThan(r) || (!this.isInfinity() && this.getValue == r);
    }
}

@("RationalWithInfinity initialization with value")
unittest {
    import std.bigint;

    alias R = Rational!BigInt;
    alias RWI = RationalWithInfinity!BigInt;

    RWI a = RWI(new R(5));
    assert(a.getValue() == new R(5));
    assert(!a.isInfinity());
}

@("RationalWithInfinity with positive infinity")
unittest {
    import std.bigint;
    import std.exception : assertThrown;

    alias R = Rational!BigInt;
    alias RWI = RationalWithInfinity!BigInt;

    RWI finite = RWI(new R(5));
    RWI positiveInf = RWI.positiveInfinity;

    assert(finite != positiveInf);
    assert(positiveInf == RWI.positiveInfinity);
    assertThrown(positiveInf.getValue());
    assert(positiveInf.isInfinity());
    assert(positiveInf.isPositiveInfinity());
    assert(!positiveInf.isNegativeInfinity());
    assert(positiveInf.isMoreThan(finite.getValue));
    assert(!positiveInf.isLessThan(finite.getValue));
}

@("RationalWithInfinity with negative infinity")
unittest {
    import std.bigint;
    import std.exception : assertThrown;

    alias R = Rational!BigInt;
    alias RWI = RationalWithInfinity!BigInt;

    RWI finite = RWI(new R(5));
    RWI negativeInf = RWI.negativeInfinity;

    assert(finite != negativeInf);
    assert(negativeInf == RWI.negativeInfinity);
    assertThrown(negativeInf.getValue());
    assert(negativeInf.isInfinity());
    assert(!negativeInf.isPositiveInfinity());
    assert(negativeInf.isNegativeInfinity());
    assert(!negativeInf.isMoreThan(finite.getValue));
    assert(negativeInf.isLessThan(finite.getValue));
}