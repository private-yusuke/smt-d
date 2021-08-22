module smtd.util.unionfind;

import std.traits : isSigned;
import std.algorithm : swap;

class UnionFind(T) if (isSigned!T)
{
    T[] arr;
    this(ulong n)
    {
        arr.length = n;
        arr[] = -1;
    }

    T root(T x)
    {
        return arr[x] < 0 ? x : root(arr[x]);
    }

    bool same(T x, T y)
    {
        return root(x) == root(y);
    }

    bool unite(T x, T y)
    {
        x = root(x);
        y = root(y);
        if (x == y)
            return false;
        if (arr[x] > arr[y])
            swap(x, y);
        arr[x] += arr[y];
        arr[y] = x;
        return true;
    }

    T size(T a)
    {
        return -arr[root(a)];
    }
}
