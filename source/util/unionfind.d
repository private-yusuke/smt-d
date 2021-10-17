module smtd.util.unionfind;

import std.traits : isSigned;
import std.algorithm : swap;

/// 素集合データ構造（扱う値は型引数 T で与えられる）
class UnionFind(T) if (isSigned!T)
{
    T[] arr;
    this(ulong n)
    {
        arr.length = n;
        arr[] = -1;
    }

    /// 与えられた値に対応する頂点の根の値を返します。
    T root(T x)
    {
        return arr[x] < 0 ? x : root(arr[x]);
    }

    /// 与えられた2引数が同じ素集合に属していたら true、そうでなければ false を返します。
    bool same(T x, T y)
    {
        return root(x) == root(y);
    }

    /// 与えられた2引数が同じ素集合に属していることにします。
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

    /// 与えられた値が属す素集合に含まれる要素の個数を返します。
    T size(T a)
    {
        return -arr[root(a)];
    }
}
