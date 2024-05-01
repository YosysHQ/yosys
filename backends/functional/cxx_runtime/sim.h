/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#ifndef SIM_H
#define SIM_H

#include <array>

template<size_t n>
using Signal = std::array<bool, n>;

template<size_t n, size_t m>
Signal<n> slice(Signal<m> const& a, size_t offset)
{
    Signal<n> ret;

    std::copy(a.begin() + offset, a.begin() + offset + n, ret.begin());
    return ret;
}

template<size_t n>
Signal<n> $const(uint32_t val)
{
    size_t i;
    Signal<n> ret;

    for(i = 0; i < n; i++)
        if(i < 32)
            ret[i] = val & (1<<i);
        else
            ret[i] = false;
    return ret;
}

template<size_t n>
Signal<n> $const(std::initializer_list<uint32_t> vals)
{
    size_t k, i;
    Signal<n> ret;

    k = 0;
    for (auto val : vals) {
        for(i = 0; i < 32; i++)
            if(i + k < n)
                ret[i + k] = val & (1<<i);
        k += 32;
    }
    for(; k < n; k++)
        ret[k] = false;
    return ret;
}

template<size_t n>
bool as_bool(Signal<n> sig)
{
    for(int i = 0; i < n; i++)
        if(sig[i])
            return true;
    return false;
}

template<size_t n>
uint32_t as_int(Signal<n> sig)
{
    uint32_t ret = 0;
    for(int i = 0; i < n; i++)
        if(sig[i] && i < 32)
            ret |= 1<<i;
    return ret;
}

template<size_t n>
Signal<n> $mux(Signal<n> const& a, Signal<n> const &b, Signal<1> const &s)
{
    return s[0] ? b : a;
}

template<size_t n>
Signal<n> $not(Signal<n> const& a)
{
    Signal<n> ret;
    for(size_t i = 0; i < n; i++)
        ret[i] = !a[i];
    return ret;
}

template<size_t n>
Signal<n> $neg(Signal<n> const& a)
{
    Signal<n> ret;
    bool carry = true;
    for(size_t i = 0; i < n; i++) {
        int r = !a[i] + carry;
        ret[i] = (r & 1) != 0;
        carry = (r >> 1) != 0;
    }
    return ret;
}

template<size_t n>
Signal<1> $reduce_or(Signal<n> const& a)
{
    return { as_bool(a) };
}

template<size_t n>
Signal<1> $reduce_and(Signal<n> const& a)
{
    for(size_t i = 0; i < n; i++)
        if(!a[i])
            return { false };
    return { true };
}

template<size_t n>
Signal<1> $reduce_bool(Signal<n> const& a)
{
    return { as_bool(a) };
}

template<size_t n>
Signal<1> $logic_and(Signal<n> const& a, Signal<n> const& b)
{
    return { as_bool(a) && as_bool(b) };
}

template<size_t n>
Signal<1> $logic_or(Signal<n> const& a, Signal<n> const& b)
{
    return { as_bool(a) || as_bool(b) };
}

template<size_t n>
Signal<1> $logic_not(Signal<n> const& a)
{
    return { !as_bool(a) };
}

template<size_t n>
Signal<n> $add(Signal<n> const& a, Signal<n> const &b)
{
    Signal<n> ret;
    size_t i;
    int x = 0;
    for(i = 0; i < n; i++){
        x += (int)a[i] + (int)b[i];
        ret[i] = x & 1;
        x >>= 1;
    }
    return ret;
}
template<size_t n>
Signal<n> $sub(Signal<n> const& a, Signal<n> const &b)
{
    Signal<n> ret;
    int x = 1;
    for(size_t i = 0; i < n; i++){
        x += (int)a[i] + (int)!b[i];
        ret[i] = x & 1;
        x >>= 1;
    }
    return ret;
}

template<size_t n>
Signal<1> $uge(Signal<n> const& a, Signal<n> const &b)
{
    for(size_t i = n; i-- != 0; )
        if(a[i] != b[i])
            return { a[i] };
    return { true };
}

template<size_t n>
Signal<1> $ugt(Signal<n> const& a, Signal<n> const &b)
{
    for(size_t i = n; i-- != 0; )
        if(a[i] != b[i])
            return { a[i] };
    return { false };
}

template<size_t n>
Signal<1> $ge(Signal<n> const& a, Signal<n> const &b)
{
    if(a[n-1] != b[n-1])
        return { b[n-1] };
    return $uge(a, b);
}

template<size_t n>
Signal<1> $gt(Signal<n> const& a, Signal<n> const &b)
{
    if(a[n-1] != b[n-1])
        return { b[n-1] };
    return $ugt(a, b);
}

template<size_t n> Signal<1> $ule(Signal<n> const& a, Signal<n> const &b) { return $uge(b, a); }
template<size_t n> Signal<1> $ult(Signal<n> const& a, Signal<n> const &b) { return $ugt(b, a); }
template<size_t n> Signal<1> $le(Signal<n> const& a, Signal<n> const &b) { return $ge(b, a); }
template<size_t n> Signal<1> $lt(Signal<n> const& a, Signal<n> const &b) { return $gt(b, a); }

template<size_t n>
Signal<n> $and(Signal<n> const& a, Signal<n> const &b)
{
    Signal<n> ret;
    for(size_t i = 0; i < n; i++)
        ret[i] = a[i] && b[i];
    return ret;
}

template<size_t n>
Signal<n> $or(Signal<n> const& a, Signal<n> const &b)
{
    Signal<n> ret;
    for(size_t i = 0; i < n; i++)
        ret[i] = a[i] || b[i];
    return ret;
}

template<size_t n>
Signal<n> $xor(Signal<n> const& a, Signal<n> const &b)
{
    Signal<n> ret;
    for(size_t i = 0; i < n; i++)
        ret[i] = a[i] != b[i];
    return ret;
}

template<size_t n, size_t na, size_t nb>
Signal<n> $shl(Signal<na> const& a, Signal<nb> const &b)
{
    if(nb >= sizeof(int) * 8 - 1)
        for(size_t i = sizeof(int) * 8 - 1; i < nb; i++)
            assert(!b[i]);
    size_t amount = as_int(b);
    Signal<n> ret = $const<n>(0);
    if(amount < n){
        if(amount + na > n)
            std::copy(a.begin(), a.begin() + (n - amount), ret.begin() + amount);
        else
            std::copy(a.begin(), a.end(), ret.begin() + amount);
    }
    return ret;
}

template<size_t n, size_t nb>
Signal<n> $shr(Signal<n> const& a, Signal<nb> const &b)
{
    if(nb >= sizeof(int) * 8 - 1)
        for(size_t i = sizeof(int) * 8 - 1; i < nb; i++)
            assert(!b[i]);
    size_t amount = as_int(b);
    Signal<n> ret;
    for (size_t i = 0; i < n; i++) {
        if(i + amount < n)
            ret[i] = a[i + amount];
        else
            ret[i] = false;
    }
    return ret;
}

template<size_t n, size_t nb>
Signal<n> $asr(Signal<n> const& a, Signal<nb> const &b)
{
    if(nb >= sizeof(int) * 8 - 1)
        for(size_t i = sizeof(int) * 8 - 1; i < nb; i++)
            assert(!b[i]);
    size_t amount = as_int(b);
    Signal<n> ret;
    for (size_t i = 0; i < n; i++) {
        if(i + amount < n)
            ret[i] = a[i + amount];
        else
            ret[i] = a[n - 1];
    }
    return ret;
}

template<size_t n>
Signal<1> $eq(Signal<n> const& a, Signal<n> const &b)
{
    for(size_t i = 0; i < n; i++)
        if(a[i] != b[i])
            return { false };
    return { true };
}

template<size_t n>
Signal<1> $ne(Signal<n> const& a, Signal<n> const &b)
{
    for(size_t i = 0; i < n; i++)
        if(a[i] != b[i])
            return { true };
    return { false };
}

template<size_t n, size_t ns>
Signal<n> $pmux(Signal<n> const& a, Signal<n*ns> const &b, Signal<ns> const &s)
{
    bool found;
    Signal<n> ret;

    found = false;
    ret = a;
    for(size_t i = 0; i < ns; i++){
        if(s[i]){
            if(found)
                return $const<n>(0);
            found = true;
            ret = slice<n>(b, n * i);
        }
    }
    return ret;
}

template<size_t n, size_t m>
Signal<n+m> concat(Signal<n> const& a, Signal<m> const& b)
{
    Signal<n + m> ret;
    std::copy(a.begin(), a.end(), ret.begin());
    std::copy(b.begin(), b.end(), ret.begin() + n);
    return ret;
}

template<size_t n, size_t m>
Signal<n> $zero_extend(Signal<m> const& a)
{
    assert(n >= m);
    Signal<n> ret;
    std::copy(a.begin(), a.end(), ret.begin());
    for(size_t i = m; i < n; i++)
        ret[i] = false;
    return ret;
}

template<size_t n, size_t m>
Signal<n> $sign_extend(Signal<m> const& a)
{
    assert(n >= m);
    Signal<n> ret;
    std::copy(a.begin(), a.end(), ret.begin());
    for(size_t i = m; i < n; i++)
        ret[i] = a[m-1];
    return ret;
}

#endif
