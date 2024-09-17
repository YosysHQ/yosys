/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
 *  Copyright (C) 2024 National Technology and Engineering Solutions of Sandia, LLC
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
#include <cassert>
#include <string>
#include <iostream>
#include <algorithm>

template<size_t n>
class Signal {
    template<size_t m> friend class Signal;
    std::array<bool, n> _bits;
public:
    Signal() { }
    Signal(uint32_t val)
    {
        for(size_t i = 0; i < n; i++)
            if(i < 32)
                _bits[i] = val & (1<<i);
            else
                _bits[i] = false;
    }

    Signal(std::initializer_list<uint32_t> vals)
    {
        size_t k, i;

        k = 0;
        for (auto val : vals) {
            for(i = 0; i < 32; i++)
                if(i + k < n)
                    _bits[i + k] = val & (1<<i);
            k += 32;
        }
        for(; k < n; k++)
            _bits[k] = false;
    }

    template<typename T>
    static Signal from_array(T vals)
    {
        size_t k, i;
        Signal ret;

        k = 0;
        for (auto val : vals) {
            for(i = 0; i < 32; i++)
                if(i + k < n)
                    ret._bits[i + k] = val & (1<<i);
            k += 32;
        }
        for(; k < n; k++)
            ret._bits[k] = false;
        return ret;
    }

    static Signal from_signed(int32_t val)
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            if(i < 32)
                ret._bits[i] = val & (1<<i);
            else
                ret._bits[i] = val < 0;
        return ret;
    }
    static Signal repeat(bool b)
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            ret._bits[i] = b;
        return ret;
    }

    int size() const { return n; }
    bool operator[](int i) const { assert(n >= 0 && i < n); return _bits[i]; }

    template<size_t m>
    Signal<m> slice(size_t offset) const
    {
        Signal<m> ret;

        assert(offset + m <= n);
        std::copy(_bits.begin() + offset, _bits.begin() + offset + m, ret._bits.begin());
        return ret;
    }

    bool any() const
    {
        for(int i = 0; i < n; i++)
            if(_bits[i])
                return true;
        return false;
    }

    bool all() const
    {
        for(int i = 0; i < n; i++)
            if(!_bits[i])
                return false;
        return true;
    }

    bool parity() const
    {
        bool result = false;
        for(int i = 0; i < n; i++)
            result ^= _bits[i];
        return result;
    }

    bool sign() const { return _bits[n-1]; }

    template<typename T>
    T as_numeric() const
    {
        T ret = 0;
        for(size_t i = 0; i < std::min<size_t>(sizeof(T) * 8, n); i++)
            if(_bits[i])
                ret |= ((T)1)<<i;
        return ret;
    }

    template<typename T>
    T as_numeric_clamped() const
    {
        for(size_t i = sizeof(T) * 8; i < n; i++)
            if(_bits[i])
                return ~((T)0);
        return as_numeric<T>();
    }

    uint32_t as_int() const { return as_numeric<uint32_t>(); }

private:
    std::string as_string_p2(int b) const {
        std::string ret;
        for(int i = (n - 1) - (n - 1) % b; i >= 0; i -= b)
            ret += "0123456789abcdef"[(*this >> Signal<32>(i)).as_int() & ((1<<b)-1)];
        return ret;
    }
    std::string as_string_b10() const {
        std::string ret;
        if(n < 4) return std::string() + (char)('0' + as_int());
        Signal<n> t = *this;
        Signal<n> b = 10;
        do{
            ret += (char)('0' + (t % b).as_int());
            t = t / b;
        }while(t.any());
        std::reverse(ret.begin(), ret.end());
        return ret;
    }
public:
    std::string as_string(int base = 16, bool showbase = true) const {
        std::string ret;
        if(showbase) {
            ret += std::to_string(n);
            switch(base) {
            case 2: ret += "'b"; break;
            case 8: ret += "'o"; break;
            case 10: ret += "'d"; break;
            case 16: ret += "'h"; break;
            default: assert(0);
            }
        }
        switch(base) {
        case 2: return ret + as_string_p2(1);
        case 8: return ret + as_string_p2(3);
        case 10: return ret + as_string_b10();
        case 16: return ret + as_string_p2(4);
        default: assert(0);
        }
    }
    friend std::ostream &operator << (std::ostream &os, Signal<n> const &s) { return os << s.as_string(); }

    Signal<n> operator ~() const
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            ret._bits[i] = !_bits[i];
        return ret;
    }

    Signal<n> operator -() const
    {
        Signal<n> ret;
        int x = 1;
        for(size_t i = 0; i < n; i++) {
            x += (int)!_bits[i];
            ret._bits[i] = (x & 1) != 0;
            x >>= 1;
        }
        return ret;
    }

    Signal<n> operator +(Signal<n> const &b) const
    {
        Signal<n> ret;
        int x = 0;
        for(size_t i = 0; i < n; i++){
            x += (int)_bits[i] + (int)b._bits[i];
            ret._bits[i] = x & 1;
            x >>= 1;
        }
        return ret;
    }

    Signal<n> operator -(Signal<n> const &b) const
    {
        Signal<n> ret;
        int x = 1;
        for(size_t i = 0; i < n; i++){
            x += (int)_bits[i] + (int)!b._bits[i];
            ret._bits[i] = x & 1;
            x >>= 1;
        }
        return ret;
    }

    Signal<n> operator *(Signal<n> const &b) const
    {
        Signal<n> ret;
        int x = 0;
        for(size_t i = 0; i < n; i++){
            for(size_t j = 0; j <= i; j++)
                x += (int)_bits[j] & (int)b._bits[i-j];
            ret._bits[i] = x & 1;
            x >>= 1;
        }
        return ret;
    }

private:
    Signal<n> divmod(Signal<n> const &b, bool modulo) const
    {
        if(!b.any()) return 0;
        Signal<n> q = 0;
        Signal<n> r = 0;
        for(size_t i = n; i-- != 0; ){
            r = r << Signal<1>(1);
            r._bits[0] = _bits[i];
            if(r >= b){
                r = r - b;
                q._bits[i] = true;
            }
        }
        return modulo ? r : q;
    }
public:

    Signal<n> operator /(Signal<n> const &b) const { return divmod(b, false); }
    Signal<n> operator %(Signal<n> const &b) const { return divmod(b, true); }

    bool operator ==(Signal<n> const &b) const
    {
        for(size_t i = 0; i < n; i++)
            if(_bits[i] != b._bits[i])
                return false;
        return true;
    }

    bool operator >=(Signal<n> const &b) const
    {
        for(size_t i = n; i-- != 0; )
            if(_bits[i] != b._bits[i])
                return _bits[i];
        return true;
    }

    bool operator >(Signal<n> const &b) const
    {
        for(size_t i = n; i-- != 0; )
            if(_bits[i] != b._bits[i])
                return _bits[i];
        return false;
    }

    bool operator !=(Signal<n> const &b) const { return !(*this == b); }
    bool operator <=(Signal<n> const &b) const { return b <= *this; }
    bool operator <(Signal<n> const &b) const { return b < *this; }

    bool signed_greater_than(Signal<n> const &b) const
    {
        if(_bits[n-1] != b._bits[n-1])
            return b._bits[n-1];
        return *this > b;
    }

    bool signed_greater_equal(Signal<n> const &b) const
    {
        if(_bits[n-1] != b._bits[n-1])
            return b._bits[n-1];
        return *this >= b;
    }

    Signal<n> operator &(Signal<n> const &b) const
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            ret._bits[i] = _bits[i] && b._bits[i];
        return ret;
    }

    Signal<n> operator |(Signal<n> const &b) const
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            ret._bits[i] = _bits[i] || b._bits[i];
        return ret;
    }

    Signal<n> operator ^(Signal<n> const &b) const
    {
        Signal<n> ret;
        for(size_t i = 0; i < n; i++)
            ret._bits[i] = _bits[i] != b._bits[i];
        return ret;
    }

    template<size_t nb>
    Signal<n> operator <<(Signal<nb> const &b) const
    {
        Signal<n> ret = 0;
        size_t amount = b.template as_numeric_clamped<size_t>();
        if(amount < n)
            std::copy(_bits.begin(), _bits.begin() + (n - amount), ret._bits.begin() + amount);
        return ret;
    }

    template<size_t nb>
    Signal<n> operator >>(Signal<nb> const &b) const
    {
        Signal<n> ret = 0;
        size_t amount = b.template as_numeric_clamped<size_t>();
        if(amount < n)
            std::copy(_bits.begin() + amount, _bits.end(), ret._bits.begin());
        return ret;
    }

    template<size_t nb>
    Signal<n> arithmetic_shift_right(Signal<nb> const &b) const
    {
        Signal<n> ret = Signal::repeat(sign());
        size_t amount = b.template as_numeric_clamped<size_t>();
        if(amount < n)
            std::copy(_bits.begin() + amount, _bits.end(), ret._bits.begin());
        return ret;
    }

    template<size_t m>
    Signal<n+m> concat(Signal<m> const& b) const
    {
        Signal<n + m> ret;
        std::copy(_bits.begin(), _bits.end(), ret._bits.begin());
        std::copy(b._bits.begin(), b._bits.end(), ret._bits.begin() + n);
        return ret;
    }

    template<size_t m>
    Signal<m> zero_extend() const
    {
        assert(m >= n);
        Signal<m> ret = 0;
        std::copy(_bits.begin(), _bits.end(), ret._bits.begin());
        return ret;
    }

    template<size_t m>
    Signal<m> sign_extend() const
    {
        assert(m >= n);
        Signal<m> ret = Signal<m>::repeat(sign());
        std::copy(_bits.begin(), _bits.end(), ret._bits.begin());
        return ret;
    }
};

template<size_t a, size_t d>
class Memory {
    std::array<Signal<d>, 1<<a> _contents;
public:
    Memory() {}
    Memory(std::array<Signal<d>, 1<<a> const &contents) : _contents(contents) {}
    Signal<d> read(Signal<a> addr) const
    {
        return _contents[addr.template as_numeric<size_t>()];
    }
    Memory write(Signal<a> addr, Signal<d> data) const
    {
        Memory ret = *this;
        ret._contents[addr.template as_numeric<size_t>()] = data;
        return ret;
    }
};

#endif
