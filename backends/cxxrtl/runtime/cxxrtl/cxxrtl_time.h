/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Catherine <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
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

#ifndef CXXRTL_TIME_H
#define CXXRTL_TIME_H

#include <cinttypes>
#include <string>

#include <cxxrtl/cxxrtl.h>

namespace cxxrtl {

// A timestamp or a difference in time, stored as a 96-bit number of femtoseconds (10e-15 s). The range and resolution
// of this format can represent any VCD timestamp within approx. ±1255321.2 years, without the need for a timescale.
class time {
public:
	static constexpr size_t bits = 96; // 3 chunks

private:
	static constexpr size_t resolution_digits = 15;

	static_assert(sizeof(chunk_t) == 4, "a chunk is expected to be 32-bit");
	static constexpr value<bits> resolution = value<bits> {
		chunk_t(1000000000000000ull & 0xffffffffull), chunk_t(1000000000000000ull >> 32), 0u
	};

	// Signed number of femtoseconds from the beginning of time.
	value<bits> raw;

public:
	constexpr time() {}

	explicit constexpr time(const value<bits> &raw) : raw(raw) {}
	explicit operator const value<bits> &() const { return raw; }

	static constexpr time maximum() {
		return time(value<bits> { 0xffffffffu, 0xffffffffu, 0x7fffffffu });
	}

	time(int64_t secs, int64_t femtos) {
		value<64> secs_val;
		secs_val.set(secs);
		value<64> femtos_val;
		femtos_val.set(femtos);
		raw = secs_val.sext<bits>().mul<bits>(resolution).add(femtos_val.sext<bits>());
	}

	bool is_zero() const {
		return raw.is_zero();
	}

	// Extracts the sign of the value.
	bool is_negative() const {
		return raw.is_neg();
	}

	// Extracts the number of whole seconds. Negative if the value is negative.
	int64_t secs() const {
		return raw.sdivmod(resolution).first.trunc<64>().get<int64_t>();
	}

	// Extracts the number of femtoseconds in the fractional second. Negative if the value is negative.
	int64_t femtos() const {
		return raw.sdivmod(resolution).second.trunc<64>().get<int64_t>();
	}

	bool operator==(const time &other) const {
		return raw == other.raw;
	}

	bool operator!=(const time &other) const {
		return raw != other.raw;
	}

	bool operator>(const time &other) const {
		return other.raw.scmp(raw);
	}

	bool operator>=(const time &other) const {
		return !raw.scmp(other.raw);
	}

	bool operator<(const time &other) const {
		return raw.scmp(other.raw);
	}

	bool operator<=(const time &other) const {
		return !other.raw.scmp(raw);
	}

	time operator+(const time &other) const {
		return time(raw.add(other.raw));
	}

	time &operator+=(const time &other) {
		*this = *this + other;
		return *this;
	}

	time operator-() const {
		return time(raw.neg());
	}

	time operator-(const time &other) const {
		return *this + (-other);
	}

	time &operator-=(const time &other) {
		*this = *this - other;
		return *this;
	}

	operator std::string() const {
		char buf[48]; // x=2**95; len(f"-{x/1_000_000_000_000_000}.{x^1_000_000_000_000_000}") == 48
		int64_t secs = this->secs();
		int64_t femtos = this->femtos();
		snprintf(buf, sizeof(buf), "%s%" PRIi64 ".%015" PRIi64,
			is_negative() ? "-" : "", secs >= 0 ? secs : -secs, femtos >= 0 ? femtos : -femtos);
		return buf;
	}

#if __cplusplus >= 201603L
	[[nodiscard("ignoring parse errors")]]
#endif
	bool parse(const std::string &str) {
		enum {
			parse_sign_opt,
			parse_integral,
			parse_fractional,
		} state = parse_sign_opt;
		bool negative = false;
		int64_t integral = 0;
		int64_t fractional = 0;
		size_t frac_digits = 0;
		for (auto chr : str) {
			switch (state) {
				case parse_sign_opt:
					state = parse_integral;
					if (chr == '+' || chr == '-') {
						negative = (chr == '-');
						break;
					}
					/* fallthrough */
				case parse_integral:
					if (chr >= '0' && chr <= '9') {
						integral *= 10;
						integral += chr - '0';
					} else if (chr == '.') {
						state = parse_fractional;
					} else {
						return false;
					}
					break;
				case parse_fractional:
					if (chr >= '0' && chr <= '9' && frac_digits < resolution_digits) {
						fractional *= 10;
						fractional += chr - '0';
						frac_digits++;
					} else {
						return false;
					}
					break;
			}
		}
		if (frac_digits == 0)
			return false;
		while (frac_digits++ < resolution_digits)
			fractional *= 10;
		*this = negative ? -time { integral, fractional} : time { integral, fractional };
		return true;
	}
};

// Out-of-line definition required until C++17.
constexpr value<time::bits> time::resolution;

std::ostream &operator<<(std::ostream &os, const time &val) {
	os << (std::string)val;
	return os;
}

// These literals are (confusingly) compatible with the ones from `std::chrono`: the `std::chrono` literals do not
// have an underscore (e.g. 1ms) and the `cxxrtl::time` literals do (e.g. 1_ms). This syntactic difference is
// a requirement of the C++ standard. Despite being compatible the literals should not be mixed in the same namespace.
namespace time_literals {

time operator""_s(unsigned long long seconds) {
	return time { (int64_t)seconds, 0 };
}

time operator""_ms(unsigned long long milliseconds) {
	return time { 0, (int64_t)milliseconds * 1000000000000 };
}

time operator""_us(unsigned long long microseconds) {
	return time { 0, (int64_t)microseconds * 1000000000 };
}

time operator""_ns(unsigned long long nanoseconds) {
	return time { 0, (int64_t)nanoseconds * 1000000 };
}

time operator""_ps(unsigned long long picoseconds) {
	return time { 0, (int64_t)picoseconds * 1000 };
}

time operator""_fs(unsigned long long femtoseconds) {
	return time { 0, (int64_t)femtoseconds };
}

};

};

#endif
