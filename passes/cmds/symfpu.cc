/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/log_help.h"
#include "kernel/yosys.h"

#include "libs/symfpu/baseTypes/shared.h"
#include "libs/symfpu/core/add.h"
#include "libs/symfpu/core/divide.h"
#include "libs/symfpu/core/ite.h"
#include "libs/symfpu/core/multiply.h"
#include "libs/symfpu/core/packing.h"
#include "libs/symfpu/core/unpackedFloat.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct prop;

template <bool is_signed> struct bv;

struct rm {
	enum class mode { RNE, RNA, RTP, RTN, RTZ };
	mode mode;

	prop operator==(rm op) const;
};

thread_local Module *symfpu_mod = nullptr;

struct rtlil_traits {
	typedef uint64_t bwt;
	typedef rm rm;
	typedef symfpu::shared::floatingPointTypeInfo fpt;
	typedef prop prop;
	typedef bv<true> sbv;
	typedef bv<false> ubv;

	// Return an instance of each rounding mode.
	static rm RNE(void) { return {rm::mode::RNE}; };
	static rm RNA(void) { return {rm::mode::RNA}; };
	static rm RTP(void) { return {rm::mode::RTP}; };
	static rm RTN(void) { return {rm::mode::RTN}; };
	static rm RTZ(void) { return {rm::mode::RTZ}; };

	// Handle various invariants.
	// These can be empty to start with.
	static void precondition(const bool b) { assert(b); }
	static void postcondition(const bool b) { assert(b); }
	static void invariant(const bool b) { assert(b); }
	static void precondition(const prop &p);
	static void postcondition(const prop &p);
	static void invariant(const prop &p);
};

using bwt = rtlil_traits::bwt;
using fpt = rtlil_traits::fpt;
using ubv = rtlil_traits::ubv;
using sbv = rtlil_traits::sbv;
using symfpu::ite;
using uf = symfpu::unpackedFloat<rtlil_traits>;

PRIVATE_NAMESPACE_END

namespace symfpu
{
template <> struct ite<prop, prop> {
	static prop iteOp(const prop &cond, const prop &t, const prop &e);
};
template <bool is_signed> struct ite<prop, bv<is_signed>> {
	static bv<is_signed> iteOp(const prop &cond, const bv<is_signed> &t, const bv<is_signed> &e);
};
template <> struct ite<bool, prop> {
	static prop iteOp(bool cond, const prop &t, const prop &e);
};
template <bool is_signed> struct ite<bool, bv<is_signed>> {
	static bv<is_signed> iteOp(bool cond, const bv<is_signed> &t, const bv<is_signed> &e);
};
} // namespace symfpu

PRIVATE_NAMESPACE_BEGIN

struct prop {
	SigBit bit;

	explicit prop(SigBit bit) : bit(bit) {}
	prop(bool v) : bit(v) {}

	prop operator&&(const prop &op) const { return prop{symfpu_mod->And(NEW_ID, bit, op.bit)}; }
	prop operator||(const prop &op) const { return prop{symfpu_mod->Or(NEW_ID, bit, op.bit)}; }
	prop operator^(const prop &op) const { return prop{symfpu_mod->Xor(NEW_ID, bit, op.bit)}; }
	prop operator!() const { return prop{symfpu_mod->Not(NEW_ID, bit)}; }

	prop operator==(const prop &op) const { return prop{symfpu_mod->Eq(NEW_ID, bit, op.bit)}; }

	const prop &named(std::string_view s) const
	{
		symfpu_mod->connect(symfpu_mod->addWire(symfpu_mod->uniquify(stringf("\\%s", s))), bit);
		return *this;
	}
};

template <bool is_signed> struct bv {
	SigSpec bits;

	const bv &named(std::string_view s) const
	{
		symfpu_mod->connect(symfpu_mod->addWire(symfpu_mod->uniquify(stringf("\\%s", s)), bits.size()), bits);
		return *this;
	}

	friend ite<prop, bv<is_signed>>;

	explicit bv(SigSpec bits) : bits(bits) {}
	explicit bv(prop prop) : bits(prop.bit) {}
	explicit bv(bwt w, unsigned v) { bits = Const((long long)v, w); }
	bv(bv<!is_signed> const &other) : bits(other.bits) {}

	bwt getWidth() const { return bits.size(); }

	static bv<is_signed> one(bwt w) { return bv{SigSpec(1, w)}; }
	static bv<is_signed> zero(bwt w) { return bv{SigSpec(0, w)}; }
	static bv<is_signed> allOnes(bwt w) { return bv{SigSpec(State::S1, w)}; }

	static bv<is_signed> maxValue(bwt w)
	{
		if (!is_signed)
			return allOnes(w);
		log_assert(w > 0);
		Const value = Const(State::S1, w);
		value.set(w - 1, State::S0);
		return bv{SigSpec(value)};
	}
	static bv<is_signed> minValue(bwt w)
	{

		if (!is_signed)
			return zero(w);
		log_assert(w > 0);
		Const value = Const(State::S0, w);
		value.set(w - 1, State::S1);
		return bv{SigSpec(value)};
	}

	bv toSigned(void) const { return bv<true>(*this); }
	bv toUnsigned(void) const { return bv<false>(*this); }

	bv<is_signed> extract(bwt upper, bwt lower) const
	{
		return bv{bits.extract(lower, upper + 1 - lower)};
	}

	bv<is_signed> extend(bwt extension) const
	{
		auto extended_bits = bits;
		extended_bits.extend_u0(bits.size() + extension, is_signed);
		return bv{extended_bits};
	}

	inline bv<is_signed> matchWidth(const bv<is_signed> &op) const
	{
		log_assert(this->getWidth() <= op.getWidth());
		return this->extend(op.getWidth() - this->getWidth());
	}

	inline bv<is_signed> resize(bwt newSize) const
	{
		bwt width = this->getWidth();

		if (newSize > width) {
			return this->extend(newSize - width);
		} else if (newSize < width) {
			return this->extract(newSize - 1, 0);
		} else {
			return *this;
		}
	}

	inline bv<is_signed> contract(bwt reduction) const
	{
		log_assert(getWidth() > reduction);
		return resize(getWidth() - reduction);
	}

	bv<is_signed> append(const bv<is_signed> &op) const { return bv{SigSpec({bits, op.bits})}; }

	prop isAllOnes() const { return prop{symfpu_mod->ReduceAnd(NEW_ID, bits)}; }
	prop isAllZeros() const { return prop{symfpu_mod->ReduceAnd(NEW_ID, symfpu_mod->Not(NEW_ID, bits))}; }

	bv<is_signed> operator-() const { return bv{symfpu_mod->Neg(NEW_ID, bits, is_signed)}; }
	bv<is_signed> operator~() const { return bv{symfpu_mod->Not(NEW_ID, bits, is_signed)}; }

	bv<is_signed> operator+(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return bv{symfpu_mod->Add(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator-(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return bv{symfpu_mod->Sub(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator*(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		log_assert(!is_signed);
		return bv{symfpu_mod->Mul(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator%(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		log_assert(!is_signed);
		return bv{symfpu_mod->Mod(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator/(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		log_assert(!is_signed);
		return bv{symfpu_mod->Div(NEW_ID, bits, op.bits, is_signed)};
	}

	bv<is_signed> operator|(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return bv{symfpu_mod->Or(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator&(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return bv{symfpu_mod->And(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator<<(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return bv{symfpu_mod->Shl(NEW_ID, bits, op.bits, is_signed)};
	}
	bv<is_signed> operator>>(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
        if (is_signed)
            return bv{symfpu_mod->Sshr(NEW_ID, bits, op.bits, is_signed)};
        else
    		return bv{symfpu_mod->Shr(NEW_ID, bits, op.bits, is_signed)};
	}

	prop operator==(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return prop{symfpu_mod->Eq(NEW_ID, bits, op.bits, is_signed)};
	}

	prop operator<=(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return prop{symfpu_mod->Le(NEW_ID, bits, op.bits, is_signed)};
	}
	prop operator>=(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return prop{symfpu_mod->Ge(NEW_ID, bits, op.bits, is_signed)};
	}

	prop operator<(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return prop{symfpu_mod->Lt(NEW_ID, bits, op.bits, is_signed)};
	}
	prop operator>(const bv<is_signed> &op) const
	{
		log_assert(getWidth() == op.getWidth());
		return prop{symfpu_mod->Gt(NEW_ID, bits, op.bits, is_signed)};
	}

	inline bv<is_signed> increment() const { return *this + one(getWidth()); }
	inline bv<is_signed> decrement() const { return *this - one(getWidth()); }

	inline bv<is_signed> modularLeftShift(const bv<is_signed> &op) const { return *this << op; }

	inline bv<is_signed> modularRightShift(const bv<is_signed> &op) const { return *this >> op; }

	inline bv<is_signed> modularIncrement() const { return this->increment(); }

	inline bv<is_signed> modularDecrement() const { return this->decrement(); }

	inline bv<is_signed> modularAdd(const bv<is_signed> &op) const { return *this + op; }
	inline bv<is_signed> modularSubtract(const bv<is_signed> &op) const { return *this - op; }

	inline bv<is_signed> modularNegate() const { return -(*this); }

	inline bv<is_signed> signExtendRightShift(const bv<is_signed> &op) const { return bv{sbv(sbv(*this) >> sbv(op))}; }
};

PRIVATE_NAMESPACE_END

prop symfpu::ite<prop, prop>::iteOp(const prop &cond, const prop &t, const prop &e) { return prop{symfpu_mod->Mux(NEW_ID, e.bit, t.bit, cond.bit)}; }

template <bool is_signed> bv<is_signed> symfpu::ite<prop, bv<is_signed>>::iteOp(const prop &cond, const bv<is_signed> &t, const bv<is_signed> &e)
{
	log_assert(t.getWidth() == e.getWidth());
	return bv<is_signed>{symfpu_mod->Mux(NEW_ID, e.bits, t.bits, cond.bit)};
}

prop symfpu::ite<bool, prop>::iteOp(bool cond, const prop &t, const prop &e) { return cond ? t : e; }

template <bool is_signed> bv<is_signed> symfpu::ite<bool, bv<is_signed>>::iteOp(bool cond, const bv<is_signed> &t, const bv<is_signed> &e)
{
	log_assert(t.getWidth() == e.getWidth());
	return cond ? t : e;
}

PRIVATE_NAMESPACE_BEGIN

prop rm::operator==(rm op) const { return mode == op.mode; }

void rtlil_traits::precondition(const prop &cond)
{
	Cell *cell = symfpu_mod->addAssert(NEW_ID, cond.bit, State::S1);
	cell->set_bool_attribute(ID(symfpu_pre));
}
void rtlil_traits::postcondition(const prop &cond)
{
	Cell *cell = symfpu_mod->addAssert(NEW_ID, cond.bit, State::S1);
	cell->set_bool_attribute(ID(symfpu_post));
}
void rtlil_traits::invariant(const prop &cond)
{
	Cell *cell = symfpu_mod->addAssert(NEW_ID, cond.bit, State::S1);
	cell->set_bool_attribute(ID(symfpu_inv));
}

ubv input_ubv(IdString name, int width)
{
	auto input = symfpu_mod->addWire(name, width);
	input->port_input = true;
	return ubv(SigSpec(input));
}

void output_ubv(IdString name, const ubv &value)
{
	auto output = symfpu_mod->addWire(name, value.getWidth());
	symfpu_mod->connect(output, value.bits);
	output->port_output = true;
}

struct SymFpuPass : public Pass {
	SymFpuPass() : Pass("symfpu", "SymFPU based floating point netlist generator") {}
	bool formatted_help() override
	{
		auto *help = PrettyHelp::get_current();
		help->set_group("formal");

		auto content_root = help->get_root();

		content_root->usage("symfpu [options]");
		content_root->paragraph("TODO");

		content_root->option("-eb <N>", "use <N> bits for exponent; default=8");
		content_root->option("-sb <N>", "use <N> bits for significand, including hidden bit; default=24");

		return true;
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int eb = 8, sb = 24;
		log_header(design, "Executing SYMFPU pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-eb" && argidx+1 < args.size()) {
				eb = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-sb" && argidx+1 < args.size()) {
				sb = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);

		fpt format(eb, sb);

		auto mod = design->addModule(ID(symfpu));

		symfpu_mod = mod;

		uf a = symfpu::unpack<rtlil_traits>(format, input_ubv(ID(a), eb+sb));
		uf b = symfpu::unpack<rtlil_traits>(format, input_ubv(ID(b), eb+sb));

		uf added(symfpu::add<rtlil_traits>(format, rtlil_traits::RNE(), a, b, prop(true)));
		uf multiplied(symfpu::multiply<rtlil_traits>(format, rtlil_traits::RNE(), a, b));
		uf divided(symfpu::divide<rtlil_traits>(format, rtlil_traits::RNE(), a, b));

		output_ubv(ID(added), symfpu::pack<rtlil_traits>(format, added));
		output_ubv(ID(multiplied), symfpu::pack<rtlil_traits>(format, multiplied));
		output_ubv(ID(divided), symfpu::pack<rtlil_traits>(format, divided));
		symfpu_mod->fixup_ports();
	}
} SymFpuPass;

PRIVATE_NAMESPACE_END
