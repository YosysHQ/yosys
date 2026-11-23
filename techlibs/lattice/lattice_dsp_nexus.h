#ifndef LATTICE_DSP_NEXUS_H
#define LATTICE_DSP_NEXUS_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// $add and $sub are signed only if both operands are
inline bool nexus_add_signed(Cell *add) { return add->getParam(ID::A_SIGNED).as_bool() && add->getParam(ID::B_SIGNED).as_bool(); }

// Bits [0, width) of the exact product of mul, or empty if its Y cuts them off
inline SigSpec nexus_product_bits(Cell *mul, const SigSpec &mul_y, int width)
{
	int full_width = GetSize(mul->getPort(ID::A)) + GetSize(mul->getPort(ID::B));
	if (GetSize(mul_y) < width && GetSize(mul_y) < full_width)
		return SigSpec();

	SigSpec bits = mul_y;
	bits.extend_u0(width, mul->getParam(ID::A_SIGNED).as_bool());
	return bits;
}

// True if an adder operand, extended as the adder does, is value
inline bool nexus_operand_is(SigSpec operand, bool add_signed, const SigSpec &value)
{
	if (value.empty())
		return false;
	operand.extend_u0(GetSize(value), add_signed);
	return operand == value;
}

struct NexusMac9_4LaneMatch
{
	Cell *add3 = nullptr;
	Cell *mul3 = nullptr;
	Cell *add2 = nullptr;
	Cell *mul2 = nullptr;
	Cell *add1 = nullptr;
	Cell *mul1 = nullptr;
	Cell *add0 = nullptr;
	Cell *mul0 = nullptr;
};

// maccmap -unmap adds the addends first, then one product per $add:
// (((C + P0) + P1) + P2) + P3, or ((P0 + P1) + P2) + P3 without C
struct NexusMac9_4Lane : MatchPattern<NexusMac9_4Lane, NexusMac9_4LaneMatch>
{
	vector<Cell*> add3_cells = {};
	MatchIndex<SigBit> mul_index = {};
	MatchIndex<SigBit> add_index = {};

	NexusMac9_4Lane(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &NexusMac9_4Lane::match_add3)
	{
		for (auto cell : cells) {
			if (cell->type == ID($add) && GetSize(port(cell, ID::Y)) <= 54)
				add3_cells.push_back(cell);
			if (cell->type == ID($mul) && GetSize(port(cell, ID::A)) <= 9 && GetSize(port(cell, ID::B)) <= 9 && nusers(port(cell, ID::Y)) == 2)
				mul_index.add(port(cell, ID::Y)[0], cell);
			if (cell->type == ID($add) && nusers(port(cell, ID::Y)) == 2)
				add_index.add(port(cell, ID::Y)[0], cell);
		}
	}

	// Bits [0, width) of a partial sum, or empty if it is narrower
	static SigSpec nexus_sum_bits(const SigSpec &sum_y, int width)
	{
		if (GetSize(sum_y) < width)
			return SigSpec();
		return sum_y.extract(0, width);
	}

	void match_add3(const Match &m)
	{
		match_each(m, add3_cells, &Match::add3, &NexusMac9_4Lane::match_mul3);
	}

	void match_mul3(const Match &m)
	{
		match_each(m, mul_index.find(port(m.add3, ID::B)[0]), &Match::mul3, &NexusMac9_4Lane::match_add2);
	}

	void match_add2(const Match &m)
	{
		match_each(m, add_index.find(port(m.add3, ID::A)[0]), &Match::add2, &NexusMac9_4Lane::match_mul2);
	}

	void match_mul2(const Match &m)
	{
		match_each(m, mul_index.find(port(m.add2, ID::B)[0]), &Match::mul2, &NexusMac9_4Lane::match_add1);
	}

	void match_add1(const Match &m)
	{
		match_each(m, add_index.find(port(m.add2, ID::A)[0]), &Match::add1, &NexusMac9_4Lane::match_mul1);
	}

	void match_mul1(const Match &m)
	{
		match_each(m, mul_index.find(port(m.add1, ID::B)[0]), &Match::mul1, &NexusMac9_4Lane::match_add0);
	}

	// C + P0
	void match_add0(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *add0 : candidates(add_index.find(port(m.add1, ID::A)[0]))) {
			Match n = m;
			n.add0 = add0;
			if (descend(frame, add0, &NexusMac9_4Lane::match_mul0, n))
				return;
		}
		Match n = m;
		n.add0 = nullptr;
		match_mul0(n);
	}

	void match_mul0(const Match &m)
	{
		match_each(m, mul_index.find(m.add0 ? port(m.add0, ID::B)[0] : port(m.add1, ID::A)[0]), &Match::mul0, &NexusMac9_4Lane::code_accept);
	}

	void code_accept(const Match &m)
	{
		int width = GetSize(port(m.add3, ID::Y));
		bool is_signed = param(m.mul0, ID::A_SIGNED).as_bool();
		for (auto mul : {m.mul0, m.mul1, m.mul2, m.mul3})
			if (param(mul, ID::A_SIGNED).as_bool() != is_signed || param(mul, ID::B_SIGNED).as_bool() != is_signed)
				return;

		// Each adder must see the exact products and partial sums in the width of the top one
		SigSpec p0 = nexus_product_bits(m.mul0, port(m.mul0, ID::Y), width);
		SigSpec p1 = nexus_product_bits(m.mul1, port(m.mul1, ID::Y), width);
		SigSpec p2 = nexus_product_bits(m.mul2, port(m.mul2, ID::Y), width);
		SigSpec p3 = nexus_product_bits(m.mul3, port(m.mul3, ID::Y), width);
		SigSpec s1 = m.add0 ? nexus_sum_bits(port(m.add0, ID::Y), width) : p0;
		SigSpec s2 = nexus_sum_bits(port(m.add1, ID::Y), width);
		SigSpec s3 = nexus_sum_bits(port(m.add2, ID::Y), width);
		if (!nexus_operand_is(port(m.add3, ID::A), nexus_add_signed(m.add3), s3) || !nexus_operand_is(port(m.add3, ID::B), nexus_add_signed(m.add3), p3))
			return;
		if (!nexus_operand_is(port(m.add2, ID::A), nexus_add_signed(m.add2), s2) || !nexus_operand_is(port(m.add2, ID::B), nexus_add_signed(m.add2), p2))
			return;
		if (!nexus_operand_is(port(m.add1, ID::A), nexus_add_signed(m.add1), s1) || !nexus_operand_is(port(m.add1, ID::B), nexus_add_signed(m.add1), p1))
			return;
		if (m.add0 && !nexus_operand_is(port(m.add0, ID::B), nexus_add_signed(m.add0), p0))
			return;

		SigSpec sigC = {};
		if (m.add0) {
			sigC = port(m.add0, ID::A);
			sigC.extend_u0(width, nexus_add_signed(m.add0));
			// C must not read cells that are removed
			for (auto cell : {m.mul0, m.mul1, m.mul2, m.mul3, m.add0, m.add1, m.add2, m.add3})
				if (!sigC.extract(port(cell, ID::Y)).empty())
					return;
		}
		sigC.extend_u0(54, false);

		SigSpec sigY = port(m.add3, ID::Y);
		if (width < 54)
			sigY.append(module->addWire(NEW_ID, 54 - width));

		Cell *mac = module->addCell(NEW_ID, "$__NX_MAC9X9WIDE_4LANE");
		int i = 0;
		for (auto mul : {m.mul0, m.mul1, m.mul2, m.mul3}) {
			SigSpec sigA = port(mul, ID::A);
			SigSpec sigB = port(mul, ID::B);
			sigA.extend_u0(9, is_signed);
			sigB.extend_u0(9, is_signed);
			mac->setPort(stringf("\\A%d", i), sigA);
			mac->setPort(stringf("\\B%d", i), sigB);
			i++;
		}
		mac->setPort(ID::C, sigC);
		mac->setPort(ID::Y, sigY);
		mac->setParam(ID::SIGNED, is_signed ? State::S1 : State::S0);

		for (auto cell : {m.mul0, m.mul1, m.mul2, m.mul3, m.add0, m.add1, m.add2, m.add3})
			autoremove(cell);

		accept(m);
	}
};

struct NexusMacMatch
{
	IdString add_AB = {};
	IdString add_C = {};
	IdString mux_add = {};
	IdString mux_mul = {};
	Cell *mul = nullptr;
	Cell *add = nullptr;
	Cell *mux = nullptr;
};

struct NexusMac : MatchPattern<NexusMac, NexusMacMatch>
{
	struct PortChoice {
		Cell *cell = nullptr;
		IdString AB = {};
		IdString BA = {};
	};

	vector<Cell*> mul_cells = {};
	MatchIndex<SigBit, PortChoice> add_index = {};
	MatchIndex<SigSpec, PortChoice> mux_index = {};

	NexusMac(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &NexusMac::match_mul)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($mul)) && param(cell, ID::A_SIGNED).as_bool() == param(cell, ID::B_SIGNED).as_bool() && GetSize(port(cell, ID::A)) <= 36 && GetSize(port(cell, ID::B)) <= 36)
				mul_cells.push_back(cell);
			if (cell->type.in(ID($add), ID($sub)) && GetSize(port(cell, ID::Y)) <= 108)
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					add_index.add(port(cell, AB)[0], {cell, AB, BA});
				}
			if (cell->type == ID($mux))
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					mux_index.add(port(cell, AB), {cell, AB, BA});
				}
		}
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_cells, &Match::mul, &NexusMac::match_add);
	}

	void match_add(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[add, AB, BA] : candidates(add_index.find(port(m.mul, ID::Y)[0]))) {
			if (add->type != ID($add) && AB != ID::B)
				continue;
			Match n = m;
			n.add = add;
			n.add_AB = AB;
			n.add_C = BA;
			if (descend(frame, add, &NexusMac::match_mux, n))
				return;
		}
	}

	// Clear: S ? A * B : C + A * B becomes (S ? 0 : C) + A * B
	void match_mux(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[mux, AB, BA] : candidates(mux_index.find(port(m.add, ID::Y)))) {
			Match n = m;
			n.mux = mux;
			n.mux_add = AB;
			n.mux_mul = BA;
			if (descend(frame, mux, &NexusMac::code_accept, n))
				return;
		}
		Match n = m;
		n.mux = nullptr;
		code_accept(n);
	}

	void code_accept(const Match &m)
	{
		int width = GetSize(port(m.add, ID::Y));
		bool add_signed = nexus_add_signed(m.add);
		SigSpec product = nexus_product_bits(m.mul, port(m.mul, ID::Y), width);
		if (!nexus_operand_is(port(m.add, m.add_AB), add_signed, product))
			return;

		SigSpec sigC = port(m.add, m.add_C);
		if (!sigC.extract(port(m.mul, ID::Y)).empty())
			return;

		if (m.mux) {
			if (m.add->type != ID($add) || port(m.mux, m.mux_mul) != product)
				return;
			// Don't read removed cells
			SigSpec sel = port(m.mux, ID::S);
			if (!sel.extract(port(m.mul, ID::Y)).empty() || !sel.extract(port(m.add, ID::Y)).empty())
				return;
			if (nusers(port(m.mul, ID::Y)) != 3 || nusers(port(m.add, ID::Y)) != 2)
				return;
		} else if (nusers(port(m.mul, ID::Y)) != 2) {
			return;
		}

		bool narrow_mul = GetSize(port(m.mul, ID::A)) <= 18 && GetSize(port(m.mul, ID::B)) <= 18;
		// Narrow muls don't take a whole 36x36 block for a wide sum
		if (narrow_mul && width > 54)
			return;
		int ab_width = narrow_mul ? 18 : 36;
		int z_width = narrow_mul ? 54 : 108;

		bool ab_signed = param(m.mul, ID::A_SIGNED).as_bool();
		SigSpec sigA = port(m.mul, ID::A);
		SigSpec sigB = port(m.mul, ID::B);
		SigSpec sigY = m.mux ? port(m.mux, ID::Y) : port(m.add, ID::Y);
		sigA.extend_u0(ab_width, ab_signed);
		sigB.extend_u0(ab_width, ab_signed);
		sigC.extend_u0(width, add_signed);
		if (m.mux) {
			SigSpec zero(State::S0, width);
			SigSpec sel = port(m.mux, ID::S);
			if (m.mux_add == ID::A)
				sigC = module->Mux(NEW_ID, sigC, zero, sel);
			else
				sigC = module->Mux(NEW_ID, zero, sigC, sel);
		}
		sigC.extend_u0(z_width, false);
		if (width < z_width)
			sigY.append(module->addWire(NEW_ID, z_width - width));

		Cell *mac = module->addCell(NEW_ID, narrow_mul ? "$__NX_MAC18X18" : "$__NX_MAC36X36");
		mac->setPort(ID::A, sigA);
		mac->setPort(ID::B, sigB);
		mac->setPort(ID::C, sigC);
		mac->setPort(ID::Y, sigY);
		mac->setParam(ID::A_SIGNED, param(m.mul, ID::A_SIGNED));
		mac->setParam(ID::SUBTRACT, m.add->type == ID($sub) ? State::S1 : State::S0);

		autoremove(m.mul);
		autoremove(m.add);
		autoremove(m.mux);

		accept(m);
	}
};

struct NexusPreadd18Match
{
	Cell *preadd = nullptr;
	Cell *mul = nullptr;
	Cell *pipe_ff = nullptr;
};

struct NexusPreadd18 : MatchPattern<NexusPreadd18, NexusPreadd18Match>
{
	vector<Cell*> preadd_cells = {};
	MatchIndex<SigBit> mul_index = {};
	MatchIndex<SigBit> pipe_ff_index = {};

	NexusPreadd18(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &NexusPreadd18::match_preadd)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($add), ID($sub)) && GetSize(port(cell, ID::Y)) <= 19 && nusers(port(cell, ID::Y)) == 2)
				preadd_cells.push_back(cell);
			if (cell->type.in(ID($mul)) && GetSize(port(cell, ID::Y)) <= 48)
				for (IdString mul_AB : {ID::A, ID::B})
					mul_index.add(port(cell, mul_AB)[0], cell);
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)))
				pipe_ff_index.add(port(cell, ID::D)[0], cell);
		}
	}

	void match_preadd(const Match &m)
	{
		match_each(m, preadd_cells, &Match::preadd, &NexusPreadd18::match_mul);
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_index.find(port(m.preadd, ID::Y)[0]), &Match::mul, &NexusPreadd18::match_pipe_ff);
	}

	void match_pipe_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *pipe_ff : candidates(pipe_ff_index.find(port(m.mul, ID::Y)[0]))) {
			if (nusers(port(m.mul, ID::Y)) != 2)
				continue;
			Match n = m;
			n.pipe_ff = pipe_ff;
			if (descend(frame, pipe_ff, &NexusPreadd18::code_accept, n))
				return;
		}
		Match n = m;
		n.pipe_ff = nullptr;
		code_accept(n);
	}

	void code_accept(const Match &m)
	{
		SigSpec preadd_out = port(m.preadd, ID::Y);
		IdString actual_mul_AB = {};

		if (GetSize(port(m.mul, ID::A)) >= GetSize(preadd_out) && port(m.mul, ID::A).extract(0, GetSize(preadd_out)) == preadd_out) {
			actual_mul_AB = ID::A;
		} else if (GetSize(port(m.mul, ID::B)) >= GetSize(preadd_out) && port(m.mul, ID::B).extract(0, GetSize(preadd_out)) == preadd_out) {
			actual_mul_AB = ID::B;
		} else {
			return;
		}

		Cell *mac = module->addCell(NEW_ID, "$__NX_PREADD18X18");

		IdString mul_other = (actual_mul_AB == ID::A) ? ID::B : ID::A;
		IdString sgn_AC = (mul_other == ID::A) ? ID::B_SIGNED : ID::A_SIGNED;
		IdString sgn_B = (mul_other == ID::A) ? ID::A_SIGNED : ID::B_SIGNED;

		SigSpec sig_A = port(m.preadd, ID::A);
		SigSpec sig_C = port(m.preadd, ID::B);
		SigSpec sig_B = port(m.mul, mul_other);

		sig_A.extend_u0(18, false);
		sig_C.extend_u0(18, false);
		sig_B.extend_u0(18, false);

		mac->setPort(ID::A, sig_A.extract(0, 18));
		mac->setPort(ID::C, sig_C.extract(0, 18));
		mac->setPort(ID::B, sig_B.extract(0, 18));

		if (m.pipe_ff) {
			mac->setPort(ID::Y, port(m.pipe_ff, ID::Q));
			mac->setPort(ID::CLK, port(m.pipe_ff, ID::CLK));
			mac->setParam(ID::PIPELINED, State::S1);
		} else {
			mac->setPort(ID::Y, port(m.mul, ID::Y));
			mac->setPort(ID::CLK, State::S0);
			mac->setParam(ID::PIPELINED, State::S0);
		}

		mac->setParam(ID::A_SIGNED, m.mul->getParam(sgn_AC));
		mac->setParam(ID::B_SIGNED, m.mul->getParam(sgn_B));
		mac->setParam(ID::C_SIGNED, m.mul->getParam(sgn_AC));

		if (m.pipe_ff) autoremove(m.pipe_ff);
		autoremove(m.mul);
		autoremove(m.preadd);

		accept(m);
	}
};

struct NexusMulRegMatch
{
	SigBit clk = {};
	SigSpec argQ = {};
	SigSpec argD = {};
	Cell *ffA = nullptr;
	Cell *ffB = nullptr;
	Cell *ffY = nullptr;
	Cell *mul = nullptr;
	Cell *ff = nullptr;
};

struct NexusMulReg : MatchPattern<NexusMulReg, NexusMulRegMatch>
{
	Cell *dff = nullptr;
	SigBit dffclk = {};

	vector<Cell*> mul_cells = {};
	MatchIndex<SigSpec> in_ff_index = {};
	MatchIndex<SigSpec> out_ff_index = {};

	NexusMulReg(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &NexusMulReg::match_mul)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($mul)) && GetSize(port(cell, ID::A)) <= 36 && GetSize(port(cell, ID::B)) <= 36 && GetSize(port(cell, ID::Y)) <= 72)
				mul_cells.push_back(cell);
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)) && param(cell, ID::CLK_POLARITY).as_bool()) {
				in_ff_index.add(port(cell, ID::Q), cell);
				out_ff_index.add(port(cell, ID::D), cell);
			}
		}
	}

	SigBit ce_of(Cell *ff)
	{
		if (!ff) return State::S0;

		if (ff->type.in(ID($dffe), ID($sdffe))) {
			SigBit e = port(ff, ID::EN)[0];
			if (!ff->getParam(ID::EN_POLARITY).as_bool())
				e = module->NotGate(NEW_ID, e);

			return e;
		}

		return State::S1; // Always enabled
	}

	SigBit rst_of(Cell *ff)
	{
		if (!ff) return State::S0;

		if (ff->type.in(ID($sdff), ID($sdffe))) {
			SigBit r = port(ff, ID::SRST)[0];
			if (!ff->getParam(ID::SRST_POLARITY).as_bool())
				r = module->NotGate(NEW_ID, r);

			return r;
		}

		return State::S0; // No reset
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_cells, &Match::mul, &NexusMulReg::code_ffA);
	}

	// Absorb the pipeline FF on each mul input
	void code_ffA(const Match &m)
	{
		Match n = m;
		n.argQ = port(n.mul, ID::A);
		in_ff(n);
		if (unwinding())
			return;
		if (dff) {
			n.ffA = dff;
			n.clk = dffclk;
		}
		code_ffB(n);
	}

	void code_ffB(const Match &m)
	{
		Match n = m;
		n.argQ = port(n.mul, ID::B);
		in_ff(n);
		if (unwinding())
			return;
		if (dff) {
			n.ffB = dff;
			n.clk = dffclk;
		}
		code_ffY(n);
	}

	// Absorb the FF on the mul output
	void code_ffY(const Match &m)
	{
		Match n = m;
		n.argD = port(n.mul, ID::Y);
		out_ff(n);
		if (unwinding())
			return;
		if (dff) {
			n.ffY = dff;
			n.clk = dffclk;
		}
		code_accept(n);
	}

	void code_accept(const Match &m)
	{
		if (!m.ffA && !m.ffB && !m.ffY)
			return;

		int aw = GetSize(port(m.mul, ID::A));
		int bw = GetSize(port(m.mul, ID::B));
		IdString prim = {};
		int A_PINS = {};
		int B_PINS = {};

		if (aw <= 18 && bw <= 18) {
			prim = ID($__NX_MUL18X18);
			A_PINS = 18;
			B_PINS = 18;
		} else if (aw <= 36 && bw <= 18) {
			prim = ID($__NX_MUL36X18);
			A_PINS = 36;
			B_PINS = 18;
		} else if (aw <= 18 && bw <= 36) {
			prim = ID($__NX_MUL36X18);
			A_PINS = 36;
			B_PINS = 18;
		} else {
			prim = ID($__NX_MUL36X36);
			A_PINS = 36;
			B_PINS = 36;
		}

		bool a_signed = m.mul->getParam(ID::A_SIGNED).as_bool();
		bool b_signed = m.mul->getParam(ID::B_SIGNED).as_bool();
		// Drive the DSP from the FF's D
		SigSpec sigA = m.ffA ? port(m.ffA, ID::D) : port(m.mul, ID::A);
		SigSpec sigB = m.ffB ? port(m.ffB, ID::D) : port(m.mul, ID::B);
		SigSpec sigY = m.ffY ? port(m.ffY, ID::Q) : port(m.mul, ID::Y);

		// 36X18 -> wide operand goes to A
		Cell *ffa = m.ffA;
		Cell *ffb = m.ffB;
		if (prim == ID($__NX_MUL36X18) && aw <= 18 && bw <= 36) {
			std::swap(sigA, sigB);
			std::swap(a_signed, b_signed);
			std::swap(ffa, ffb);
		}

		sigA.extend_u0(A_PINS, a_signed);
		sigB.extend_u0(B_PINS, b_signed);

		Cell *cell = module->addCell(NEW_ID, prim);
		cell->setPort(ID::A, sigA);
		cell->setPort(ID::B, sigB);
		cell->setPort(ID::Y, sigY);
		cell->setParam(ID::A_WIDTH, A_PINS);
		cell->setParam(ID::B_WIDTH, B_PINS);
		cell->setParam(ID::Y_WIDTH, GetSize(sigY));
		cell->setParam(ID::A_SIGNED, a_signed ? State::S1 : State::S0);
		cell->setParam(ID::B_SIGNED, b_signed ? State::S1 : State::S0);
		cell->setParam(ID::RESETMODE, std::string("SYNC"));

		cell->setPort(ID::CLK, m.clk != SigBit() ? m.clk : State::S0);
		cell->setPort(ID::CEA, ce_of(ffa));
		cell->setPort(ID::RSTA, rst_of(ffa));
		cell->setPort(ID::CEB, ce_of(ffb));
		cell->setPort(ID::RSTB, rst_of(ffb));
		cell->setPort(ID::CEOUT, ce_of(m.ffY));
		cell->setPort(ID::RSTOUT, rst_of(m.ffY));
		cell->setParam(ID::REGINPUTA, ffa ? std::string("REGISTER") : std::string("BYPASS"));
		cell->setParam(ID::REGINPUTB, ffb ? std::string("REGISTER") : std::string("BYPASS"));
		cell->setParam(ID::REGOUTPUT, m.ffY ? std::string("REGISTER") : std::string("BYPASS"));

		if (ffa) autoremove(ffa);
		if (ffb && ffb != ffa) autoremove(ffb);
		if (m.ffY) autoremove(m.ffY);
		autoremove(m.mul);

		accept(m);
	}

	// Find the input pipeline FF whose Q feeds argQ
	void in_ff(const Match &m)
	{
		dff = nullptr;
		in_ff_match_ff(m);
	}

	void in_ff_match_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *ff : candidates(in_ff_index.find(m.argQ))) {
			if (!ff->type.in(ID($dff), ID($dffe)) && !param(ff, ID::SRST_VALUE).is_fully_zero())
				continue;
			if (GetSize(port(ff, ID::Q)) != GetSize(m.argQ))
				continue;
			if (nusers(port(ff, ID::Q)) != 2)
				continue;
			Match n = m;
			n.ff = ff;
			if (descend(frame, ff, &NexusMulReg::in_ff_code_found, n))
				return;
		}
	}

	void in_ff_code_found(const Match &m)
	{
		if (m.clk != SigBit() && sigmap(port(m.ff, ID::CLK)[0]) != m.clk)
			return;

		for (auto bit : sigmap(port(m.ff, ID::Q))) {
			if (!bit.wire)
				continue;
			auto it = bit.wire->attributes.find(ID::init);
			if (it == bit.wire->attributes.end())
				continue;
			if (bit.offset < GetSize(it->second)) {
				State s = it->second[bit.offset];
				if (s != State::Sx && s != State::S0)
					return;
			}
		}

		dff = m.ff;
		dffclk = sigmap(port(m.ff, ID::CLK)[0]);
	}

	void out_ff(const Match &m)
	{
		dff = nullptr;
		out_ff_match_ff(m);
	}

	void out_ff_match_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *ff : candidates(out_ff_index.find(m.argD))) {
			if (!ff->type.in(ID($dff), ID($dffe)) && !param(ff, ID::SRST_VALUE).is_fully_zero())
				continue;
			if (GetSize(port(ff, ID::D)) != GetSize(m.argD))
				continue;
			if (nusers(port(ff, ID::D)) != 2)
				continue;
			Match n = m;
			n.ff = ff;
			if (descend(frame, ff, &NexusMulReg::out_ff_code_found, n))
				return;
		}
	}

	void out_ff_code_found(const Match &m)
	{
		if (m.clk != SigBit() && sigmap(port(m.ff, ID::CLK)[0]) != m.clk)
			return;

		for (auto bit : sigmap(port(m.ff, ID::Q))) {
			if (!bit.wire)
				continue;
			auto it = bit.wire->attributes.find(ID::init);
			if (it == bit.wire->attributes.end())
				continue;
			if (bit.offset < GetSize(it->second)) {
				State s = it->second[bit.offset];
				if (s != State::Sx && s != State::S0)
					return;
			}
		}

		dff = m.ff;
		dffclk = sigmap(port(m.ff, ID::CLK)[0]);
	}
};

YOSYS_NAMESPACE_END

#endif
