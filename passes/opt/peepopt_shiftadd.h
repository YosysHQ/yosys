#ifndef PEEPOPT_SHIFTADD_H
#define PEEPOPT_SHIFTADD_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

//
// Transforms add/sub+shift pairs that result from expressions such as data[s*W +C +:W2]
// specifically something like: out[W2-1:0] = data >> (s*W +C)
// will be transformed into: out[W2-1:0] = (data >> C) >> (s*W)
// this can then be optimized using peepopt_shiftmul_right.h
//

struct PeepoptShiftaddMatch
{
	Cell *shift = nullptr;
	// the right shift amount
	SigSpec shift_amount = {};
	// log2 scale factor in interpreting of shift_amount
	// due to zero padding on the shift cell's B port
	int log2scale = {};
	// zeros at the MSB position make it unsigned
	bool msb_zeros = {};
	bool var_signed = {};
	SigSpec var_signal = {};
	// offset: signed constant value c in data[var+c +:W1] (constant shift-right amount)
	int offset = {};
	Cell *add = nullptr;
};

struct PeepoptShiftadd : MatchPattern<PeepoptShiftadd, PeepoptShiftaddMatch>
{
	struct AddChoice {
		Cell *cell = nullptr;
		IdString constport = {};
		IdString varport = {};
		bool varport_A = {};
		bool is_sub = {};
		bool constport_signed = {};
		bool varport_signed = {};
		bool offset_negative = {};
	};

	bool did_something = {};
	int shiftadd_max_ratio = {};

	vector<Cell*> shift_cells = {};
	MatchIndex<SigSpec, AddChoice> add_index = {};

	PeepoptShiftadd(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptShiftadd::match_shift)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($shift), ID($shiftx), ID($shr)))
				shift_cells.push_back(cell);
			// either data[var+c +:W1] or data[var-c +:W1]
			if (cell->type.in(ID($add), ID($sub))) {
				// one must be constant, the other is variable
				for (IdString constport : {ID::A, ID::B}) {
					if (port(cell, constport).empty())
						continue;
					if (!port(cell, constport).is_fully_const())
						continue;
					IdString varport = (constport == ID::A ? ID::B : ID::A);

					// only optimize for constants up to a fixed width. this prevents cases
					// with a blowup in internal term size and prevents larger constants being
					// casted to int incorrectly
					if (GetSize(port(cell, constport)) > 24)
						continue;

					// if a value of var is able to wrap the output, the transformation might give wrong results
					// an addition/substraction can at most flip one more bit than the largest operand (the carry bit)
					// as long as the output can show this bit, no wrap should occur (assuming all signed-ness make sense)
					if (GetSize(port(cell, ID::Y)) <= max(GetSize(port(cell, ID::A)), GetSize(port(cell, ID::B))))
						continue;

					bool varport_A = (varport == ID::A);
					bool is_sub = cell->type.in(ID($sub));

					bool constport_signed = param(cell, !varport_A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
					bool varport_signed = param(cell, varport_A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
					bool const_negative = (constport_signed && (port(cell, constport).bits().back() == State::S1));
					bool offset_negative = ((is_sub && varport_A) ^ const_negative);

					// checking some value boundaries as well:
					// data[...-c +:W1] is fine for any signed var (pad at LSB, all data still accessible)
					// unsigned shift may underflow (eg var-3 with var<3) -> cannot be converted
					// data[...+c +:W1] is only fine for +var(add) and var unsigned
					// (+c cuts lower C bits, making them inaccessible, a signed var could try to access them)
					// either its an add or the variable port is A (it must be positive)
					if (!cell->type.in(ID($add)) && varport != ID::A)
						continue;

					add_index.add(port(cell, ID::Y), {cell, constport, varport, varport_A, is_sub, constport_signed, varport_signed, offset_negative});
				}
			}
		}
	}

	void match_shift(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *shift : candidates(shift_cells)) {
			if (port(shift, ID::B).empty())
				continue;
			Match n = m;
			n.shift = shift;
			if (descend(frame, shift, &PeepoptShiftadd::code_shift_amount, n))
				return;
		}
	}

	void code_shift_amount(const Match &m)
	{
		Match n = m;
		n.shift_amount = port(n.shift, ID::B);

		n.log2scale = 0;
		while (n.shift_amount[0] == State::S0) {
			n.shift_amount.remove(0);
			if (n.shift_amount.empty()) return;
			n.log2scale++;
		}

		n.msb_zeros = 0;
		while (n.shift_amount.bits().back() == State::S0) {
			n.msb_zeros = true;
			n.shift_amount.remove(GetSize(n.shift_amount) - 1);
			if (n.shift_amount.empty()) return;
		}

		match_add(n);
	}

	void match_add(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[add, constport, varport, varport_A, is_sub, constport_signed, varport_signed, offset_negative] : candidates(add_index.find(m.shift_amount))) {
			// -> data[var+c +:W1] (with var signed) is illegal
			if (!offset_negative && varport_signed)
				continue;
			// -> data >> (var-c) (with var unsigned) is illegal
			if (offset_negative && !varport_signed)
				continue;
			// shift must read B with the add/sub signedness
			if (varport_signed != (param(m.shift, ID::B_SIGNED).as_bool() && !m.msb_zeros))
				continue;
			Match n = m;
			n.add = add;
			// state-variables are assigned at the end only:
			// shift the log2scale offset in-front of add to get true value: (var+c)<<N -> (var<<N)+(c<<N)
			n.offset = ( (port(add, constport).as_int(constport_signed) << n.log2scale) * ( (is_sub && varport_A) ? -1 : 1 ) );
			n.var_signed = varport_signed;
			n.var_signal = add->getPort(varport);
			if (descend(frame, add, &PeepoptShiftadd::code_rewrite, n))
				return;
		}
	}

	void code_rewrite(const Match &m)
	{
		// positive constant offset with a signed variable (index) cannot be handled
		// the above filter should get rid of this case but 'offset' is calculated differently
		// it should only differ if previous passes create invalid data
		log_assert(!(m.offset>0 && m.var_signed));

		SigSpec old_a = port(m.shift, ID::A); // data
		std::string location = m.shift->get_src_attribute();

		if(shiftadd_max_ratio>0 && m.offset<0 && -m.offset*shiftadd_max_ratio > old_a.size()) {
			log_warning("at %s: candiate for shiftadd optimization (shifting '%s' by '%s - %d' bits) "
						"was ignored to avoid high resource usage, see help peepopt\n",
						location.c_str(), log_signal(old_a), log_signal(m.var_signal), -m.offset);
			return;
		}

		// $shr and $shift sign-extend A to max(A_WIDTH, Y_WIDTH), so bake that in
		// before reslicing A and clear A_SIGNED, or it gets applied twice
		bool a_signed = m.shift->type.in(ID($shr), ID($shift)) && param(m.shift, ID::A_SIGNED).as_bool();
		if (a_signed && !old_a.empty())
			old_a.extend_u0(max(GetSize(old_a), GetSize(port(m.shift, ID::Y))), true);

		did_something = true;
		log("shiftadd pattern in %s: shift=%s, add/sub=%s, offset: %d\n",
				module, m.shift, m.add, m.offset);

		SigSpec new_a = {};
		if(m.offset<0) {
			// data >> (...-c) transformed to {data, c'X} >> (...)
			SigSpec padding( (m.shift->type.in(ID($shiftx)) ? State::Sx : State::S0), -m.offset );
			new_a.append(padding);
			new_a.append(old_a);
		} else {
			// data >> (...+c) transformed to data[MAX:c] >> (...)
			if(m.offset < GetSize(old_a)) { // some signal bits left?
				new_a.append(old_a.extract_end(m.offset));
			} else {
				// warn user in case data is empty (no bits left)
				if (location.empty())
					location = m.shift->name.str();
				if(m.shift->type.in(ID($shiftx)))
					log_warning("at %s: result of indexed part-selection is always constant (selecting from '%s' with index '%s + %d')\n",
								location.c_str(), log_signal(old_a), log_signal(m.var_signal), m.offset);
				else
					log_warning("at %s: result of shift operation is always constant (shifting '%s' by '%s + %d' bits)\n",
								location.c_str(), log_signal(old_a), log_signal(m.var_signal), m.offset);
			}
		}

		SigSpec new_b = {m.var_signal, SigSpec(State::S0, m.log2scale)};
		if (m.msb_zeros || !m.var_signed)
			new_b.append(State::S0);

		m.shift->setPort(ID::A, new_a);
		m.shift->setParam(ID::A_WIDTH, GetSize(new_a));
		if (a_signed)
			m.shift->setParam(ID::A_SIGNED, 0);
		m.shift->setPort(ID::B, new_b);
		m.shift->setParam(ID::B_WIDTH, GetSize(new_b));
		blacklist(m.add);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
