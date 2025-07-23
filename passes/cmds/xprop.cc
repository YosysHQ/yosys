/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/yosys.h"
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct XpropOptions
{
	bool split_inputs = false;
	bool split_outputs = false;
	bool split_public = false;
	bool assume_encoding = false;
	bool assert_encoding = false;
	bool assume_def_inputs = false;
	bool required = false;
	bool formal = false;
	bool debug_asserts = false;
};

struct XpropWorker
{
	struct EncodedBit {
		SigBit is_0, is_1, is_x;
		bool driven;
	};

	struct EncodedSig {
		SigSpec is_0, is_1, is_x;
		Module *module;

		void invert() { std::swap(is_0, is_1); }
		void auto_0() { connect_0(module->Not(NEW_ID, module->Or(NEW_ID, is_1, is_x))); }
		void auto_1() { connect_1(module->Not(NEW_ID, module->Or(NEW_ID, is_0, is_x))); }
		void auto_x() { connect_x(module->Not(NEW_ID, module->Or(NEW_ID, is_0, is_1))); }

		void connect_0(SigSpec sig) { module->connect(is_0, sig); }
		void connect_1(SigSpec sig) { module->connect(is_1, sig); }
		void connect_x(SigSpec sig) { module->connect(is_x, sig); }

		void connect_1_under_x(SigSpec sig) { connect_1(module->And(NEW_ID, sig, module->Not(NEW_ID, is_x))); }
		void connect_0_under_x(SigSpec sig) { connect_0(module->And(NEW_ID, sig, module->Not(NEW_ID, is_x))); }

		void connect_x_under_0(SigSpec sig) { connect_x(module->And(NEW_ID, sig, module->Not(NEW_ID, is_0))); }

		void connect_as_bool() {
			int width = GetSize(is_0);
			if (width <= 1)
				return;
			module->connect(is_0.extract(1, width - 1), Const(State::S1, width - 1));
			module->connect(is_1.extract(1, width - 1), Const(State::S0, width - 1));
			module->connect(is_x.extract(1, width - 1), Const(State::S0, width - 1));
			is_0 = is_0[0];
			is_1 = is_1[0];
			is_x = is_x[0];
		}

		int size() const { return is_0.size(); }
	};

	Module *module;
	XpropOptions options;
	ModWalker modwalker;
	SigMap &sigmap;
	FfInitVals initvals;

	pool<SigBit> maybe_x_bits;
	dict<SigBit, EncodedBit> encoded_bits;

	pool<Cell *> pending_cells;
	std::deque<Cell *> pending_cell_queue;

	XpropWorker(Module *module, XpropOptions options) :
		module(module), options(options),
		modwalker(module->design), sigmap(modwalker.sigmap)
	{
		modwalker.setup(module);
		initvals.set(&modwalker.sigmap, module);

		maybe_x_bits.insert(State::Sx);

		for (auto cell : module->cells()) {
			pending_cells.insert(cell);
			pending_cell_queue.push_back(cell);
		}

		if (!options.assume_def_inputs) {
			for (auto port : module->ports) {
				auto wire = module->wire(port);
				if (wire->port_input)
					mark_maybe_x(SigSpec(wire));
			}
		}
	}

	bool maybe_x(SigBit bit)
	{
		return maybe_x_bits.count(sigmap(bit));
	}

	bool maybe_x(const SigSpec &sig)
	{
		for (auto bit : sig)
			if (maybe_x(bit)) return true;
		return false;
	}

	bool ports_maybe_x(Cell *cell)
	{
		for (auto &conn : cell->connections())
			if (maybe_x(conn.second))
				return true;
		return false;
	}

	bool inputs_maybe_x(Cell *cell)
	{
		for (auto &conn : cell->connections())
			if (cell->input(conn.first) && maybe_x(conn.second))
				return true;
		return false;
	}

	void mark_maybe_x(SigBit bit)
	{
		sigmap.apply(bit);
		if (!maybe_x_bits.insert(bit).second)
			return;
		auto it = modwalker.signal_consumers.find(bit);
		if (it == modwalker.signal_consumers.end())
			return;
		for (auto &consumer : it->second)
			if (pending_cells.insert(consumer.cell).second)
				pending_cell_queue.push_back(consumer.cell);
	}

	void mark_maybe_x(const SigSpec &sig)
	{
		for (auto bit : sig)
			mark_maybe_x(bit);
	}

	void mark_outputs_maybe_x(Cell *cell)
	{
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				mark_maybe_x(conn.second);
	}

	EncodedSig encoded(SigSpec sig, bool driving = false)
	{
		EncodedSig result;
		SigSpec invert;

		if (driving)
			result.module = module;

		int new_bits = 0;

		sigmap.apply(sig);

		for (auto bit : sig) {
			if (!bit.is_wire())
				continue;
			else if (!maybe_x(bit) && !driving)
				invert.append(bit);
			else if (!encoded_bits.count(bit)) {
				new_bits += 1;
				encoded_bits.emplace(bit, {
					State::Sm, State::Sm, State::Sm, false
				});
			}
		}

		if (!invert.empty() && !driving)
			invert = module->Not(NEW_ID, invert);

		EncodedSig new_sigs;
		if (new_bits > 0) {
			new_sigs.is_0 = module->addWire(NEW_ID, new_bits);
			new_sigs.is_1 = module->addWire(NEW_ID, new_bits);
			new_sigs.is_x = module->addWire(NEW_ID, new_bits);
		}

		int invert_pos = 0;
		int new_pos = 0;

		SigSpec driven_orig;
		EncodedSig driven_enc;
		SigSig driven_never_x;

		for (auto bit : sig)
		{
			if (!bit.is_wire()) {
				result.is_0.append(bit == State::S0 ? State::S1 : State::S0);
				result.is_1.append(bit == State::S1 ? State::S1 : State::S0);
				result.is_x.append(bit == State::Sx ? State::S1 : State::S0);
				continue;
			} else if (!maybe_x(bit) && !driving) {
				result.is_0.append(invert[invert_pos++]);
				result.is_1.append(bit);
				result.is_x.append(State::S0);
				continue;
			}
			auto &enc = encoded_bits.at(bit);
			if (enc.is_0 == State::Sm) {
				enc.is_0 = new_sigs.is_0[new_pos];
				enc.is_1 = new_sigs.is_1[new_pos];
				enc.is_x = new_sigs.is_x[new_pos];
				new_pos++;
			}
			if (driving) {
				log_assert(!enc.driven);
				enc.driven = true;
				if (maybe_x(bit)) {
					driven_orig.append(bit);
					driven_enc.is_0.append(enc.is_0);
					driven_enc.is_1.append(enc.is_1);
					driven_enc.is_x.append(enc.is_x);
				} else {
					driven_never_x.first.append(bit);
					driven_never_x.second.append(enc.is_1);
				}
			}
			result.is_0.append(enc.is_0);
			result.is_1.append(enc.is_1);
			result.is_x.append(enc.is_x);
		}

		if (!driven_orig.empty()) {
			auto decoder = module->addBwmux(NEW_ID, driven_enc.is_1, Const(State::Sx, GetSize(driven_orig)), driven_enc.is_x, driven_orig);
			decoder->set_bool_attribute(ID::xprop_decoder);
		}
		if (!driven_never_x.first.empty()) {
			module->connect(driven_never_x);
		}

		if (driving && (options.assert_encoding || options.assume_encoding)) {
			auto not_0 = module->Not(NEW_ID, result.is_0);
			auto not_1 = module->Not(NEW_ID, result.is_1);
			auto not_x = module->Not(NEW_ID, result.is_x);
			auto valid = module->ReduceAnd(NEW_ID, {
				module->Eq(NEW_ID, result.is_0, module->And(NEW_ID, not_1, not_x)),
				module->Eq(NEW_ID, result.is_1, module->And(NEW_ID, not_0, not_x)),
				module->Eq(NEW_ID, result.is_x, module->And(NEW_ID, not_0, not_1)),
			});
			if (options.assert_encoding)
				module->addAssert(NEW_ID_SUFFIX("xprop_enc"), valid, State::S1);
			else
				module->addAssume(NEW_ID_SUFFIX("xprop_enc"), valid, State::S1);
			if (options.debug_asserts) {
				auto bad_bits = module->Bweqx(NEW_ID, {result.is_0, result.is_1, result.is_x}, Const(State::Sx, GetSize(result) * 3));
				module->addAssert(NEW_ID_SUFFIX("xprop_debug"), module->LogicNot(NEW_ID, bad_bits), State::S1);
			}
		}

		return result;
	}

	void mark_all_maybe_x()
	{
		while (!pending_cell_queue.empty()) {
			Cell *cell = pending_cell_queue.front();
			pending_cell_queue.pop_front();
			pending_cells.erase(cell);

			mark_maybe_x(cell);
		}
	}

	void mark_maybe_x(Cell *cell) {
		if (cell->type.in(ID($bweqx), ID($eqx), ID($nex), ID($initstate), ID($assert), ID($assume), ID($cover), ID($anyseq), ID($anyconst)))
			return;

		if (cell->type.in(ID($pmux))) {
			mark_outputs_maybe_x(cell);
			return;
		}

		if (RTLIL::builtin_ff_cell_types().count(cell->type) || cell->type == ID($anyinit)) {
			FfData ff(&initvals, cell);

			if (cell->type != ID($anyinit))
				for (int i = 0; i < ff.width; i++)
					if (ff.val_init[i] == State::Sx)
						mark_maybe_x(ff.sig_q[i]);

			for (int i = 0; i < ff.width; i++)
				if (maybe_x(ff.sig_d[i]))
					mark_maybe_x(ff.sig_q[i]);

			if ((ff.has_clk || ff.has_gclk) && !ff.has_ce && !ff.has_aload && !ff.has_srst && !ff.has_arst && !ff.has_sr)
				return;
		}

		if (cell->type == ID($not)) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A); sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
			for (int i = 0; i < GetSize(sig_y); i++)
				if (maybe_x(sig_a[i]))
					mark_maybe_x(sig_y[i]);
			return;
		}

		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A); sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
			auto sig_b = cell->getPort(ID::B); sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			for (int i = 0; i < GetSize(sig_y); i++)
				if (maybe_x(sig_a[i]) || maybe_x(sig_b[i]))
					mark_maybe_x(sig_y[i]);
			return;
		}

		if (cell->type.in(ID($bwmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_s = cell->getPort(ID::S);
			for (int i = 0; i < GetSize(sig_y); i++)
				if (maybe_x(sig_a[i]) || maybe_x(sig_b[i]) || maybe_x(sig_s[i]))
					mark_maybe_x(sig_y[i]);
			return;
		}

		if (cell->type.in(ID($_MUX_), ID($mux), ID($bmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_s = cell->getPort(ID::S);
			if (maybe_x(sig_s)) {
				mark_maybe_x(sig_y);
				return;
			}
			for (int i = 0; i < GetSize(sig_y); i++) {
				if (maybe_x(sig_a[i])) {
					mark_maybe_x(sig_y[i]);
					continue;
				}
				for (int j = i; j < GetSize(sig_b); j += GetSize(sig_y)) {
					if (maybe_x(sig_b[j])) {
						mark_maybe_x(sig_y[i]);
						break;
					}
				}
			}
			return;
		}

		if (cell->type.in(ID($demux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_s = cell->getPort(ID::S);
			if (maybe_x(sig_s)) {
				mark_maybe_x(sig_y);
				return;
			}
			for (int i = 0; i < GetSize(sig_a); i++)
				if (maybe_x(sig_a[i]))
					for (int j = i; j < GetSize(sig_y); j += GetSize(sig_a))
						mark_maybe_x(sig_y[j]);
			return;
		}

		if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift))) {
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_y = cell->getPort(ID::Y);

			if (maybe_x(sig_b)) {
				mark_maybe_x(sig_y);
				return;
			}

			auto &sig_a = cell->getPort(ID::A);

			if (maybe_x(sig_a)) {
				// We could be more precise for shifts, but that's not required
				// for correctness, so let's keep it simple
				mark_maybe_x(sig_y);
				return;
			}
			return;
		}

		if (cell->type.in(ID($shiftx))) {
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_y = cell->getPort(ID::Y);

			if (cell->getParam(ID::B_SIGNED).as_bool() || GetSize(sig_b) >= 30) {
				mark_maybe_x(sig_y);
			} else {
				int max_shift = (1 << GetSize(sig_b)) - 1;

				auto &sig_a = cell->getPort(ID::A);

				for (int i = 0; i < GetSize(sig_y); i++)
					if (i + max_shift >= GetSize(sig_a))
						mark_maybe_x(sig_y[i]);
			}

			if (maybe_x(sig_b)) {
				mark_maybe_x(sig_y);
				return;
			}

			auto &sig_a = cell->getPort(ID::A);
			if (maybe_x(sig_a)) {
				// We could be more precise for shifts, but that's not required
				// for correctness, so let's keep it simple
				mark_maybe_x(sig_y);
				return;
			}
			return;
		}

		if (cell->type.in(ID($add), ID($sub), ID($mul), ID($neg))) {
			if (inputs_maybe_x(cell))
				mark_outputs_maybe_x(cell);
			return;
		}

		if (cell->type.in(ID($div), ID($mod), ID($divfloor), ID($modfloor))) {
			mark_outputs_maybe_x(cell);
			return;
		}

		if (cell->type.in(
			ID($le), ID($lt), ID($ge), ID($gt),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
			ID($reduce_bool), ID($logic_not), ID($logic_or), ID($logic_and),
			ID($eq), ID($ne),

			ID($_NOT_), ID($_AND_), ID($_NAND_), ID($_ANDNOT_), ID($_OR_), ID($_NOR_), ID($_ORNOT_), ID($_XOR_), ID($_XNOR_)
		)) {
			auto &sig_y = cell->getPort(ID::Y);
			if (inputs_maybe_x(cell))
				mark_maybe_x(sig_y[0]);
			return;
		}

		log_warning("Unhandled cell %s (%s) during maybe-x marking\n", log_id(cell), log_id(cell->type));
		mark_outputs_maybe_x(cell);
	}

	void process_cells()
	{
		for (auto cell : module->selected_cells())
			process_cell(cell);
	}

	void process_cell(Cell *cell)
	{
		if (!ports_maybe_x(cell)) {

			if (cell->type == ID($bweq)) {
				auto sig_y = cell->getPort(ID::Y);
				auto sig_a = cell->getPort(ID::A);
				auto sig_b = cell->getPort(ID::B);

				auto name = cell->name;
				module->remove(cell);
				module->addXnor(name, sig_a, sig_b, sig_y);
				return;
			}

			if (cell->type.in(ID($nex), ID($eqx))) {
				auto sig_y = cell->getPort(ID::Y);
				auto sig_a = cell->getPort(ID::A);
				auto sig_b = cell->getPort(ID::B);

				auto name = cell->name;
				auto type = cell->type;
				module->remove(cell);
				if (type == ID($eqx))
					module->addEq(name, sig_a, sig_b, sig_y);
				else
					module->addNe(name, sig_a, sig_b, sig_y);
				return;
			}

			return;
		}

		if (cell->type.in(ID($not), ID($_NOT_))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			if (cell->type == ID($not))
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());

			auto enc_a = encoded(sig_a);
			auto enc_y = encoded(sig_y, true);

			enc_y.connect_x(enc_a.is_x);
			enc_y.connect_0(enc_a.is_1);
			enc_y.connect_1(enc_a.is_0);

			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($and), ID($or), ID($_AND_), ID($_OR_), ID($_NAND_), ID($_NOR_), ID($_ANDNOT_), ID($_ORNOT_))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			if (cell->type.in(ID($and), ID($or))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			}

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_y = encoded(sig_y, true);

			if (cell->type.in(ID($or), ID($_OR_), ID($_NOR_), ID($_ORNOT_)))
				enc_a.invert(), enc_b.invert(), enc_y.invert();
			if (cell->type.in(ID($_NAND_), ID($_NOR_)))
				enc_y.invert();
			if (cell->type.in(ID($_ANDNOT_), ID($_ORNOT_)))
				enc_b.invert();

			enc_y.connect_0(module->Or(NEW_ID, enc_a.is_0, enc_b.is_0));
			enc_y.connect_1(module->And(NEW_ID, enc_a.is_1, enc_b.is_1));
			enc_y.auto_x();
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($logic_not))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);

			auto enc_a = encoded(sig_a);
			auto enc_y = encoded(sig_y, true);

			enc_y.connect_as_bool();

			if (cell->type.in(ID($reduce_or), ID($reduce_bool)))
				enc_a.invert(), enc_y.invert();
			if (cell->type == ID($logic_not))
				enc_a.invert();

			enc_y.connect_0(module->ReduceOr(NEW_ID, enc_a.is_0));
			enc_y.connect_1(module->ReduceAnd(NEW_ID, enc_a.is_1));
			enc_y.auto_x();
			module->remove(cell);

			return;
		}

		if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);

			auto enc_a = encoded(sig_a);
			auto enc_y = encoded(sig_y, true);

			enc_y.connect_as_bool();
			if (cell->type == ID($reduce_xnor))
				enc_y.invert();


			enc_y.connect_x(module->ReduceOr(NEW_ID, enc_a.is_x));
			enc_y.connect_1_under_x(module->ReduceXor(NEW_ID, enc_a.is_1));
			enc_y.auto_0();
			module->remove(cell);

			return;
		}

		if (cell->type.in(ID($logic_and), ID($logic_or))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_y = encoded(sig_y, true);

			enc_y.connect_as_bool();

			auto a_is_1 = module->ReduceOr(NEW_ID, enc_a.is_1);
			auto a_is_0 = module->ReduceAnd(NEW_ID, enc_a.is_0);
			auto b_is_1 = module->ReduceOr(NEW_ID, enc_b.is_1);
			auto b_is_0 = module->ReduceAnd(NEW_ID, enc_b.is_0);

			if (cell->type == ID($logic_or))
				 enc_y.invert(), std::swap(a_is_0, a_is_1), std::swap(b_is_0, b_is_1);

			enc_y.connect_0(module->Or(NEW_ID, a_is_0, b_is_0));
			enc_y.connect_1(module->And(NEW_ID, a_is_1, b_is_1));
			enc_y.auto_x();
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($xor), ID($xnor), ID($_XOR_), ID($_XNOR_))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			if (cell->type.in(ID($xor), ID($xnor))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			}

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_y = encoded(sig_y, true);

			if (cell->type.in(ID($xnor), ID($_XNOR_)))
				enc_y.invert();

			enc_y.connect_x(module->Or(NEW_ID, enc_a.is_x, enc_b.is_x));
			enc_y.connect_1_under_x(module->Xor(NEW_ID, enc_a.is_1, enc_b.is_1));
			enc_y.auto_0();
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($eq), ID($ne))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			int width = std::max(GetSize(sig_a), GetSize(sig_b));
			sig_a.extend_u0(width, cell->getParam(ID::A_SIGNED).as_bool());
			sig_b.extend_u0(width, cell->getParam(ID::B_SIGNED).as_bool());

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_y = encoded(sig_y, true);
			enc_y.connect_as_bool();

			if (cell->type == ID($ne))
				enc_y.invert();

			auto delta = module->Xor(NEW_ID, enc_a.is_1, enc_b.is_1);
			auto xpos = module->Or(NEW_ID, enc_a.is_x, enc_b.is_x);

			enc_y.connect_0(module->ReduceOr(NEW_ID, module->And(NEW_ID, delta, module->Not(NEW_ID, xpos))));
			enc_y.connect_x_under_0(module->ReduceOr(NEW_ID, xpos));
			enc_y.auto_1();
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($eqx), ID($nex))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			int width = std::max(GetSize(sig_a), GetSize(sig_b));
			sig_a.extend_u0(width, cell->getParam(ID::A_SIGNED).as_bool());
			sig_b.extend_u0(width, cell->getParam(ID::B_SIGNED).as_bool());

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);

			auto delta_0 = module->Xnor(NEW_ID, enc_a.is_0, enc_b.is_0);
			auto delta_1 = module->Xnor(NEW_ID, enc_a.is_1, enc_b.is_1);

			auto eq = module->ReduceAnd(NEW_ID, {delta_0, delta_1});

			auto res = cell->type == ID($nex) ? module->Not(NEW_ID, eq) : eq;

			module->connect(sig_y[0], res);
			if (GetSize(sig_y) > 1)
				module->connect(sig_y.extract(1, GetSize(sig_y) - 1), Const(State::S0, GetSize(sig_y) - 1));
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($bweqx))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);

			auto delta_0 = module->Xnor(NEW_ID, enc_a.is_0, enc_b.is_0);
			auto delta_1 = module->Xnor(NEW_ID, enc_a.is_1, enc_b.is_1);
			module->addAnd(NEW_ID, delta_0, delta_1, sig_y);
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($_MUX_), ID($mux), ID($bwmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto sig_s = cell->getPort(ID::S);

			if (cell->type == ID($mux))
				sig_s = SigSpec(sig_s[0], GetSize(sig_y));

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_s = encoded(sig_s);
			auto enc_y = encoded(sig_y, true);

			enc_y.connect_1(module->And(NEW_ID,
					module->Or(NEW_ID, enc_a.is_1, enc_s.is_1),
					module->Or(NEW_ID, enc_b.is_1, enc_s.is_0)));
			enc_y.connect_0(module->And(NEW_ID,
					module->Or(NEW_ID, enc_a.is_0, enc_s.is_1),
					module->Or(NEW_ID, enc_b.is_0, enc_s.is_0)));
			enc_y.auto_x();
			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($pmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_s = cell->getPort(ID::S);

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_s = encoded(sig_s);
			auto enc_y = encoded(sig_y, true);

			int width = GetSize(enc_y);

			auto all_x = module->ReduceOr(NEW_ID, {
				enc_s.is_x,
				module->And(NEW_ID, enc_s.is_1, module->Sub(NEW_ID, enc_s.is_1, Const(1, width)))
			});

			auto selected = enc_a;

			for (int i = 0; i < GetSize(enc_s); i++) {
				auto sel_bit = enc_s.is_1[i];
				selected.is_0 = module->Mux(NEW_ID, selected.is_0, enc_b.is_0.extract(i * width, width), sel_bit);
				selected.is_1 = module->Mux(NEW_ID, selected.is_1, enc_b.is_1.extract(i * width, width), sel_bit);
				selected.is_x = module->Mux(NEW_ID, selected.is_x, enc_b.is_x.extract(i * width, width), sel_bit);
			}

			enc_y.connect_0(module->Mux(NEW_ID, selected.is_0, Const(State::S0, width), all_x));
			enc_y.connect_1(module->Mux(NEW_ID, selected.is_1, Const(State::S0, width), all_x));
			enc_y.connect_x(module->Mux(NEW_ID, selected.is_x, Const(State::S1, width), all_x));

			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);

			auto enc_a = encoded(sig_a);
			auto enc_b = encoded(sig_b);
			auto enc_y = encoded(sig_y, true);

			auto all_x = module->ReduceOr(NEW_ID, enc_b.is_x)[0];
			auto not_all_x = module->Not(NEW_ID, all_x)[0];

			SigSpec y_not_0 = module->addWire(NEW_ID, GetSize(sig_y));
			SigSpec y_1 = module->addWire(NEW_ID, GetSize(sig_y));
			SigSpec y_x = module->addWire(NEW_ID, GetSize(sig_y));

			auto encoded_type = cell->type == ID($shiftx) ? ID($shift) : cell->type;

			if (cell->type == ID($shiftx)) {
				std::swap(enc_a.is_0, enc_a.is_x);
			}

			auto shift_0 = module->addCell(NEW_ID, encoded_type);
			shift_0->parameters = cell->parameters;
			shift_0->setPort(ID::A, module->Not(NEW_ID, enc_a.is_0));
			shift_0->setPort(ID::B, enc_b.is_1);
			shift_0->setPort(ID::Y, y_not_0);

			auto shift_1 = module->addCell(NEW_ID, encoded_type);
			shift_1->parameters = cell->parameters;
			shift_1->setPort(ID::A, enc_a.is_1);
			shift_1->setPort(ID::B, enc_b.is_1);
			shift_1->setPort(ID::Y, y_1);

			auto shift_x = module->addCell(NEW_ID, encoded_type);
			shift_x->parameters = cell->parameters;
			shift_x->setPort(ID::A, enc_a.is_x);
			shift_x->setPort(ID::B, enc_b.is_1);
			shift_x->setPort(ID::Y, y_x);

			SigSpec y_0 = module->Not(NEW_ID, y_not_0);

			if (cell->type == ID($shiftx))
				std::swap(y_0, y_x);

			enc_y.connect_0(module->And(NEW_ID, y_0, SigSpec(not_all_x, GetSize(sig_y))));
			enc_y.connect_1(module->And(NEW_ID, y_1, SigSpec(not_all_x, GetSize(sig_y))));
			enc_y.connect_x(module->Or(NEW_ID, y_x, SigSpec(all_x, GetSize(sig_y))));

			module->remove(cell);
			return;
		}

		if (cell->type.in(ID($ff))) {
			auto &sig_d = cell->getPort(ID::D);
			auto &sig_q = cell->getPort(ID::Q);

			auto init_q = initvals(sig_q);
			auto init_q_is_1 = init_q;
			auto init_q_is_x = init_q;

			for (auto &bit : init_q_is_1.bits())
				bit = bit == State::S1 ? State::S1 : State::S0;
			for (auto &bit : init_q_is_x.bits())
				bit = bit == State::Sx ? State::S1 : State::S0;

			initvals.remove_init(sig_q);

			auto enc_d = encoded(sig_d);
			auto enc_q = encoded(sig_q, true);

			auto data_q = module->addWire(NEW_ID, GetSize(sig_q));

			module->addFf(NEW_ID, enc_d.is_1, data_q);
			module->addFf(NEW_ID, enc_d.is_x, enc_q.is_x);

			initvals.set_init(data_q, init_q_is_1);
			initvals.set_init(enc_q.is_x, init_q_is_x);

			enc_q.connect_1_under_x(data_q);
			enc_q.auto_0();

			module->remove(cell);
			return;
		}

		if (RTLIL::builtin_ff_cell_types().count(cell->type) || cell->type == ID($anyinit)) {
			FfData ff(&initvals, cell);

			if ((ff.has_clk || ff.has_gclk) && !ff.has_ce && !ff.has_aload && !ff.has_srst && !ff.has_arst && !ff.has_sr) {
				if (ff.has_clk && maybe_x(ff.sig_clk)) {
					log_warning("Only non-x CLK inputs are currently supported for %s (%s)\n", log_id(cell), log_id(cell->type));
				} else {
					auto init_q = ff.val_init;
					auto init_q_is_1 = init_q;
					auto init_q_is_x = init_q;

					if (ff.is_anyinit) {
						for (auto &bit : init_q_is_1.bits())
							bit = State::Sx;
						for (auto &bit : init_q_is_x.bits())
							bit = State::S0;
					} else {
						for (auto &bit : init_q_is_1.bits())
							bit = bit == State::S1 ? State::S1 : State::S0;
						for (auto &bit : init_q_is_x.bits())
							bit = bit == State::Sx ? State::S1 : State::S0;
					}

					ff.remove();

					auto enc_d = encoded(ff.sig_d);
					auto enc_q = encoded(ff.sig_q, true);

					auto data_q = module->addWire(NEW_ID, GetSize(ff.sig_q));

					ff.sig_d = enc_d.is_1;
					ff.sig_q = data_q;
					ff.val_init = init_q_is_1;
					ff.emit();

					ff.name = NEW_ID;
					ff.cell = nullptr;
					ff.sig_d = enc_d.is_x;
					ff.sig_q = enc_q.is_x;
					ff.is_anyinit = false;
					ff.val_init = init_q_is_x;
					ff.emit();


					enc_q.connect_1_under_x(data_q);
					enc_q.auto_0();

					return;
				}
			} else {
				log_warning("Unhandled FF-cell %s (%s), consider running clk2fflogic, async2sync and/or dffunmap\n", log_id(cell), log_id(cell->type));
			}
		}

		// Celltypes where any input x bit makes the whole output x
		if (cell->type.in(
			ID($neg),
			ID($le), ID($lt), ID($ge), ID($gt),
			ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor)
		)) {

			SigSpec inbits_x;
			for (auto &conn : cell->connections()) {
				if (cell->input(conn.first)) {
					auto enc_port = encoded(conn.second);
					inbits_x.append(enc_port.is_x);
					cell->setPort(conn.first, enc_port.is_1);
				}
			}

			if (cell->type.in(ID($div), ID($mod), ID($divfloor), ID($modfloor))) {
				auto sig_b = cell->getPort(ID::B);
				auto invalid = module->LogicNot(NEW_ID, sig_b);
				inbits_x.append(invalid);
				sig_b[0] = module->Or(NEW_ID, sig_b[0], invalid);
				cell->setPort(ID::B, sig_b);
			}

			SigBit outbits_x = (GetSize(inbits_x) == 1 ? inbits_x : module->ReduceOr(NEW_ID, inbits_x));

			bool bool_out = cell->type.in(ID($le), ID($lt), ID($ge), ID($gt));

			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					auto enc_port = encoded(conn.second, true);
					if (bool_out)
						enc_port.connect_as_bool();

					SigSpec new_output = module->addWire(NEW_ID, GetSize(conn.second));

					enc_port.connect_1_under_x(bool_out ? new_output.extract(0) : new_output);
					enc_port.connect_x(SigSpec(outbits_x, GetSize(enc_port)));
					enc_port.auto_0();

					cell->setPort(conn.first, new_output);
				}
			}

			return;
		}

		if (cell->type == ID($bmux)) // TODO might want to support bmux natively anyway
			log("Running 'bmuxmap' preserves x-propagation and can be run before 'xprop'.\n");
		if (cell->type == ID($demux)) // TODO might want to support demux natively anyway
			log("Running 'demuxmap' preserves x-propagation and can be run before 'xprop'.\n");

		if (options.required)
			log_error("Unhandled cell %s (%s)\n", log_id(cell), log_id(cell->type));
		else
			log_warning("Unhandled cell %s (%s)\n", log_id(cell), log_id(cell->type));
	}

	void split_ports()
	{
		if (!options.split_inputs && !options.split_outputs)
			return;

		int port_id = 1;

		for (auto port : module->ports) {
			auto wire = module->wire(port);
			if (module->design->selected(module, wire)) {
				if (wire->port_input == wire->port_output) {
					log_warning("Port %s not an input or an output port which is not supported by xprop\n", log_id(wire));
				} else if ((options.split_inputs && !options.assume_def_inputs && wire->port_input) || (options.split_outputs && wire->port_output)) {
					auto port_d = module->uniquify(stringf("%s_d", port.c_str()));
					auto port_x = module->uniquify(stringf("%s_x", port.c_str()));

					auto wire_d = module->addWire(port_d, GetSize(wire));
					auto wire_x = module->addWire(port_x, GetSize(wire));

					wire_d->port_input = wire->port_input;
					wire_d->port_output = wire->port_output;
					wire_d->port_id = port_id++;

					wire_x->port_input = wire->port_input;
					wire_x->port_output = wire->port_output;
					wire_x->port_id = port_id++;

					if (wire->port_output) {
						auto enc = encoded(wire);
						module->connect(wire_d, enc.is_1);
						module->connect(wire_x, enc.is_x);

						if (options.split_public) {
							// Need to hide the original wire so split_public doesn't try to split it again
							module->rename(wire, NEW_ID_SUFFIX(wire->name.c_str()));
						}
					} else {
						auto enc = encoded(wire, true);

						enc.connect_x(wire_x);
						enc.connect_1_under_x(wire_d);
						enc.auto_0();
					}

					wire->port_input = wire->port_output = false;
					wire->port_id = 0;

					continue;
				}
			}
			wire->port_id = port_id++;
		}

		module->fixup_ports();
	}

	void split_public()
	{
		if (!options.split_public)
			return;

		for (auto wire : module->selected_wires()) {
			if (wire->port_input || wire->port_output || !wire->name.isPublic())
				continue;
			int index_d = 0;
			int index_x = 0;
			auto name_d = module->uniquify(stringf("%s_d", wire->name.c_str()), index_d);
			auto name_x = module->uniquify(stringf("%s_x", wire->name.c_str()), index_x);

			auto hdlname = wire->get_hdlname_attribute();

			auto wire_d = module->addWire(name_d, GetSize(wire));
			auto wire_x = module->addWire(name_x, GetSize(wire));

			if (!hdlname.empty()) {
				auto hdlname_d = hdlname;
				auto hdlname_x = hdlname;
				hdlname_d.back() += index_d ? stringf("_d_%d", index_d) : "_d";
				hdlname_x.back() += index_x ? stringf("_x_%d", index_x) : "_x";
				wire_d->set_hdlname_attribute(hdlname_d);
				wire_x->set_hdlname_attribute(hdlname_x);
			}

			auto enc = encoded(wire);
			module->connect(wire_d, enc.is_1);
			module->connect(wire_x, enc.is_x);

			module->rename(wire, NEW_ID_SUFFIX(wire->name.c_str()));
		}
	}

	void encode_remaining()
	{
		pool<Wire *> enc_undriven_wires;

		for (auto &enc_bit : encoded_bits) {
			if (!enc_bit.second.driven) {
				log_assert(enc_bit.first.is_wire());
				enc_undriven_wires.insert(enc_bit.first.wire);
			}
		}

		if (options.formal && !enc_undriven_wires.empty()) {
			for (auto &bit : enc_undriven_wires)
				log_warning("Found encoded wire %s having a non-encoded driver\n", log_signal(bit));

			log_error("Found encoded wires having a non-encoded driver, not allowed in -formal mode\n");
		}


		for (auto wire : enc_undriven_wires) {
			SigSpec sig(sigmap(wire));

			SigSpec orig;
			EncodedSig enc;

			for (auto bit : sig) {
				auto it = encoded_bits.find(bit);
				if (it == encoded_bits.end() || it->second.driven)
					continue;
				orig.append(bit);
				enc.is_0.append(it->second.is_0);
				enc.is_1.append(it->second.is_1);
				enc.is_x.append(it->second.is_x);
				it->second.driven = true;
			}

			module->addBweqx(NEW_ID, orig, Const(State::S0, GetSize(orig)), enc.is_0);
			module->addBweqx(NEW_ID, orig, Const(State::S1, GetSize(orig)), enc.is_1);
			module->addBweqx(NEW_ID, orig, Const(State::Sx, GetSize(orig)), enc.is_x);
		}
	}
};

struct XpropPass : public Pass {
	XpropPass() : Pass("xprop", "formal x propagation") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xprop [options] [selection]\n");
		log("\n");
		log("This pass transforms the circuit into an equivalent circuit that explicitly\n");
		log("encodes the propagation of x values using purely 2-valued logic. On the\n");
		log("interface between xprop-transformed and non-transformed parts of the design,\n");
		log("appropriate conversions are inserted automatically.\n");
		log("\n");
		log("    -split-inputs\n");
		log("    -split-outputs\n");
		log("    -split-ports\n");
		log("        Replace each input/output/port with two new ports, one carrying the\n");
		log("        defined values (named <portname>_d) and one carrying the mask of which\n");
		log("        bits are x (named <portname>_x). When a bit in the <portname>_x is set\n");
		log("        the corresponding bit in <portname>_d is ignored for inputs and\n");
		log("        guaranteed to be 0 for outputs.\n");
		log("\n");
		log("    -split-public\n");
		log("        Replace each public non-port wire with two new wires, one carrying the\n");
		log("        defined values (named <wirename>_d) and one carrying the mask of which\n");
		log("        bits are x (named <wirename>_x). When a bit in the <portname>_x is set\n");
		log("        the corresponding bit in <wirename>_d is guaranteed to be 0 for\n");
		log("        outputs.\n");
		log("\n");
		log("    -assume-encoding\n");
		log("        Add encoding invariants as assumptions. This can speed up formal\n");
		log("        verification tasks.\n");
		log("\n");
		log("    -assert-encoding\n");
		log("        Add encoding invariants as assertions. Used for testing the xprop\n");
		log("        pass itself.\n");
		log("\n");
		log("    -assume-def-inputs\n");
		log("        Assume all inputs are fully defined. This adds corresponding\n");
		log("        assumptions to the design and uses these assumptions to optimize the\n");
		log("        xprop encoding.\n");
		log("\n");
		log("    -required\n");
		log("        Produce a runtime error if any encountered cell could not be encoded.\n");
		log("\n");
		log("    -formal\n");
		log("        Produce a runtime error if any encoded cell uses a signal that is\n");
		log("		 neither known to be non-x nor driven by another encoded cell.\n");
		log("\n");
		log("    -debug-asserts\n");
		log("        Add assertions checking that the encoding used by this pass never\n");
		log("        produces x values within the encoded signals.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		XpropOptions options;

		log_header(design, "Executing XPROP pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-split-ports") {
				options.split_inputs = true;
				options.split_outputs = true;
				continue;
			}
			if (args[argidx] == "-split-inputs") {
				options.split_inputs = true;
				continue;
			}
			if (args[argidx] == "-split-outputs") {
				options.split_outputs = true;
				continue;
			}
			if (args[argidx] == "-split-public") {
				options.split_public = true;
				continue;
			}
			if (args[argidx] == "-assume-encoding") {
				options.assume_encoding = true;
				continue;
			}
			if (args[argidx] == "-assert-encoding") {
				options.assert_encoding = true;
				continue;
			}
			if (args[argidx] == "-assume-def-inputs") {
				options.assume_def_inputs = true;
				continue;
			}
			if (args[argidx] == "-required") {
				options.required = true; // TODO check more
				continue;
			}
			if (args[argidx] == "-formal") {
				options.formal = true;
				options.required = true;
				continue;
			}
			if (args[argidx] == "-debug-asserts") { // TODO documented
				options.debug_asserts = true;
				options.assert_encoding = true;
				continue;
			}
			break;
		}

		if (options.assert_encoding && options.assume_encoding)
			log_cmd_error("The options -assert-encoding and -assume-encoding are exclusive.\n");

		extra_args(args, argidx, design);

		log_push();
		Pass::call(design, "bmuxmap");
		Pass::call(design, "demuxmap");
		log_pop();

		for (auto module : design->selected_modules()) {
			if (options.assume_def_inputs) {
				for (auto port : module->ports) {
					auto wire = module->wire(port);
					if (!module->design->selected(module, wire))
						continue;

					if (wire->port_input) {
						module->addAssume(NEW_ID, module->Not(NEW_ID, module->ReduceOr(NEW_ID, module->Bweqx(NEW_ID, wire, Const(State::Sx, GetSize(wire))))), State::S1);
					}
				}
			}

			XpropWorker worker(module, options);
			log_debug("Marking all x-bits.\n");
			worker.mark_all_maybe_x();
			log_debug("Repalcing cells.\n");
			worker.process_cells();
			log_debug("Splitting ports.\n");
			worker.split_ports();
			log_debug("Splitting public signals.\n");
			worker.split_public();
			log_debug("Encode remaining signals.\n");
			worker.encode_remaining();

		}
	}
} XpropPass;

PRIVATE_NAMESPACE_END
