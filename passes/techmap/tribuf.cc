/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TribufConfig {
	bool merge_mode;
	bool logic_mode;
	bool formal_mode;

	TribufConfig() {
		merge_mode = false;
		logic_mode = false;
		formal_mode = false;
	}
};

struct TribufWorker {
	Module *module;
	SigMap sigmap;
	const TribufConfig &config;

	TribufWorker(Module *module, const TribufConfig &config) : module(module), sigmap(module), config(config)
	{
	}

	void mux_to_tribufs(Cell *cell, dict<SigSpec, vector<Cell*>> &tribuf_cells)
	{
		bool is_fine = cell->type == ID($_MUX_);
		SigSpec sig_a = cell->getPort(ID::A);
		SigSpec sig_b = cell->getPort(ID::B);
		SigSpec sig_s = cell->getPort(ID::S);
		SigSpec sig_y = cell->getPort(ID::Y);
		std::string src = cell->get_src_attribute();

		// Slice the tribuf based on the z-ness of A and B
		SigSpec mux_a, mux_b, mux_y, s_a, s_y, ns_a, ns_y, off_y;
		for (int i = 0; i < GetSize(sig_y); i++) {
			bool z_a = sig_a[i] == State::Sz;
			bool z_b = sig_b[i] == State::Sz;
			if (z_a && z_b) {
				// y = s ? 'z : 'z -> y = $tribuf(A='x, EN='0)
				off_y.append(sig_y[i]);
			} else if (z_a) {
				// y = s ? b : 'z -> y = $tribuf(A=b, EN=s)
				s_a.append(sig_b[i]);
				s_y.append(sig_y[i]);
			} else if (z_b) {
				// y = s ? 'z : a -> y = $tribuf(A=a, EN=~s)
				ns_a.append(sig_a[i]);
				ns_y.append(sig_y[i]);
			} else {
				// No change
				mux_a.append(sig_a[i]);
				mux_b.append(sig_b[i]);
				mux_y.append(sig_y[i]);
			}
		}

		vector<std::tuple<SigSpec, SigSpec, SigSpec>> drivers;
		if (!s_y.empty())
			drivers.emplace_back(s_a, sig_s, s_y);
		if (!ns_y.empty())
			drivers.emplace_back(ns_a, is_fine ? SigSpec(module->NotGate(NEW_ID, sig_s, src)) : module->Not(NEW_ID, sig_s, false, src), ns_y);
		if (!off_y.empty())
			drivers.emplace_back(SigSpec(State::Sx, GetSize(off_y)), State::S0, off_y);

		if (!mux_y.empty()) {
			cell->setPort(ID::A, mux_a);
			cell->setPort(ID::B, mux_b);
			cell->setPort(ID::Y, mux_y);
			cell->setParam(ID::WIDTH, GetSize(mux_y));
		}

		for (int i = 0; i < GetSize(drivers); i++) {
			auto &[a, en, y] = drivers[i];
			Cell *tribuf;
			if (i == 0 && mux_y.empty()) {
				tribuf = cell;
				tribuf->unsetPort(ID::B);
				tribuf->unsetPort(ID::S);
				tribuf->type = is_fine ? ID($_TBUF_) : ID($tribuf);
				tribuf->setPort(ID::A, a);
				tribuf->setPort(is_fine ? ID::E : ID::EN, en);
				tribuf->setPort(ID::Y, y);
				if (!is_fine)
					tribuf->setParam(ID::WIDTH, GetSize(y));
			} else {
				tribuf = module->addTribuf(NEW_ID, a, en, y);
				tribuf->attributes = cell->attributes;
			}
			tribuf_cells[sigmap(y)].push_back(tribuf);
		}

		module->design->scratchpad_set_bool("tribuf.added_something", true);
	}

	void run()
	{
		dict<SigSpec, vector<Cell*>> tribuf_cells;
		pool<SigBit> output_bits;

		if (config.logic_mode || config.formal_mode)
			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						output_bits.insert(bit);

		for (auto cell : module->selected_cells())
		{
			if (cell->type == ID($tribuf))
				tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type == ID($_TBUF_))
				tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type.in(ID($mux), ID($_MUX_)) && (cell->getPort(ID::A).has_const(State::Sz) || cell->getPort(ID::B).has_const(State::Sz)))
				mux_to_tribufs(cell, tribuf_cells);
		}

		if (config.merge_mode || config.logic_mode || config.formal_mode)
		{
			for (auto &it : tribuf_cells)
			{
				bool no_tribuf = false;

				if (config.logic_mode && !config.formal_mode) {
					no_tribuf = true;
					for (auto bit : it.first)
						if (output_bits.count(bit))
							no_tribuf = false;
				}

				if (config.formal_mode)
					no_tribuf = true;

				if (GetSize(it.second) <= 1 && !no_tribuf)
					continue;

				if (config.formal_mode && GetSize(it.second) >= 2) {
					for (auto cell : it.second) {
						SigSpec others_s;

						for (auto other_cell : it.second) {
							if (other_cell == cell)
								continue;
							else if (other_cell->type == ID($tribuf))
								others_s.append(other_cell->getPort(ID::EN));
							else
								others_s.append(other_cell->getPort(ID::E));
						}

						auto cell_s = cell->type == ID($tribuf) ? cell->getPort(ID::EN) : cell->getPort(ID::E);

						auto other_s = module->ReduceOr(NEW_ID, others_s);

						auto conflict = module->And(NEW_ID, cell_s, other_s);

						std::string name = stringf("$tribuf_conflict$%s", cell);
						auto assert_cell = module->addAssert(name, module->Not(NEW_ID, conflict), SigSpec(true));

						assert_cell->set_src_attribute(cell->get_src_attribute());
						assert_cell->set_bool_attribute(ID::keep);

						module->design->scratchpad_set_bool("tribuf.added_something", true);
					}
				}

				SigSpec pmux_b, pmux_s;
				for (auto cell : it.second) {
					if (cell->type == ID($tribuf))
						pmux_s.append(cell->getPort(ID::EN));
					else
						pmux_s.append(cell->getPort(ID::E));
					pmux_b.append(cell->getPort(ID::A));
					module->remove(cell);
				}

				SigSpec muxout = GetSize(pmux_s) > 1 ? module->Pmux(NEW_ID, SigSpec(State::Sx, GetSize(it.first)), pmux_b, pmux_s) : pmux_b;

				if (no_tribuf)
					module->connect(it.first, muxout);
				else {
					module->addTribuf(NEW_ID, muxout, module->ReduceOr(NEW_ID, pmux_s), it.first);
					module->design->scratchpad_set_bool("tribuf.added_something", true);
				}
			}
		}
	}
};

struct TribufPass : public Pass {
	TribufPass() : Pass("tribuf", "infer tri-state buffers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    tribuf [options] [selection]\n");
		log("\n");
		log("This pass transforms $mux cells with 'z' inputs to tristate buffers.\n");
		log("\n");
		log("    -merge\n");
		log("        merge multiple tri-state buffers driving the same net\n");
		log("        into a single buffer.\n");
		log("\n");
		log("    -logic\n");
		log("        convert tri-state buffers that do not drive output ports\n");
		log("        to non-tristate logic. this option implies -merge.\n");
		log("\n");
		log("    -formal\n");
		log("        convert all tri-state buffers to non-tristate logic and\n");
		log("        add a formal assertion that no two buffers are driving the\n");
		log("        same net simultaneously. this option implies -merge.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		TribufConfig config;

		log_header(design, "Executing TRIBUF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-merge") {
				config.merge_mode = true;
				continue;
			}
			if (args[argidx] == "-logic") {
				config.logic_mode = true;
				continue;
			}
			if (args[argidx] == "-formal") {
				config.formal_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			TribufWorker worker(module, config);
			worker.run();
		}
	}
} TribufPass;

PRIVATE_NAMESPACE_END
