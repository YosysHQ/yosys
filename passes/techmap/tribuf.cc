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

	static bool is_all_z(SigSpec sig)
	{
		for (auto bit : sig)
			if (bit != State::Sz)
				return false;
		return true;
	}

	static IdString tribuf_en_id(Cell *cell)
	{
		return cell->type == ID($tribuf) ? ID::EN : ID::E;
	}

	static SigSpec tribuf_en(Cell *cell)
	{
		return cell->getPort(tribuf_en_id(cell));
	}

	Cell *inner_tribuf(SigSpec sig, dict<SigBit, Cell*> &tribuf_driver, dict<SigBit, int> &fanout)
	{
		Cell *c = nullptr;
		for (auto bit : sigmap(sig)) {
			auto it = tribuf_driver.find(bit);
			if (it == tribuf_driver.end() || fanout[bit] != 1)
				return nullptr;
			if (c && c != it->second)
				return nullptr;
			c = it->second;
		}
		if (c && sigmap(c->getPort(ID::Y)) == sigmap(sig))
			return c;
		return nullptr;
	}

	// Fold tri-state that is hidden behind an ordinary $mux (or behind the data input of another tribuf)
	// into a single tribuf, so nested z like cond ? val : (en ? z : x) is not lost before iopadmap can see it
	bool fold_tristate()
	{
		dict<SigBit, Cell*> tribuf_driver;
		dict<SigBit, int> fanout;

		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections())
				if (!cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						fanout[bit]++;
			if (cell->type.in(ID($tribuf), ID($_TBUF_)))
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					tribuf_driver[bit] = cell;
		}
		// Ports keep their nets alive, so never fold them away
		for (auto wire : module->wires())
			if (wire->port_id)
				for (auto bit : sigmap(wire))
					fanout[bit]++;

		struct MuxJob { Cell *mux, *ta, *tb; };
		struct TriJob { Cell *outer, *inner; };
		std::vector<MuxJob> mux_jobs;
		std::vector<TriJob> tri_jobs;

		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID($mux), ID($_MUX_))) {
				Cell *ta = inner_tribuf(cell->getPort(ID::A), tribuf_driver, fanout);
				Cell *tb = inner_tribuf(cell->getPort(ID::B), tribuf_driver, fanout);
				if (ta || tb)
					mux_jobs.push_back({cell, ta, tb});
			} else if (cell->type.in(ID($tribuf), ID($_TBUF_))) {
				Cell *inner = inner_tribuf(cell->getPort(ID::A), tribuf_driver, fanout);
				if (inner)
					tri_jobs.push_back({cell, inner});
			}
		}

		for (auto &job : mux_jobs) {
			SigSpec s = job.mux->getPort(ID::S);
			SigSpec en_a  = job.ta ? tribuf_en(job.ta) : SigSpec(State::S1);
			SigSpec en_b  = job.tb ? tribuf_en(job.tb) : SigSpec(State::S1);
			SigSpec val_a = job.ta ? job.ta->getPort(ID::A) : job.mux->getPort(ID::A);
			SigSpec val_b = job.tb ? job.tb->getPort(ID::A) : job.mux->getPort(ID::B);
			SigSpec en  = module->Mux(NEW_ID, en_a, en_b, s);
			SigSpec val = module->Mux(NEW_ID, val_a, val_b, s);

			SigSpec y = job.mux->getPort(ID::Y);
			if (job.ta) module->remove(job.ta);
			if (job.tb) module->remove(job.tb);
			module->remove(job.mux);
			module->addTribuf(NEW_ID, val, en, y);
			module->design->scratchpad_set_bool("tribuf.added_something", true);
		}

		// A tribuf whose data is another tribuf drives its value only while both are enabled
		pool<Cell*> folded_inner;
		for (auto &job : mux_jobs) {
			if (job.ta) folded_inner.insert(job.ta);
			if (job.tb) folded_inner.insert(job.tb);
		}

		for (auto &job : tri_jobs)
			folded_inner.insert(job.inner);

		bool tri_changed = false;
		for (auto &job : tri_jobs) {
			if (folded_inner.count(job.outer))
				continue;
			SigSpec en = module->And(NEW_ID, tribuf_en(job.outer), tribuf_en(job.inner));
			job.outer->setPort(ID::A, job.inner->getPort(ID::A));
			job.outer->setPort(tribuf_en_id(job.outer), en);
			module->remove(job.inner);
			module->design->scratchpad_set_bool("tribuf.added_something", true);
			tri_changed = true;
		}

		return !mux_jobs.empty() || tri_changed;
	}

	void run()
	{
		pool<SigBit> output_bits;

		if (config.logic_mode || config.formal_mode)
			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						output_bits.insert(bit);

		for (auto cell : module->selected_cells())
		{
			if (!cell->type.in(ID($mux), ID($_MUX_)))
				continue;

			IdString en_port = cell->type == ID($mux) ? ID::EN : ID::E;
			IdString tri_type = cell->type == ID($mux) ? ID($tribuf) : ID($_TBUF_);

			if (is_all_z(cell->getPort(ID::A)) && is_all_z(cell->getPort(ID::B))) {
				module->remove(cell);
				continue;
			}

			if (is_all_z(cell->getPort(ID::A))) {
				cell->setPort(ID::A, cell->getPort(ID::B));
				cell->setPort(en_port, cell->getPort(ID::S));
				cell->unsetPort(ID::B);
				cell->unsetPort(ID::S);
				cell->type = tri_type;
				module->design->scratchpad_set_bool("tribuf.added_something", true);
				continue;
			}

			if (is_all_z(cell->getPort(ID::B))) {
				cell->setPort(en_port, module->Not(NEW_ID, cell->getPort(ID::S)));
				cell->unsetPort(ID::B);
				cell->unsetPort(ID::S);
				cell->type = tri_type;
				module->design->scratchpad_set_bool("tribuf.added_something", true);
				continue;
			}
		}

		while (fold_tristate()) {}

		dict<SigSpec, vector<Cell*>> tribuf_cells;
		for (auto cell : module->selected_cells())
			if (cell->type.in(ID($tribuf), ID($_TBUF_)))
				tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

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
							others_s.append(tribuf_en(other_cell));
						}

						auto cell_s = tribuf_en(cell);

						auto other_s = module->ReduceOr(NEW_ID, others_s);

						auto conflict = module->And(NEW_ID, cell_s, other_s);

						std::string name = stringf("$tribuf_conflict$%s", cell->name.unescape());
						auto assert_cell = module->addAssert(name, module->Not(NEW_ID, conflict), SigSpec(true));

						assert_cell->set_src_attribute(cell->get_src_attribute());
						assert_cell->set_bool_attribute(ID::keep);

						module->design->scratchpad_set_bool("tribuf.added_something", true);
					}
				}

				SigSpec pmux_b, pmux_s;
				for (auto cell : it.second) {
					pmux_s.append(tribuf_en(cell));
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
