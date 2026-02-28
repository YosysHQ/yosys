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
	bool nested_mode;

	TribufConfig() {
		merge_mode = false;
		logic_mode = false;
		formal_mode = false;
		nested_mode = false;
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

private:
	struct TribufSelPart {
		SigSpec sig;
		bool inv;

		TribufSelPart(const SigSpec &sig, bool inv) : sig(sig), inv(inv)
		{
		}
	};

	typedef std::vector<TribufSelPart> TribufSel;

	static bool collect_tribuf_cell(Cell *cell, TribufSel &sel, const dict<SigSpec, vector<Cell*>> &muxes)
	{
		if (cell->type.in(ID($tribuf), ID($_TBUF_)))
		{
			sel.emplace_back(cell->getPort(ID::EN), /*inv*/ true);
			return true;
		}

		log_assert(cell->type.in(ID($mux), ID($_MUX_)));

		const SigSpec &s_sig = cell->getPort(ID::S);
		const SigSpec &a_sig = cell->getPort(ID::A);
		const SigSpec &b_sig = cell->getPort(ID::B);

		vector<Cell*> cells = muxes.at(a_sig, {});
		// We specifically ignore cases when there are multiple
		// driving multiplexers.
		Cell *next_cell = (cells.size() == 1) ? cells.front() : nullptr;
		if ((next_cell && collect_tribuf_cell(next_cell, sel, muxes)) || is_all_z(a_sig))
		{
			sel.emplace_back(s_sig, /*inv*/ true);
			return true;
		}

		cells = muxes.at(b_sig, {});
		next_cell = (cells.size() == 1) ? cells.front() : nullptr;
		if ((next_cell && collect_tribuf_cell(next_cell, sel, muxes)) || is_all_z(b_sig))
		{
			sel.emplace_back(s_sig, /*inv*/ false);
			return true;
		}
		return false;
	}

	static SigSpec construct_new_sel(Module *module, const TribufSel &new_sel)
	{
		size_t count = new_sel.size();
		log_assert(count > 0);

		Wire *res_wire = nullptr;
		Cell *res_cell = nullptr;
		SigSpec result = new_sel[0].sig;
		if (new_sel[0].inv)
		{
			res_wire = module->addWire(NEW_ID, new_sel[0].sig.size());
			res_cell = module->addNot(NEW_ID, result, res_wire);
			result = res_cell->getPort(ID::Y);
		}

		for (size_t i = 1; i < count; ++i)
		{
			const TribufSelPart &sel_part = new_sel[i];
			SigSpec curr_sig = sel_part.sig;
			if (sel_part.inv)
			{
				res_wire = module->addWire(NEW_ID, sel_part.sig.size());
				res_cell = module->addNot(NEW_ID, sel_part.sig, res_wire);
				curr_sig = res_cell->getPort(ID::Y);
			}

			res_wire = module->addWire(NEW_ID, std::max(curr_sig.size(), result.size()));
			res_cell = module->addAnd(NEW_ID, result, curr_sig, res_wire);
			result = res_cell->getPort(ID::Y);
		}

		return result;
	}

	static void nested_mux_to_tribuf(Module *module, Cell *cell, dict<SigSpec, vector<Cell*>> &tribufs, const dict<SigSpec, vector<Cell*>> &muxes)
	{
		TribufSel new_sel;
		// Collect all selector parts by traversing multiplexers recursively.
		if (!collect_tribuf_cell(cell, new_sel, muxes))
			return;

		// Construct a conjunction of all selectors leading to Z-vector.
		SigSpec new_sel_sig = construct_new_sel(module, new_sel);

		SigSpec old_sig = cell->getPort(ID::Y);
		// Create a new wire to rebind old multiplexer to.
		Wire *mux_wire = module->addWire(NEW_ID, old_sig.size());
		cell->setPort(ID::Y, mux_wire);

		// Create an inverse of the conjunction to create the new tri-state cell.
		Wire *not_wire = module->addWire(NEW_ID, new_sel_sig.size());
		module->addNot(NEW_ID, new_sel_sig, not_wire);
		Cell *tribuf_cell = module->addTribuf(NEW_ID, mux_wire, not_wire, old_sig);
		tribufs[old_sig].push_back(tribuf_cell);
	}

public:
	void run()
	{
		dict<SigSpec, vector<Cell*>> tribuf_cells;
		dict<SigSpec, vector<Cell*>> y_port_to_mux;
		pool<SigBit> output_bits;

		if (config.logic_mode || config.formal_mode)
			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						output_bits.insert(bit);

		for (auto cell : module->selected_cells())
		{
			if (config.nested_mode && cell->type.in(ID($tribuf), ID($_TBUF_), ID($mux), ID($_MUX_)))
				y_port_to_mux[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type == ID($tribuf))
				tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type == ID($_TBUF_))
				tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);

			if (cell->type.in(ID($mux), ID($_MUX_)))
			{
				IdString en_port = cell->type == ID($mux) ? ID::EN : ID::E;
				IdString tri_type = cell->type == ID($mux) ? ID($tribuf) : ID($_TBUF_);
				bool a_all_z = is_all_z(cell->getPort(ID::A));
				bool b_all_z = is_all_z(cell->getPort(ID::B));

				if (a_all_z && b_all_z) {
					module->remove(cell);
					continue;
				}

				if (a_all_z) {
					cell->setPort(ID::A, cell->getPort(ID::B));
					cell->setPort(en_port, cell->getPort(ID::S));
					cell->unsetPort(ID::B);
					cell->unsetPort(ID::S);
					cell->type = tri_type;
					tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);
					module->design->scratchpad_set_bool("tribuf.added_something", true);
					continue;
				}

				if (b_all_z) {
					cell->setPort(en_port, module->Not(NEW_ID, cell->getPort(ID::S)));
					cell->unsetPort(ID::B);
					cell->unsetPort(ID::S);
					cell->type = tri_type;
					tribuf_cells[sigmap(cell->getPort(ID::Y))].push_back(cell);
					module->design->scratchpad_set_bool("tribuf.added_something", true);
					continue;
				}
			}
		}

		if (config.nested_mode)
		{
			for (auto &[y_sig, muxes]: y_port_to_mux)
			{
				for (Cell *cell: muxes)
				{
					// Tri-state cells are handled later, so at this point
					// we need to process only "true" multiplexers.
					if (cell->type.in(ID($mux), ID($_MUX_)))
						nested_mux_to_tribuf(module, cell, tribuf_cells, y_port_to_mux);
				}
			}

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

						std::string name = stringf("$tribuf_conflict$%s", log_id(cell->name));
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
		log("    -nested\n");
		log("        convert multiplexers using tri-state cells to tri-state cells\n");
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
			if (args[argidx] == "-nested") {
				config.nested_mode = true;
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
