/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

	TribufConfig() {
		merge_mode = false;
		logic_mode = false;
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

	void run()
	{
		dict<SigSpec, vector<Cell*>> tribuf_cells;
		pool<SigBit> output_bits;

		if (config.logic_mode)
			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						output_bits.insert(bit);

		for (auto cell : module->selected_cells())
		{
			if (cell->type == "$tribuf")
				tribuf_cells[sigmap(cell->getPort("\\Y"))].push_back(cell);

			if (cell->type == "$_TBUF_")
				tribuf_cells[sigmap(cell->getPort("\\Y"))].push_back(cell);

			if (cell->type.in("$mux", "$_MUX_"))
			{
				IdString en_port = cell->type == "$mux" ? "\\EN" : "\\E";
				IdString tri_type = cell->type == "$mux" ? "$tribuf" : "$_TBUF_";

				if (is_all_z(cell->getPort("\\A")) && is_all_z(cell->getPort("\\B"))) {
					module->remove(cell);
					continue;
				}

				if (is_all_z(cell->getPort("\\A"))) {
					cell->setPort("\\A", cell->getPort("\\B"));
					cell->setPort(en_port, cell->getPort("\\S"));
					cell->unsetPort("\\B");
					cell->unsetPort("\\S");
					cell->type = tri_type;
					tribuf_cells[sigmap(cell->getPort("\\Y"))].push_back(cell);
					continue;
				}

				if (is_all_z(cell->getPort("\\B"))) {
					cell->setPort(en_port, module->Not(NEW_ID, cell->getPort("\\S")));
					cell->unsetPort("\\B");
					cell->unsetPort("\\S");
					cell->type = tri_type;
					tribuf_cells[sigmap(cell->getPort("\\Y"))].push_back(cell);
					continue;
				}
			}
		}

		if (config.merge_mode || config.logic_mode)
		{
			for (auto &it : tribuf_cells)
			{
				bool no_tribuf = false;

				if (config.logic_mode) {
					no_tribuf = true;
					for (auto bit : it.first)
						if (output_bits.count(bit))
							no_tribuf = false;
				}

				if (GetSize(it.second) <= 1 && !no_tribuf)
					continue;

				SigSpec pmux_b, pmux_s;
				for (auto cell : it.second) {
					if (cell->type == "$tribuf")
						pmux_s.append(cell->getPort("\\EN"));
					else
						pmux_s.append(cell->getPort("\\E"));
					pmux_b.append(cell->getPort("\\A"));
					module->remove(cell);
				}

				SigSpec muxout = GetSize(pmux_s) > 1 ? module->Pmux(NEW_ID, SigSpec(State::Sx, GetSize(it.first)), pmux_b, pmux_s) : pmux_b;

				if (no_tribuf)
					module->connect(it.first, muxout);
				else
					module->addTribuf(NEW_ID, muxout, module->ReduceOr(NEW_ID, pmux_s), it.first);
			}
		}
	}
};

struct TribufPass : public Pass {
	TribufPass() : Pass("tribuf", "infer tri-state buffers") { }
	virtual void help()
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
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
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
