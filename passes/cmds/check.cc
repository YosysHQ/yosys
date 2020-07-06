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
#include "kernel/celltypes.h"
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CheckPass : public Pass {
	CheckPass() : Pass("check", "check for obvious problems in the design") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    check [options] [selection]\n");
		log("\n");
		log("This pass identifies the following problems in the current design:\n");
		log("\n");
		log(" - combinatorial loops\n");
		log("\n");
		log(" - two or more conflicting drivers for one wire\n");
		log("\n");
		log(" - used wires that do not have a driver\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("  -noinit\n");
		log("    Also check for wires which have the 'init' attribute set.\n");
		log("\n");
		log("  -initdrv\n");
		log("    Also check for wires that have the 'init' attribute set and are not\n");
		log("    driven by an FF cell type.\n");
		log("\n");
		log("  -mapped\n");
		log("    Also check for internal cells that have not been mapped to cells of the\n");
		log("    target architecture.\n");
		log("\n");
		log("  -allow-tbuf\n");
		log("    Modify the -mapped behavior to still allow $_TBUF_ cells.\n");
		log("\n");
		log("  -assert\n");
		log("    Produce a runtime error if any problems are found in the current design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int counter = 0;
		bool noinit = false;
		bool initdrv = false;
		bool mapped = false;
		bool allow_tbuf = false;
		bool assert_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-noinit") {
				noinit = true;
				continue;
			}
			if (args[argidx] == "-initdrv") {
				initdrv = true;
				continue;
			}
			if (args[argidx] == "-mapped") {
				mapped = true;
				continue;
			}
			if (args[argidx] == "-allow-tbuf") {
				allow_tbuf = true;
				continue;
			}
			if (args[argidx] == "-assert") {
				assert_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing CHECK pass (checking for obvious problems).\n");

		pool<IdString> fftypes;
		fftypes.insert("$sr");
		fftypes.insert("$ff");
		fftypes.insert("$dff");
		fftypes.insert("$dffe");
		fftypes.insert("$dffsr");
		fftypes.insert("$adff");
		fftypes.insert("$dlatch");
		fftypes.insert("$dlatchsr");
		fftypes.insert("$_DFFE_NN_");
		fftypes.insert("$_DFFE_NP_");
		fftypes.insert("$_DFFE_PN_");
		fftypes.insert("$_DFFE_PP_");
		fftypes.insert("$_DFFSR_NNN_");
		fftypes.insert("$_DFFSR_NNP_");
		fftypes.insert("$_DFFSR_NPN_");
		fftypes.insert("$_DFFSR_NPP_");
		fftypes.insert("$_DFFSR_PNN_");
		fftypes.insert("$_DFFSR_PNP_");
		fftypes.insert("$_DFFSR_PPN_");
		fftypes.insert("$_DFFSR_PPP_");
		fftypes.insert("$_DFF_NN0_");
		fftypes.insert("$_DFF_NN1_");
		fftypes.insert("$_DFF_NP0_");
		fftypes.insert("$_DFF_NP1_");
		fftypes.insert("$_DFF_N_");
		fftypes.insert("$_DFF_PN0_");
		fftypes.insert("$_DFF_PN1_");
		fftypes.insert("$_DFF_PP0_");
		fftypes.insert("$_DFF_PP1_");
		fftypes.insert("$_DFF_P_");
		fftypes.insert("$_DLATCHSR_NNN_");
		fftypes.insert("$_DLATCHSR_NNP_");
		fftypes.insert("$_DLATCHSR_NPN_");
		fftypes.insert("$_DLATCHSR_NPP_");
		fftypes.insert("$_DLATCHSR_PNN_");
		fftypes.insert("$_DLATCHSR_PNP_");
		fftypes.insert("$_DLATCHSR_PPN_");
		fftypes.insert("$_DLATCHSR_PPP_");
		fftypes.insert("$_DLATCH_N_");
		fftypes.insert("$_DLATCH_P_");
		fftypes.insert("$_FF_");

		for (auto module : design->selected_whole_modules_warn())
		{
			if (module->has_processes_warn())
				continue;

			log("checking module %s..\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, vector<string>> wire_drivers;
			dict<SigBit, int> wire_drivers_count;
			pool<SigBit> used_wires;
			TopoSort<string> topo;

			for (auto cell : module->cells())
			{
				if (mapped && cell->type.begins_with("$") && design->module(cell->type) == nullptr) {
					if (allow_tbuf && cell->type == ID($_TBUF_)) goto cell_allowed;
					log_warning("Cell %s.%s is an unmapped internal cell of type %s.\n", log_id(module), log_id(cell), log_id(cell->type));
					counter++;
				cell_allowed:;
				}
				for (auto &conn : cell->connections()) {
					SigSpec sig = sigmap(conn.second);
					bool logic_cell = yosys_celltypes.cell_evaluable(cell->type);
					if (cell->input(conn.first))
						for (auto bit : sig)
							if (bit.wire) {
								if (logic_cell)
									topo.edge(stringf("wire %s", log_signal(bit)),
											stringf("cell %s (%s)", log_id(cell), log_id(cell->type)));
								used_wires.insert(bit);
							}
					if (cell->output(conn.first))
						for (int i = 0; i < GetSize(sig); i++) {
							if (logic_cell)
								topo.edge(stringf("cell %s (%s)", log_id(cell), log_id(cell->type)),
										stringf("wire %s", log_signal(sig[i])));
							if (sig[i].wire)
								wire_drivers[sig[i]].push_back(stringf("port %s[%d] of cell %s (%s)",
										log_id(conn.first), i, log_id(cell), log_id(cell->type)));
						}
					if (!cell->input(conn.first) && cell->output(conn.first))
						for (auto bit : sig)
							if (bit.wire) wire_drivers_count[bit]++;
				}
			}

			pool<SigBit> init_bits;

			for (auto wire : module->wires()) {
				if (wire->port_input) {
					SigSpec sig = sigmap(wire);
					for (int i = 0; i < GetSize(sig); i++)
						wire_drivers[sig[i]].push_back(stringf("module input %s[%d]", log_id(wire), i));
				}
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						if (bit.wire) used_wires.insert(bit);
				if (wire->port_input && !wire->port_output)
					for (auto bit : sigmap(wire))
						if (bit.wire) wire_drivers_count[bit]++;
				if (wire->attributes.count("\\init")) {
					Const initval = wire->attributes.at("\\init");
					for (int i = 0; i < GetSize(initval) && i < GetSize(wire); i++)
						if (initval[i] == State::S0 || initval[i] == State::S1)
							init_bits.insert(sigmap(SigBit(wire, i)));
					if (noinit) {
						log_warning("Wire %s.%s has an unprocessed 'init' attribute.\n", log_id(module), log_id(wire));
						counter++;
					}
				}
			}

			for (auto it : wire_drivers)
				if (wire_drivers_count[it.first] > 1) {
					string message = stringf("multiple conflicting drivers for %s.%s:\n", log_id(module), log_signal(it.first));
					for (auto str : it.second)
						message += stringf("    %s\n", str.c_str());
					log_warning("%s", message.c_str());
					counter++;
				}

			for (auto bit : used_wires)
				if (!wire_drivers.count(bit)) {
					log_warning("Wire %s.%s is used but has no driver.\n", log_id(module), log_signal(bit));
					counter++;
				}

			topo.sort();
			for (auto &loop : topo.loops) {
				string message = stringf("found logic loop in module %s:\n", log_id(module));
				for (auto &str : loop)
					message += stringf("    %s\n", str.c_str());
				log_warning("%s", message.c_str());
				counter++;
			}

			if (initdrv)
			{
				for (auto cell : module->cells())
				{
					if (fftypes.count(cell->type) == 0)
						continue;

					for (auto bit : sigmap(cell->getPort("\\Q")))
						init_bits.erase(bit);
				}

				SigSpec init_sig(init_bits);
				init_sig.sort_and_unify();

				for (auto chunk : init_sig.chunks()) {
					log_warning("Wire %s.%s has 'init' attribute and is not driven by an FF cell.\n", log_id(module), log_signal(chunk));
					counter++;
				}
			}
		}

		log("found and reported %d problems.\n", counter);

		if (assert_mode && counter > 0)
			log_error("Found %d problems in 'check -assert'.\n", counter);
	}
} CheckPass;

PRIVATE_NAMESPACE_END
