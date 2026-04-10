/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Silimate Inc.
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

// Worker that counts fanout for each driver (input ports and cell output ports)
// and reports any that exceed a user-specified limit.
struct ReportFanoutWorker
{
	Module *module;
	SigMap sigmap;

	// Maps each driven SigBit to its fanout count
	dict<SigBit, int> bit_fanout;

	// Maps each driven SigBit back to its driver:
	//   - For input ports:       driver_port[bit] = (wire_name, IdString())
	//   - For cell output ports:  driver_port[bit] = (cell_name, port_name)
	dict<SigBit, pair<IdString, IdString>> bit_driver;

	// SigBits that are clock or reset signals (driven into CLK/RST/ARST ports)
	pool<SigBit> clk_rst_bits;

	ReportFanoutWorker(Module *module, bool skip_clk_rst) : module(module), sigmap(module)
	{
		// Record drivers from input ports
		// Every bit of an input port wire is a driver into the module
		for (auto wire : module->wires()) {
			if (!wire->port_input) continue;
			SigSpec sig = sigmap(wire);
			for (int i = 0; i < GetSize(sig); i++) {
				SigBit bit = sig[i];
				bit_driver[bit] = {wire->name, IdString()};
			}
		}

		// Record drivers from cell output ports
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first)) continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit = sigmap(conn.second[i]);
					bit_driver[bit] = {cell->name, conn.first};
				}
			}
		}

		// Identify clock and reset signals by looking at FF cell ports,
		// then trace backwards through driver cells to mark the original
		// source bits (handles intermediate cells like $reduce_or inserted
		// by proc_dff between input ports and FF ARST/CLK).
		if (skip_clk_rst) {
			for (auto cell : module->cells()) {
				for (auto port_id : {ID(CLK), ID(C)}) {
					if (cell->hasPort(port_id)) {
						SigSpec sig = sigmap(cell->getPort(port_id));
						for (auto bit : sig)
							clk_rst_bits.insert(bit);
					}
				}
				for (auto port_id : {ID(RST), ID(ARST), ID(SRST), ID(R), ID(S)}) {
					if (cell->hasPort(port_id)) {
						SigSpec sig = sigmap(cell->getPort(port_id));
						for (auto bit : sig)
							clk_rst_bits.insert(bit);
					}
				}
			}

			// Build a map from each driven bit to the cell that drives it
			dict<SigBit, Cell*> bit_to_cell;
			for (auto cell : module->cells()) {
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first)) continue;
					for (auto bit : sigmap(conn.second))
						bit_to_cell[bit] = cell;
				}
			}

			// Iteratively trace backwards: if a clk/rst bit is driven by a
			// cell, mark all of that cell's input bits as clk/rst too.
			bool changed = true;
			while (changed) {
				changed = false;
				pool<SigBit> new_bits;
				for (auto bit : clk_rst_bits) {
					auto it = bit_to_cell.find(bit);
					if (it == bit_to_cell.end()) continue;
					Cell *drv_cell = it->second;
					for (auto &conn : drv_cell->connections()) {
						if (!drv_cell->input(conn.first)) continue;
						for (auto inp_bit : sigmap(conn.second)) {
							if (!clk_rst_bits.count(inp_bit))
								new_bits.insert(inp_bit);
						}
					}
				}
				if (!new_bits.empty()) {
					changed = true;
					for (auto bit : new_bits)
						clk_rst_bits.insert(bit);
				}
			}
		}

		// Count fanout: each cell input pin connection is one fanout
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first)) continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit = sigmap(conn.second[i]);
					if (bit_driver.count(bit))
						bit_fanout[bit]++;
				}
			}
		}

		// Count fanout: each output port connection is one fanout
		for (auto wire : module->wires()) {
			if (!wire->port_output) continue;
			SigSpec sig = sigmap(wire);
			for (int i = 0; i < GetSize(sig); i++) {
				SigBit bit = sig[i];
				if (bit_driver.count(bit))
					bit_fanout[bit]++;
			}
		}
	}

	// Report all drivers whose total fanout exceeds the limit.
	// Aggregates per-bit fanout to the (driver, port) level.
	// If f is non-null, also writes the same lines to that file.
	void report(int limit, FILE *f = nullptr)
	{
		// Aggregate fanout per driver (identified by driver_name + port_name),
		// skipping bits identified as clock or reset signals.
		dict<pair<IdString, IdString>, int> driver_fanout;
		for (auto &entry : bit_fanout) {
			SigBit bit = entry.first;
			if (clk_rst_bits.count(bit))
				continue;
			int count = entry.second;
			auto &drv = bit_driver.at(bit);
			driver_fanout[drv] += count;
		}

		// Report any driver exceeding the limit
		for (auto &entry : driver_fanout) {
			int fanout = entry.second;
			if (fanout <= limit) continue;

			IdString driver_name = entry.first.first;
			IdString port_name = entry.first.second;

			if (port_name == IdString()) {
				// Driver is an input port
				log_warning("(%s, %s) = %d\n",
					log_id(module), log_id(driver_name), fanout);
				if (f)
					fprintf(f, "(%s, %s) = %d\n",
						log_id(module), log_id(driver_name), fanout);
			} else {
				// Driver is a cell output port
				log_warning("(%s, %s, %s) = %d\n",
					log_id(module), log_id(driver_name), log_id(port_name), fanout);
				if (f)
					fprintf(f, "(%s, %s, %s) = %d\n",
						log_id(module), log_id(driver_name), log_id(port_name), fanout);
			}
		}
	}
};

struct ReportFanoutPass : public Pass {
	ReportFanoutPass() : Pass("report_fanout", "report nets with fanout exceeding a limit") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    report_fanout -limit <n> [-file <filename>] [-include_clk_rst] [selection]\n");
		log("\n");
		log("This command reports all input ports and cell output ports whose fanout\n");
		log("exceeds the specified limit. Results are printed as log_warning messages.\n");
		log("\n");
		log("By default, nets driving clock or reset ports (CLK, C, RST, ARST, SRST,\n");
		log("R, S) on flip-flops are excluded from the report.\n");
		log("\n");
		log("    -limit n\n");
		log("        fanout threshold. Nets with fanout > n are reported.\n");
		log("\n");
		log("    -file filename\n");
		log("        also write the report to the specified file.\n");
		log("\n");
		log("    -include_clk_rst\n");
		log("        include clock and reset nets in the report.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int limit = -1;
		std::string filename;
		bool include_clk_rst = false;
		log_header(design, "Executing REPORT_FANOUT pass (reporting nets with high fanout).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-limit" && argidx + 1 < args.size()) {
				try {
					limit = std::stoi(args[++argidx]);
				} catch (...) {
					log_cmd_error("Invalid value for -limit: '%s'. Expected an integer.\n", args[argidx].c_str());
				}
				continue;
			}
			if (args[argidx] == "-file" && argidx + 1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-include_clk_rst") {
				include_clk_rst = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

			if (limit < 0)
				log_cmd_error("Missing required -limit option (must be a non-negative integer).\n");

		// Open output file if requested
		FILE *f = nullptr;
		if (!filename.empty()) {
			f = fopen(filename.c_str(), "w");
			if (!f)
				log_cmd_error("Cannot open file '%s' for writing.\n", filename.c_str());
		}

		bool skip_clk_rst = !include_clk_rst;
		for (auto module : design->selected_modules())
		{
			log("Analyzing fanout for module %s...\n", log_id(module));
			ReportFanoutWorker worker(module, skip_clk_rst);
			worker.report(limit, f);
		}

		if (f)
			fclose(f);
	}
} ReportFanoutPass;

PRIVATE_NAMESPACE_END
