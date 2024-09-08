/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Miodrag Milanovic <micko@yosyshq.com>
 *  Copyright (C) 2023
 *        National Technology & Engineering Solutions of Sandia, LLC (NTESS)
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

YOSYS_NAMESPACE_BEGIN

struct TrackingItem
{
	pool<Cell*> assertion_cells;
	std::vector<std::string> names;
};

typedef dict<RTLIL::Module*, TrackingItem> TrackingData;

struct SynthPropWorker
{
	// pointer to main design
	RTLIL::Design *design;

	RTLIL::IdString top_name;

	RTLIL::Module *module;

	std::string map_file;

	bool or_outputs;

	IdString port_name;

	IdString reset_name;

	bool reset_pol;

	// basic contrcutor
	SynthPropWorker(RTLIL::Design *design) : design(design), or_outputs(false), port_name(RTLIL::escape_id("assertions")) {}

	void tracing(RTLIL::Module *mod, int depth, TrackingData &tracing_data, std::string hier_path);
	void run();
};

void SynthPropWorker::tracing(RTLIL::Module *mod, int depth, TrackingData &tracing_data, std::string hier_path)
{
	log("%*sTracing in module %s..\n", 2*depth, "", log_id(mod));
	tracing_data[mod] = TrackingItem();
	int cnt = 0;
	for (auto cell : mod->cells()) {
		if (cell->type == ID($assert)) {
			log("%*sFound assert %s..\n", 2*(depth+1), "", log_id(cell));
			tracing_data[mod].assertion_cells.emplace(cell);
			if (!or_outputs) {
				tracing_data[mod].names.push_back(hier_path + "." + log_id(cell));
			}
			cnt++;
		}
		else if (RTLIL::Module *submod = design->module(cell->type)) {
			tracing(submod, depth+1, tracing_data, hier_path + "." + log_id(cell));
			if (!or_outputs) {
				for (size_t i = 0; i < tracing_data[submod].names.size(); i++)
					tracing_data[mod].names.push_back(tracing_data[submod].names[i]);
			} else {
				cnt += tracing_data[submod].names.size();
			}
		}
	}
	if (or_outputs && (cnt > 0)) {
		tracing_data[mod].names.push_back("merged_asserts");
	}
}

void SynthPropWorker::run()
{
	if (!module->get_bool_attribute(ID::top))
		log_error("Module is not TOP module\n");

	TrackingData tracing_data;
	tracing(module, 0, tracing_data, log_id(module->name));

	for (auto &data : tracing_data) {
		if (data.second.names.size() == 0) continue;
		RTLIL::Wire *wire = data.first->addWire(port_name, data.second.names.size());
		wire->port_output = true;
		data.first->fixup_ports();
	}

	RTLIL::Wire *output = nullptr;
	for (auto &data : tracing_data) {
		int num = 0;
		RTLIL::Wire *port_wire = data.first->wire(port_name);
		if (!reset_name.empty() && data.first == module) {
			port_wire = data.first->addWire(NEW_ID, data.second.names.size());
			output = port_wire;
		}
		pool<Wire*> connected;
		for (auto cell : data.second.assertion_cells) {
			if (cell->type == ID($assert)) {
				RTLIL::Wire *neg_wire = data.first->addWire(NEW_ID);
				RTLIL::Wire *result_wire = data.first->addWire(NEW_ID);
				data.first->addNot(NEW_ID, cell->getPort(ID::A), neg_wire);
				data.first->addAnd(NEW_ID, cell->getPort(ID::EN), neg_wire, result_wire);
				if (!or_outputs) {
					data.first->connect(SigBit(port_wire,num), result_wire);
				} else {
					connected.emplace(result_wire);
				}
				num++;
			}
		}

		for (auto cell : data.first->cells()) {
			if (RTLIL::Module *submod = design->module(cell->type)) {
				if (tracing_data[submod].names.size() > 0) {
					if (!or_outputs) {
						cell->setPort(port_name, SigChunk(port_wire, num, tracing_data[submod].names.size()));
					} else {
						RTLIL::Wire *result_wire = data.first->addWire(NEW_ID);
						cell->setPort(port_name, result_wire);
						connected.emplace(result_wire);
					}
					num += tracing_data[submod].names.size();
				}
			}
		}
		if (or_outputs && connected.size() > 0) {
			RTLIL::Wire *prev_wire = nullptr;
			for (auto wire : connected ) {
				if (!prev_wire) {
					prev_wire = wire;
				} else {
					RTLIL::Wire *result = data.first->addWire(NEW_ID);
					data.first->addOr(NEW_ID, prev_wire, wire, result);
					prev_wire = result;
				}
			}
			data.first->connect(port_wire, prev_wire);
		}
	}

	// If no assertions found
	if (tracing_data[module].names.size() == 0) return;

	if (!reset_name.empty()) {
		int width = tracing_data[module].names.size();		
		SigSpec reset = module->wire(reset_name);
		reset.extend_u0(width, true);

		module->addDlatchsr(NEW_ID, State::S1, Const(State::S0,width), reset, output, module->wire(port_name), true, true, reset_pol);
	}

	if (!map_file.empty()) {
		std::ofstream fout;
		fout.open(map_file, std::ios::out | std::ios::trunc);
		if (!fout.is_open())
			log_error("Could not open file \"%s\" with write access.\n", map_file.c_str());

		for (auto name : tracing_data[module].names) {
			fout << name << std::endl;
		}
	}
}

struct SyntProperties : public Pass {
	SyntProperties() : Pass("synthprop", "synthesize SVA properties") { }

	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synthprop [options]\n");
		log("\n");
		log("This creates synthesizable properties for the selected module.\n");
		log("\n");
		log("\n");
		log("    -name <portname>\n");
		log("        name of the output port for assertions (default: assertions).\n");
		log("\n");
		log("    -map <filename>\n");
		log("        write the port mapping for synthesizable properties into the given file.\n");
		log("\n");
		log("    -or_outputs\n");
		log("        Or all outputs together to create a single output that goes high when\n");
		log("        any property is violated, instead of generating individual output bits.\n");
		log("\n");
		log("    -reset <portname>\n");
		log("        name of the top-level reset input. Latch a high state on the generated\n");
		log("        outputs until an asynchronous top-level reset input is activated.\n");
		log("\n");
		log("    -resetn <portname>\n");
		log("        like above but with inverse polarity\n");
		log("\n");
		log("\n");
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design* design)
	{
		log_header(design, "Executing SYNTHPROP pass.\n");
		SynthPropWorker worker(design);
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-name" && argidx+1 < args.size()) {
				worker.port_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				worker.map_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-reset" && argidx+1 < args.size()) {
				worker.reset_name = RTLIL::escape_id(args[++argidx]);
				worker.reset_pol = true;
				continue;
			}
			if (args[argidx] == "-resetn" && argidx+1 < args.size()) {
				worker.reset_name = RTLIL::escape_id(args[++argidx]);
				worker.reset_pol = false;
				continue;
			}
			if (args[argidx] == "-or_outputs") {
				worker.or_outputs = true;
				continue;
			}
			break;
		}

		if (args.size() != argidx)
			cmd_error(args, argidx, "Extra argument.");

		auto *top = design->top_module();
		if (top == nullptr)
			log_cmd_error("Can't find top module in current design!\n");

		auto *reset = top->wire(worker.reset_name);
		if (!worker.reset_name.empty() && reset == nullptr)
			log_cmd_error("Can't find reset line in current design!\n");

		worker.module = top;
		worker.run();
	}
} SyntProperties;

YOSYS_NAMESPACE_END
