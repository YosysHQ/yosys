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

#include <cassert>

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SplitInOutPass : public ScriptPass {
	SplitInOutPass() : ScriptPass("splitinout", "split inout ports into separate in and out ports") { }

	RTLIL::Design* design_;
	virtual void clear_flags() YS_OVERRIDE
	{
		design_ = nullptr;
	}

	virtual void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splitinout [options] [selection]\n");
		log("\n");
		log("This command splits multi-bit nets into single-bit nets.\n");
		log("\n");
	}

	void runf(const char* fmt...)
	{
		va_list args;
		va_start(args, fmt);

		char s[255];
		int i = vsnprintf(s, sizeof(s), fmt, args);
		log("Running: %s\n", s);
		run(std::string(s, i));
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				//top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		design_ = design;

		log_header(design, "Executing splitinout pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	Wire* new_module_port(RTLIL::Module* module, RTLIL::Wire* wire, bool input)
	{
		std::string name_extra;
		if (input) {
			name_extra = "_I";
		} else {
			name_extra = "_O";
		}

		RTLIL::IdString new_name = std::string(wire->name.c_str())+name_extra;
		Wire* new_wire = module->addWire(new_name, 1);
		new_wire->port_input = input;
		new_wire->port_output = !input;
		new_wire->port_id = module->wires_.size();
		module->fixup_ports();

		if (wire->attributes.count("\\src")) {
			new_wire->attributes["\\src"] = wire->attributes.at("\\src");
		}
		if (wire->attributes.count("\\keep")) {
			new_wire->attributes["\\keep"] = wire->attributes.at("\\keep");
		}

		log("Created %s new wire %s\n", log_id(module), log_signal(new_wire));
		return new_wire;
	}

	std::pair<Wire*, Wire*> demote_module_port(RTLIL::Module* module, RTLIL::Wire* wire)
	{
		assert(wire->port_input);
		assert(wire->port_output);

		log("Demoting inout %s wire %s\n", log_id(module), log_signal(wire));
		Wire* iwire = new_module_port(module, wire, true);
		Wire* owire = new_module_port(module, wire, false);

		//wire->port_id = 0;
		//wire->port_input = false;
		//wire->port_output = false;
		//module->fixup_ports();
		log("Removed %s old wire %s\n", log_id(module), log_signal(wire));
		return std::make_pair(iwire, owire);
	}

	virtual void script() YS_OVERRIDE
	{
		pool<SigSpec> bidir_specs;
		pool<Module*> bidir_types;

		for (auto module : design_->selected_modules())
		{
			SigMap sigmap(module);

			// Find cells inside this module which have bidir ports
			log("Checking cells in %s\n", log_id(module));
			for (auto cell : module->cells()) {
				if (!module->selected(cell))
					continue;

				for (auto &conn : cell->connections())
				{
					if (!cell->known())
						continue;

					bool cellport_out = cell->output(conn.first);
					bool cellport_in = cell->input(conn.first);
					if (!(cellport_out && cellport_in))
						continue;

					log("Got inout %s cell %s conn %s\n", log_id(module), log_id(cell), log_signal(conn.second));
					bidir_specs.insert(sigmap(conn.second));

					// We don't want to modify yosys internal modules
					if (yosys_celltypes.cell_known(cell->type))
						continue;
					bidir_types.insert(design_->module(cell->type));
				}
			}
			log("\n");

			// Does this module have inout ports?
			log("Checking wires in %s\n", log_id(module));
			for (auto wire : module->selected_wires())
			{
				if (!(wire->port_input && wire->port_output))
					continue;

				log("Got inout %s wire %s\n", log_id(module), log_signal(wire));
				bidir_specs.insert(sigmap(wire));
			}
			log("\n");
			log("------ \n");

			// Convert the inout ports into separate in + out ports.
			for (auto submodule : bidir_types)
			{
				pool<Wire*> to_rewire;
				for (auto wire : submodule->wires())
				{
					if (!(wire->port_input && wire->port_output))
						continue;
					to_rewire.insert(wire);
				}
				for (auto wire : to_rewire)
				{
					demote_module_port(submodule, wire);
				}
				log("\n");
			}
			log("------ \n");

			for (auto spec : bidir_specs)
			{
				log("Rewiring inout signal %s\n", log_signal(spec));

				Wire* iwire = module->addWire(NEW_ID, GetSize(spec));
				//iwire->port_input = true;
				log(" New in wire %s\n", log_signal(iwire));
				Wire* owire = module->addWire(NEW_ID, GetSize(spec));
				//owire->port_output = true;
				log(" New out wire %s\n", log_signal(owire));

				log("Rewiring cells\n");
				for (auto cell : module->cells()) {
					if (!module->selected(cell)) {
						log("Ignoring unselected %s\n", log_id(cell));
						continue;
					}
					//if (yosys_celltypes.cell_known(cell->type)) {
					//	//log("Ignoring Yosys internal %s\n", log_id(cell));
					//	  continue;
					//}

					//log(" Rewiring %s\n", log_id(cell));
					pool<IdString> conn_names;
					for (auto &conn : cell->connections())
					{
						if (spec != sigmap(conn.second))
							continue;

						bool cellport_out = cell->output(conn.first);
						bool cellport_in = cell->input(conn.first);

						if (cellport_out && cellport_in)
						{
							conn_names.insert(conn.first);
						} else
						if (cellport_out)
						{
							cell->setPort(conn.first, iwire);
							log("  Connecting %s.%s->%s\n", log_id(cell), log_id(conn.first), log_signal(cell->getPort(conn.first)));
						} else
						if (cellport_in)
						{
							cell->setPort(conn.first, owire);
							log("  Connecting %s.%s->%s\n", log_id(cell), log_id(conn.first), log_signal(cell->getPort(conn.first)));
						}
					}

					for (auto n : conn_names)
					{
						// Creating cell input port
						RTLIL::IdString oname = std::string(n.c_str())+"_I";
						Wire* cell_owire = module->addWire(NEW_ID, GetSize(spec));
						cell_owire->port_output = true;
						cell->setPort(oname, cell_owire);
						log("  Creating %s.%s->%s\n", log_id(cell), oname.c_str(), log_signal(cell->getPort(oname)));
						module->connect(cell->getPort(oname), owire);
						log("  Connecting %s.%s->%s.%s\n", log_id(cell), log_signal(cell->getPort(oname)), log_id(module), log_signal(owire));

						// Creating cell output port
						RTLIL::IdString iname = std::string(n.c_str())+"_O";
						Wire* cell_iwire = module->addWire(NEW_ID, GetSize(spec));
						cell_iwire->port_input = true;
						cell->setPort(iname, cell_iwire);
						log("  Creating %s.%s->%s\n", log_id(cell), iname.c_str(), log_signal(cell->getPort(iname)));
						module->connect(iwire, cell->getPort(iname));
						log("  Connecting %s.%s->%s.%s\n", log_id(module), log_signal(iwire), log_id(cell), log_signal(cell->getPort(iname)));

						log("  Unconnecting %s.%s\n", log_id(cell), n.c_str());
						cell->unsetPort(n);
					}

				}

				log("Rewiring wires\n");
				pool<Wire*> full_rewire;
				for (auto wire : module->selected_wires())
				{
					if (spec != sigmap(wire))
						continue;
					if (wire->port_input && wire->port_output) {
						full_rewire.insert(wire);
					} else
					if (wire->port_input)
					{
						module->connect(wire, owire);
						log(" Connecting %s.%s->%s\n", log_id(module), log_signal(wire), log_signal(owire));
					} else
					if (wire->port_output)
					{
						module->connect(wire, iwire);
						log(" Connecting %s.%s->%s\n", log_id(module), log_signal(wire), log_signal(iwire));
					}
				}

				for (auto wire : full_rewire)
				{
					auto w = demote_module_port(module, wire);
					module->connect(w.second, iwire);
					log(" Connecting %s.%s->%s\n", log_id(module), log_id(w.second), log_signal(iwire));
					module->connect(owire, w.first);
					log(" Connecting %s.%s->%s\n", log_id(module), log_signal(owire), log_id(w.first));

					wire->port_id = 0;
					wire->port_input = false;
					wire->port_output = false;
					module->fixup_ports();
					log(" Removing %s.%s\n", log_id(module), log_signal(wire));
				}
				log("\n");
			}

			log("------ \n");
			for (auto submodule : bidir_types)
			{
				pool<Wire*> to_rewire;
				for (auto wire : submodule->wires())
				{
					if (!(wire->port_input && wire->port_output))
						continue;
					to_rewire.insert(wire);
				}
				for (auto wire : to_rewire)
				{
					wire->port_id = 0;
					wire->port_input = false;
					wire->port_output = false;
					submodule->fixup_ports();
					log("Removing %s.%s\n", log_id(submodule), log_signal(wire));
				}
				log("\n");
			}
			log("----------\n");
		}
		runf("ls");
	}
} SplitInOutPass;

PRIVATE_NAMESPACE_END
