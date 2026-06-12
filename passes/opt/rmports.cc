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

#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include "kernel/log_help.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RmportsPassPass : public Pass {
	RmportsPassPass() : Pass("rmports", "remove module ports with no connections") { }
	bool formatted_help() override {
		auto *help = PrettyHelp::get_current();
		help->set_group("techlibs/greenpak4");
		return false;
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    rmports [selection]\n");
		log("\n");
		log("This pass identifies ports in the selected modules which are not used or\n");
		log("driven and removes them.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing RMPORTS pass (remove ports with no connections).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		// The set of ports we removed
		dict<IdString, pool<IdString>> removed_ports;

		// Find all of the unused ports, and remove them from that module
		auto modules = design->selected_modules();
		for(auto mod : modules)
			ScanModule(mod, removed_ports);

		// Remove the unused ports from all instances of those modules
		for(auto mod : modules)
			CleanupModule(mod, removed_ports);
	}

	void CleanupModule(Module *module, dict<IdString, pool<IdString>> &removed_ports)
	{
		log("Removing now-unused cell ports in module %s\n", module->name);

		auto cells = module->cells();
		for(auto cell : cells)
		{
			if(removed_ports.find(cell->type) == removed_ports.end())
				continue;

			auto ports_to_remove = removed_ports[cell->type];
			for(auto p : ports_to_remove)
			{
				log("  Removing port \"%s\" from instance \"%s\"\n",
					p.c_str(), cell->type.c_str());
				cell->unsetPort(cell->module->design->twines.add(Twine{p.str()}));
			}
		}
	}

	void ScanModule(Module* module, dict<IdString, pool<IdString>> &removed_ports)
	{
		log("Finding unconnected ports in module %s\n", module->name);

		pool<TwineRef> used_ports;

		// See what wires are used.
		// Start by checking connections between named wires
		auto &conns = module->connections();
		for(auto sigsig : conns)
		{
			auto s1 = sigsig.first;
			auto s2 = sigsig.second;

			int len1 = s1.size();
			int len2 = s2.size();
			int len = len1;
			if(len2 < len1)
				len = len2;

			for(int i=0; i<len; i++)
			{
				auto w1 = s1[i].wire;
				auto w2 = s2[i].wire;
				if( (w1 == NULL) || (w2 == NULL) )
					continue;

				if( (w1->port_input || w1->port_output) && !used_ports.count(w1->name.ref()) )
					used_ports.insert(w1->name.ref());

				if( (w2->port_input || w2->port_output) && !used_ports.count(w2->name.ref()) )
					used_ports.insert(w2->name.ref());
			}
		}

		// Then check connections to cells
		auto cells = module->cells();
		for(auto cell : cells)
		{
			auto &cconns = cell->connections();
			for(auto conn : cconns)
			{
				for(int i=0; i<conn.second.size(); i++)
				{
					auto sig = conn.second[i].wire;
					if(sig == NULL)
						continue;

					if( (sig->port_input || sig->port_output) && !used_ports.count(sig->name.ref()) )
						used_ports.insert(sig->name.ref());
				}
			}
		}

		// Now that we know what IS used, get rid of anything that isn't in that list
		pool<TwineRef> unused_ports;
		for(auto port : module->ports)
		{
			if(used_ports.count(port))
				continue;
			unused_ports.insert(port);
		}

		// Print the ports out as we go through them
		for(auto port : unused_ports)
		{
			log("  removing unused port %s\n", module->design->twines.unescaped_str(port).data());
			IdString port_id(std::string(module->design->twines.str(port)));
			removed_ports[module->name].insert(port_id);

			// Remove from ports list
			for(size_t i=0; i<module->ports.size(); i++)
			{
				if(module->ports[i] == port)
				{
					module->ports.erase(module->ports.begin() + i);
					break;
				}
			}

			// Mark the wire as no longer a port
			auto wire = module->wire(port);
			wire->port_input = false;
			wire->port_output = false;
			wire->port_id = 0;
		}
		log("Removed %d unused ports.\n", GetSize(unused_ports));

		// Re-number all of the wires that DO have ports still on them
		for(size_t i=0; i<module->ports.size(); i++)
		{
			auto port = module->ports[i];
			auto wire = module->wire(port);
			wire->port_id = i+1;
		}
	}

} RmportsPassPass;

PRIVATE_NAMESPACE_END
