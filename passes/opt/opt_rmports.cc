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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptRmportsPass : public Pass {
	OptRmportsPass() : Pass("opt_rmports", "remove top-level ports with no connections") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_rmports\n");
		log("\n");
		log("This pass identifies ports in the top-level design which are not used or driven\n");
		log("and removes them\n");
		log("\n");
	}

	virtual void execute(std::vector<std::string> /*args*/, RTLIL::Design *design)
	{
		log_header(design, "Executing OPT_RMPORTS pass (remove top level ports with no connections).\n");
		ProcessModule(design->top_module());
	}

	virtual void ProcessModule(RTLIL::Module* module)
	{
		log("Finding unconnected ports in module %s\n", module->name.c_str());

		std::set<RTLIL::IdString> used_ports;

		//See what wires are used.
		//Start by checking connections between named wires
		auto& conns = module->connections();
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

				//log("  conn %s, %s\n", w1->name.c_str(), w2->name.c_str());

				if( (w1->port_input || w1->port_output) && (used_ports.find(w1->name) == used_ports.end()) )
					used_ports.emplace(w1->name);

				if( (w2->port_input || w2->port_output) && (used_ports.find(w2->name) == used_ports.end()) )
					used_ports.emplace(w2->name);
			}
		}

		//Then check connections to cells
		auto cells = module->cells();
		for(auto cell : cells)
		{
			auto& cconns = cell->connections();
			for(auto conn : cconns)
			{
				for(int i=0; i<conn.second.size(); i++)
				{
					auto sig = conn.second[i].wire;
					if(sig == NULL)
						continue;

					//log("  sig %s\n", sig->name.c_str());
					if( (sig->port_input || sig->port_output) && (used_ports.find(sig->name) == used_ports.end()) )
						used_ports.emplace(sig->name);
				}
			}
		}

		//Now that we know what IS used, get rid of anything that isn't in that list
		std::set<RTLIL::IdString> unused_ports;
		for(auto port : module->ports)
		{
			if(used_ports.find(port) != used_ports.end())
				continue;
			unused_ports.emplace(port);
		}

		//Print the ports out as we go through them
		for(auto port : unused_ports)
		{
			log("  removing unused top-level port %s\n", port.c_str());

			//Remove from ports list
			for(size_t i=0; i<module->ports.size(); i++)
			{
				if(module->ports[i] == port)
				{
					module->ports.erase(module->ports.begin() + i);
					break;
				}
			}

			//Mark the wire as no longer a port
			auto wire = module->wire(port);
			wire->port_input = false;
			wire->port_output = false;
			wire->port_id = 0;
		}
		log("Removed %zu unused top-level ports.\n", unused_ports.size());

		//Re-number all of the wires that DO have ports still on them
		for(size_t i=0; i<module->ports.size(); i++)
		{
			auto port = module->ports[i];
			auto wire = module->wire(port);
			wire->port_id = i+1;
		}
	}

} OptRmportsPass;

PRIVATE_NAMESPACE_END
