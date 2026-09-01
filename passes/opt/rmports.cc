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
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    rmports [options] [selection]\n");
		log("\n");
		log("This pass identifies ports in the selected modules which are not used or\n");
		log("driven and removes them.\n");
		log("\n");
		log("An output which is driven inside the module is also removed, if no\n");
		log("instance of the module uses it. The top module, a module which nothing\n");
		log("instantiates, and a port with the keep attribute stay. This needs a clear\n");
		log("top module: one with the top attribute, or the only module which nothing\n");
		log("instantiates. Without one, a parent design which is not loaded can still\n");
		log("use these ports.\n");
		log("\n");
		log("    -purge\n");
		log("        remove driven outputs also when there is no clear top module\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing RMPORTS pass (remove ports with no connections).\n");

		bool purge_mode = false;

		size_t argidx;
		for(argidx = 1; argidx < args.size(); argidx++)
		{
			if(args[argidx] == "-purge")
			{
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// The set of ports we removed
		dict<IdString, pool<IdString>> removed_ports;

		// Find the ports which are used by some instance in the design
		dict<IdString, pool<IdString>> used_instance_ports;
		pool<IdString> instantiated;
		pool<IdString> positional;
		CollectInstantiated(design, instantiated);
		bool scan_outputs = purge_mode || HasTopModule(design) || HasUniqueRoot(design, instantiated);
		if(scan_outputs)
			ScanInstances(design, used_instance_ports, positional);
		else
			log("The design has no clear top module. Outputs which are driven inside their module stay.\n");

		// Find all of the unused ports, and remove them from that module
		for(auto mod : design->selected_modules())
		{
			bool keep_outputs = !scan_outputs || !instantiated.count(mod->name) ||
					positional.count(mod->name) || mod->get_bool_attribute(ID::top);
			ScanModule(mod, removed_ports, used_instance_ports[mod->name], keep_outputs);
		}

		// Remove the unused ports from all instances of those modules
		for(auto mod : design->modules())
			CleanupModule(mod, removed_ports);
	}

	// The cell types which some cell in the design instantiates
	void CollectInstantiated(Design *design, pool<IdString> &instantiated)
	{
		for(auto mod : design->modules())
			for(auto cell : mod->cells())
				instantiated.insert(cell->type);
	}

	bool HasTopModule(Design *design)
	{
		for(auto mod : design->modules())
			if(mod->get_bool_attribute(ID::top))
				return true;
		return false;
	}

	// A design where only one module is not instantiated has a clear top even
	// when no module has the attribute
	bool HasUniqueRoot(Design *design, const pool<IdString> &instantiated)
	{
		int roots = 0;
		for(auto mod : design->modules())
			if(!instantiated.count(mod->name))
				roots++;
		return roots == 1;
	}

	// A port is used by an instance if some bit of its connection goes anywhere
	// else in the parent module: a public, port or kept wire, a second reference
	// to the same bit, or any wire at all if the parent still contains processes
	void ScanInstances(Design *design, dict<IdString, pool<IdString>> &used_instance_ports, pool<IdString> &positional)
	{
		// Count how often each wire bit is referenced anywhere in the design
		dict<SigBit, int> bit_refs;
		for(auto mod : design->modules())
		{
			for(auto &conn : mod->connections())
				for(auto bit : SigSpec{conn.first, conn.second})
					if(bit.wire != NULL)
						bit_refs[bit]++;
			for(auto cell : mod->cells())
				for(auto &conn : cell->connections())
					for(auto bit : conn.second)
						if(bit.wire != NULL)
							bit_refs[bit]++;
		}

		for(auto mod : design->modules())
		{
			bool has_procs = !mod->processes.empty();
			for(auto cell : mod->cells())
				for(auto &conn : cell->connections())
				{
					if(!conn.first.isPublic())
						positional.insert(cell->type);

					for(auto bit : conn.second)
					{
						if(bit.wire == NULL)
							continue;
						if(has_procs || bit.wire->name.isPublic() || bit.wire->port_input || bit.wire->port_output ||
								bit.wire->get_bool_attribute(ID::keep) || bit_refs.at(bit) > 1)
						{
							used_instance_ports[cell->type].insert(conn.first);
							break;
						}
					}
				}
		}
	}

	void CleanupModule(Module *module, dict<IdString, pool<IdString>> &removed_ports)
	{
		log("Removing now-unused cell ports in module %s\n", module->name);

		auto cells = module->cells();
		for(auto cell : cells)
		{
			if(removed_ports.find(cell->type) == removed_ports.end())
			{
				// log("  Not touching instance \"%s\" because we didn't remove any ports from module \"%s\"\n",
				//	cell->name.c_str(), cell->type.c_str());
				continue;
			}

			auto ports_to_remove = removed_ports[cell->type];
			for(auto p : ports_to_remove)
			{
				log("  Removing port \"%s\" from instance \"%s\"\n",
					p.c_str(), cell->type.c_str());
				cell->unsetPort(p);
			}
		}
	}

	void ScanModule(Module* module, dict<IdString, pool<IdString>> &removed_ports,
			const pool<IdString> &used_instance_ports, bool keep_outputs)
	{
		log("Finding unconnected ports in module %s\n", module->name);

		pool<IdString> used_ports;

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

				//log("  conn %s, %s\n", w1->name, w2->name);

				if( (w1->port_input || w1->port_output) && (used_ports.find(w1->name) == used_ports.end()) )
					used_ports.insert(w1->name);

				if( (w2->port_input || w2->port_output) && (used_ports.find(w2->name) == used_ports.end()) )
					used_ports.insert(w2->name);
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

					// log("  sig %s\n", sig->name);
					if( (sig->port_input || sig->port_output) && (used_ports.find(sig->name) == used_ports.end()) )
						used_ports.insert(sig->name);
				}
			}
		}

		// Now that we know what IS used, get rid of anything that isn't in that list
		pool<IdString> unused_ports;
		for(auto port : module->ports)
		{
			if(used_ports.find(port) == used_ports.end())
			{
				unused_ports.insert(port);
				continue;
			}

			// An output which no instance of this module uses can be removed
			// even if it is driven internally
			auto wire = module->wire(port);
			if(
				wire->port_output &&
				!wire->port_input &&
				!keep_outputs &&
				used_instance_ports.find(port) == used_instance_ports.end() &&
				!wire->get_bool_attribute(ID::keep)
			)
				unused_ports.insert(port);
		}

		// Print the ports out as we go through them
		for(auto port : unused_ports)
		{
			log("  removing unused port %s\n", port);
			removed_ports[module->name].insert(port);

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
