/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.
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

#include <map>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// A bus reconstructed from a group of bit-blasted 1-bit ports. Only a port bus is recorded:
// it is the module's interface changing, which every instance of the module has to follow.
struct BusGroup {
	RTLIL::IdString name;                 // name of the reconstructed bus, e.g. \key
	int width = 0;                        // one past the largest index seen, not the member count
	bool is_driven_by_cell = false;       // the bus is an output, so instances must not tie it to constants
	std::vector<RTLIL::IdString> members; // members[i] is the port that became bit i, empty if absent
};

// A connection is positional when it is named $1, $2 and so on, as the Verilog frontend
// emits before `hierarchy` maps them onto the port list.
static bool is_positional(RTLIL::IdString name) { return name[0] == '$' && '0' <= name[1] && name[1] <= '9'; }

// Substitutes individual bits according to a bit-level rewrite map.
struct BitRewriter {
	const dict<RTLIL::SigBit, RTLIL::SigBit> &rules;
	BitRewriter(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules) : rules(rules) {}
	void operator()(RTLIL::SigSpec &sig) { sig.replace(rules); }
};

struct BusRebuildPass : public Pass {
	BusRebuildPass() : Pass("bus_rebuild", "reconstruct busses from bit-blasted wires") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bus_rebuild [selection]\n");
		log("\n");
		log("This command reconstructs vectors from groups of 1-bit wires that follow the\n");
		log("bit-blasting convention <prefix>_<index>_, as emitted by netlist writers that\n");
		log("cannot represent vectors. The wires of the selected modules are grouped by\n");
		log("prefix, replaced by a single vector wire, and everything referring to the old\n");
		log("1-bit wires is repointed at the corresponding bit of the new vector.\n");
		log("\n");
		log("Both ports and internal nets are rebuilt. Internal nets matter as much as\n");
		log("ports for characterization: a cell-under-test surrounded by flops hangs off\n");
		log("the flop boundary nets rather than off the top-level ports, so those are what\n");
		log("carvenetlist turns into the carved cell's pins.\n");
		log("\n");
		log("Instances of a module whose ports were rewritten are updated in every module\n");
		log("of the design, including modules outside the selection, so that named port\n");
		log("connections keep resolving to a declared port. The per-bit connections\n");
		log(".p_0_(a), .p_1_(b) are merged into the single connection .p({b, a}).\n");
		log("\n");
		log("A group is left alone if its prefix collides with an existing wire, if a bit\n");
		log("index is claimed twice, if its members are not all 1 bit wide, if they mix\n");
		log("ports with internal nets, or if they do not agree on a direction.\n");
		log("\n");
	}

	// Split a bit-blasted wire name such as "\foo_12_" into the prefix "\foo" and the index 12.
	// Returns false if the name does not follow the convention. Indices with redundant leading
	// zeros are rejected, so that \foo_07_ and \foo_7_ can never claim the same bit.
	static bool parse_blasted_name(const std::string &name, std::string &prefix, int &index)
	{
		if (name.size() < 4 || name.back() != '_')
			return false;

		size_t sep = name.rfind('_', name.size() - 2);
		if (sep == std::string::npos || sep == 0)
			return false;

		std::string digits = name.substr(sep + 1, name.size() - sep - 2);
		if (digits.empty() || !std::all_of(digits.begin(), digits.end(), ::isdigit))
			return false;
		if (digits.size() > 1 && digits[0] == '0')
			return false;

		// The prefix must be more than the leading \ or $ of the identifier.
		if (sep < 2)
			return false;

		try {
			index = std::stoi(digits);
		} catch (const std::out_of_range &) {
			return false;
		}
		prefix = name.substr(0, sep);
		return true;
	}

	// Replace the bit-blasted wires of one module by vector wires, and return how many
	// vectors were rebuilt. Appends one BusGroup per reconstructed *port* bus so that
	// instances can be fixed up later; an internal net has no instance side to fix up.
	int rebuild_module_buses(RTLIL::Module *module, std::vector<BusGroup> &buses)
	{
		// Group the bit-blasted wires by prefix. std::map keeps the members ordered by
		// index, which matters because \p_10_ sorts before \p_2_ by name.
		std::map<std::string, std::map<int, RTLIL::Wire *>> groups;
		pool<std::string> rejected;

		for (auto wire : module->wires()) {
			// An autogenerated $-name is never a vector some writer bit-blasted
			if (wire->name[0] == '$')
				continue;

			std::string prefix;
			int index;
			if (!parse_blasted_name(wire->name.str(), prefix, index))
				continue;

			if (wire->width != 1) {
				log_warning("Not reconstructing bus %s in module %s: member %s is %d bits wide.\n", prefix.c_str(), log_id(module),
					    log_id(wire), wire->width);
				rejected.insert(prefix);
				continue;
			}

			auto &members = groups[prefix];
			if (members.count(index)) {
				log_warning("Not reconstructing bus %s in module %s: bit %d is claimed by both %s and %s.\n", prefix.c_str(),
					    log_id(module), index, log_id(members.at(index)), log_id(wire));
				rejected.insert(prefix);
				continue;
			}
			members[index] = wire;
		}

		dict<RTLIL::SigBit, RTLIL::SigBit> rules;
		pool<RTLIL::Wire *> old_wires;
		int rebuilt = 0;

		for (auto &group : groups) {
			const std::string &prefix = group.first;
			auto &members = group.second;

			if (rejected.count(prefix))
				continue;

			RTLIL::IdString bus_name(prefix);
			if (module->wire(bus_name) != nullptr) {
				log_warning("Not reconstructing bus %s in module %s: a wire of that name already exists.\n", log_id(bus_name),
					    log_id(module));
				continue;
			}

			// A group is either all ports or all internal nets. Merging the two would pull an
			// internal net into the module's interface, silently widening it.
			int nports = 0;
			for (auto &member : members)
				nports += member.second->port_input || member.second->port_output;
			if (nports != 0 && nports != GetSize(members)) {
				log_warning("Not reconstructing bus %s in module %s: %d of its %d members are ports.\n", log_id(bus_name),
					    log_id(module), nports, GetSize(members));
				continue;
			}

			// Take the direction as the union over the members. An inout port carries both
			// flags, so testing them one at a time would quietly demote it to a plain input.
			bool is_input = false, is_output = false;
			for (auto &member : members) {
				is_input |= member.second->port_input;
				is_output |= member.second->port_output;
			}
			if (is_input && is_output) {
				for (auto &member : members)
					if (!member.second->port_input || !member.second->port_output) {
						log_warning("Not reconstructing bus %s in module %s: members disagree on direction.\n",
							    log_id(bus_name), log_id(module));
						is_input = is_output = false;
						break;
					}
				if (!is_input && !is_output)
					continue;
			}

			// Size the bus from the largest index rather than the member count. A writer
			// may drop bits that ended up unconnected, and packing the survivors together
			// would silently renumber every bit above the first gap.
			int width = members.rbegin()->first + 1;

			// Keep the bus roughly where the blasted bits were in the port list.
			int port_id = 0;
			for (auto &member : members)
				if (member.second->port_id != 0 && (port_id == 0 || member.second->port_id < port_id))
					port_id = member.second->port_id;

			RTLIL::Wire *bus = module->addWire(bus_name, width);
			bus->port_input = is_input;
			bus->port_output = is_output;
			bus->port_id = port_id;
			bus->set_src_attribute(members.begin()->second->get_src_attribute());

			// A net carrying \keep is one opt_clean was told to leave alone. A port is kept by
			// virtue of being a port, but a net would quietly become removable once merged.
			for (auto &member : members)
				if (member.second->get_bool_attribute(ID::keep))
					bus->set_bool_attribute(ID::keep);

			BusGroup info;
			info.name = bus_name;
			info.width = width;
			info.is_driven_by_cell = is_output && !is_input;
			info.members.resize(width);
			for (auto &member : members) {
				rules[RTLIL::SigBit(member.second)] = RTLIL::SigBit(bus, member.first);
				info.members[member.first] = member.second->name;
				old_wires.insert(member.second);
			}
			// Only a port bus is visible to instances; an internal net has no formal to merge.
			if (nports)
				buses.push_back(info);
			rebuilt++;

			if (GetSize(members) == width)
				log_debug("  %s [%d:0]\n", log_id(bus_name), width - 1);
			else
				log_debug("  %s [%d:0], %d of %d bits absent\n", log_id(bus_name), width - 1, width - GetSize(members), width);
		}

		if (!rebuilt)
			return 0;

		// Repoint everything that referenced the old 1-bit wires at the new bus bits.
		BitRewriter rewriter(rules);
		module->rewrite_sigspecs(rewriter);

		module->remove(old_wires);
		module->fixup_ports();

		log("Reconstructed %d bus%s from %d wires in module %s.\n", rebuilt, rebuilt == 1 ? "" : "es", GetSize(old_wires), log_id(module));
		return rebuilt;
	}

	// Merge the per-bit connections on instances of rewritten modules into one connection
	// per bus, so that every formal keeps naming a port that actually exists.
	void reconnect_instances(RTLIL::Module *module, const dict<RTLIL::IdString, std::vector<BusGroup>> &rebuilt)
	{
		int reconnected = 0;

		for (auto cell : module->cells()) {
			auto it = rebuilt.find(cell->type);
			if (it == rebuilt.end())
				continue;

			for (auto &bus : it->second) {
				RTLIL::SigSpec sig;
				bool present = false;

				for (int i = 0; i < bus.width; i++) {
					RTLIL::IdString member = bus.members[i];
					if (!member.empty() && cell->hasPort(member)) {
						present = true;
						RTLIL::SigSpec actual = cell->getPort(member);
						if (GetSize(actual) == 1) {
							sig.append(actual);
							continue;
						}
						if (GetSize(actual) != 0)
							log_warning("Instance %s in module %s drives %d bits into 1-bit port %s, leaving bit %d "
								    "undriven.\n",
								    log_id(cell), log_id(module), GetSize(actual), log_id(member), i);
					}
					// A bit the instance never connected, or that the module dropped, stays undriven. An
					// output has to dangle on a fresh wire rather than a constant, which `hierarchy` rejects.
					if (bus.is_driven_by_cell)
						sig.append(module->addWire(NEW_ID2_SUFFIX(stringf("unconn_%s_%d", log_id(bus.name), i)), 1));
					else
						sig.append(RTLIL::State::Sx);
				}

				// Every member formal has to go even when none of them carried a usable bit, or the
				// instance is left naming ports that the module no longer declares.
				if (!present)
					continue;

				for (int i = 0; i < bus.width; i++)
					if (!bus.members[i].empty())
						cell->unsetPort(bus.members[i]);
				cell->setPort(bus.name, sig);
				reconnected++;
			}
		}

		if (reconnected)
			log("Reconnected %d bus port%s on instances in module %s.\n", reconnected, reconnected == 1 ? "" : "s", log_id(module));
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BUS_REBUILD pass (reconstructing busses from bit-blasted wires).\n");
		extra_args(args, 1, design);

		// Positional connections are resolved against the port list by index, so rewriting the
		// ports underneath them silently repoints every argument. Leave those modules alone.
		pool<RTLIL::IdString> instantiated_positionally;
		for (auto module : design->modules())
			for (auto cell : module->cells())
				for (auto &conn : cell->connections())
					if (is_positional(conn.first)) {
						instantiated_positionally.insert(cell->type);
						break;
					}

		dict<RTLIL::IdString, std::vector<BusGroup>> rebuilt;
		int total = 0;

		for (auto module : design->selected_modules()) {
			if (instantiated_positionally.count(module->name)) {
				log_warning("Not reconstructing busses in module %s: it is instantiated with positional "
					    "connections. Run `hierarchy` first.\n",
					    log_id(module));
				continue;
			}

			std::vector<BusGroup> buses;
			total += rebuild_module_buses(module, buses);
			if (!buses.empty())
				rebuilt[module->name] = std::move(buses);
		}

		if (!total) {
			log("No busses to reconstruct.\n");
			return;
		}

		// Only a port reaches an instance, so a run that rebuilt internal nets alone is done
		if (rebuilt.empty())
			return;

		// Instances live in the parent, which may well be outside the selection. Visiting
		// every module keeps a partial selection from leaving dangling formals behind.
		for (auto module : design->modules())
			reconnect_instances(module, rebuilt);
	}
} BusRebuildPass;

PRIVATE_NAMESPACE_END
