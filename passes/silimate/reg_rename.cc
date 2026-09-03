/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee          <stan@silimate.com>
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

#include <algorithm>

#include "kernel/fstdata.h"
#include "kernel/newcelltypes.h"
#include "kernel/yosys.h"
#include "passes/silimate/reg_rename.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Attributes used for register renaming, should be stamped beforehand based on elaborator convention.
#define RTL_OBJ_ATTR ID(rtl_obj)
#define RTL_OBJ_BIT_ATTR ID(rtl_obj_bit)
#define RTL_OBJ_WIDTH_ATTR ID(rtl_obj_width)

// One dumped signal belonging to an RTL object.
struct DumpLeaf {
	std::string name;
	std::string rel;
	int width = 0;
	int offset = 0;
};

// End-of-pass tally, so a partial binding is reported rather than passed off as complete
struct BindStats {
	int bound = 0;
	int no_stamp = 0;
	int no_object = 0;
	int no_bit = 0;
};

// Read one of the stamped integer fields.
static bool stamped_int(Cell *cell, IdString attr, int &out)
{
	if (!cell->has_attribute(attr))
		return false;
	const std::string text = cell->get_string_attribute(attr);
	if (text.empty() || text.find_first_not_of("0123456789") != std::string::npos)
		return false;
	out = std::stoi(text);
	return true;
}

static std::string first_component(const std::string &rel)
{
	if (rel.empty())
		return rel;
	size_t end = rel.find_first_of(".[", 1);
	return end == std::string::npos ? rel : rel.substr(0, end);
}

// Group leaves by their next path component, preserving declaration order.
static std::vector<std::vector<DumpLeaf>> group_children(const std::vector<DumpLeaf> &leaves)
{
	// Key lookups to avoid quadratic runtime
	dict<std::string, int> order;
	std::vector<std::vector<DumpLeaf>> groups;
	for (auto &leaf : leaves) {
		std::string head = first_component(leaf.rel);
		auto it = order.find(head);
		if (it == order.end()) {
			it = order.insert(std::make_pair(head, GetSize(groups))).first;
			groups.push_back({});
		}
		DumpLeaf child = leaf;
		child.rel = leaf.rel.substr(head.size()); // descend one level
		groups[it->second].push_back(child);
	}
	return groups;
}

// Total width of a subtree, i.e. what it spans if its members partition the parent
static int span(const std::vector<DumpLeaf> &leaves)
{
	int total = 0;
	for (auto &leaf : leaves)
		total += leaf.width;
	return total;
}

// Locate `bit` of an object that the waveform dumped as `leaves`, given the width the
// netlist says the object has.
static bool resolve(const std::vector<DumpLeaf> &leaves, int width, int bit, DumpLeaf &out,
		    int &leaf_bit)
{
	if (leaves.empty() || bit < 0 || bit >= width)
		return false;

	// A single leaf covering the whole object: the bit indexes straight into it
	if (leaves.size() == 1 && leaves[0].rel.empty()) {
		if (leaves[0].width != width)
			return false;
		out = leaves[0];
		leaf_bit = bit;
		return true;
	}

	// Several signals all named for the object itself is an ambiguous dump rather than a
	// member list, and would leave the recursion below with nothing to descend into.
	bool flat = true;
	for (auto &leaf : leaves)
		flat = flat && leaf.rel.empty();
	if (flat)
		return false;

	auto groups = group_children(leaves);
	int total = 0;
	for (auto &group : groups)
		total += span(group);

	// Struct or array: members partition the object, first declared taking the top bits
	if (total == width) {
		int high = width;
		for (auto &group : groups) {
			high -= span(group);
			if (bit >= high)
				return resolve(group, span(group), bit - high, out, leaf_bit);
		}
		return false;
	}

	// Union: every member spans the whole object, so read whichever is a plain signal
	bool overlay = !groups.empty();
	for (auto &group : groups)
		overlay = overlay && span(group) == width;
	if (overlay) {
		for (auto &group : groups)
			if (group.size() == 1 && group[0].rel.empty())
				return resolve(group, width, bit, out, leaf_bit);
		return resolve(groups.front(), width, bit, out, leaf_bit);
	}

	return false;
}

// First component of a netlist name, i.e. the RTL object before `.` or `[`
static std::string object_root(const std::string &name)
{
	size_t cut = name.find_first_of(".[");
	return cut == std::string::npos ? name : name.substr(0, cut);
}

// Strip a trailing bit range and report the declared lsb. A range written with no space
// before it is a packed dimension (SHM's "deep_out[1:0]"), not a bit range, but either way
// the dumped width is authoritative and the name without it is the signal.
static std::string split_bit_range(const std::string &name, int &offset)
{
	offset = 0;
	if (name.empty() || name.back() != ']')
		return name;
	size_t open = name.rfind('[');
	if (open == std::string::npos)
		return name;
	std::string inner = name.substr(open + 1, name.size() - open - 2);
	if (inner.empty() || inner.find(':') == std::string::npos ||
			inner.find_first_not_of("0123456789:") != std::string::npos)
		return name;
	size_t colon = inner.find(':');
	offset = std::min(std::stoi(inner.substr(0, colon)), std::stoi(inner.substr(colon + 1)));
	return name.substr(0, open);
}

struct RegRenameInstance {
	std::string vcd_scope;
	Module *module;
	bool debug;
	dict<Cell*, RegRenameInstance *> children;

	// Constructor
	// When constructing, it will recursively build the
	// module hierarchy with correct VCD scope mapping
	RegRenameInstance(std::string scope, Module *mod, bool dbg = false)
		: vcd_scope(scope), module(mod), debug(dbg)
	{
		// Loop through all cells in the module
		for (auto cell : module->cells()) {
			Module *child = module->design->module(cell->type);
			if (child == nullptr) {
				continue; // skip non-module cells
			}
			// Construct the child's scope in VCD format,
			// which is the parent scope plus the instance name
			std::string child_scope = vcd_scope + "." + RTLIL::unescape_id(cell->name);
			children[cell] = new RegRenameInstance(child_scope, child, debug);
		}
	}

	// Destructor
	~RegRenameInstance()
	{
		for (auto &it : children)
			delete it.second;
	}

	// Every module scope in the hierarchy, used to tell instance path from object path
	void collect_scopes(pool<std::string> &scopes)
	{
		scopes.insert(vcd_scope);
		for (auto &it : children)
			it.second->collect_scopes(scopes);
	}

	// The wire the dump expects, created at the dumped width when synthesis split the object.
	Wire *dump_wire(dict<IdString, Wire *> &cache, const DumpLeaf &leaf, const std::string &dump_path)
	{
		IdString id = RTLIL::escape_id(leaf.name);
		Wire *&wire = cache[id];
		if (!wire) {
			wire = module->wire(id);
			if (!wire) {
				if (debug)
					log("Creating wire %s[%d:%d] in scope %s\n", leaf.name.c_str(),
							leaf.offset + leaf.width - 1, leaf.offset, vcd_scope.c_str());
				wire = module->addWire(id, leaf.width);
				wire->start_offset = leaf.offset;
			}
		}
		// Dump lives in another scope, which sim will resolve through sim_src attribute
		if (!dump_path.empty())
			wire->set_string_attribute(ID(sim_src), dump_path);
		return wire;
	}

	// Move every flop collected above onto its renamed wire in one pass over the module
	void commit(const dict<SigBit, SigBit> &bit_map, const pool<SigBit> &claimed,
		    const std::vector<std::pair<SigBit, SigBit>> &aliases, const pool<Wire *> &drop)
	{
		auto rewriter = [&](SigSpec &sig) {
			for (int i = 0; i < GetSize(sig); i++) {
				auto it = bit_map.find(sig[i]);
				if (it != bit_map.end())
					sig.replace(i, SigSpec(it->second));
			}
		};
		if (!bit_map.empty())
			module->rewrite_sigspecs(rewriter);
		module->remove(drop);

		// Alias/opt left assigns (often to X) on bits the flops now own; rebuild the
		// connection list without them, keeping any unclaimed slice of each assign.
		if (!claimed.empty()) {
			std::vector<RTLIL::SigSig> kept;
			bool changed = false;
			for (auto &conn : module->connections()) {
				RTLIL::SigSpec lhs, rhs; // lhs = driven, rhs = driver
				for (int i = 0; i < GetSize(conn.first); i++) {
					if (claimed.count(conn.first[i])) {
						changed = true;
						continue;
					}
					lhs.append(conn.first[i]);
					rhs.append(conn.second[i]);
				}
				if (GetSize(lhs))
					kept.emplace_back(lhs, rhs);
			}
			if (changed)
				module->new_connections(kept);
		}

		// Added last: the rewrite above would otherwise turn these into self-assigns.
		for (auto &alias : aliases)
			module->connect(alias.first, alias.second);
	}

	// Rename each flop's Q wire to the signal the waveform dumped it under.
	void process_registers(const dict<std::string, std::vector<DumpLeaf>> &objects,
			       BindStats &stats)
	{
		if (debug)
			log("Processing registers in scope: %s (module: %s)\n", vcd_scope.c_str(),
					log_id(module->name));
		else
			log("Processing registers in %s\n", log_id(module->name));

		dict<SigBit, SigBit> bit_map; // old flop bit -> bit of the renamed wire
		pool<SigBit> claimed_bits;
		std::vector<std::pair<SigBit, SigBit>> port_aliases; // output bits to re-drive
		dict<IdString, Wire *> target_wires;
		pool<Wire *> drop_wires;

		for (auto cell : module->cells()) {
			if (!StaticCellTypes::categories.is_ff(cell->type))
				continue;

			// Which RTL object bit this flop holds, stamped before optimization
			int obj_bit = 0, obj_width = 0;
			if (!cell->has_attribute(RTL_OBJ_ATTR) || !stamped_int(cell, RTL_OBJ_BIT_ATTR, obj_bit) ||
					!stamped_int(cell, RTL_OBJ_WIDTH_ATTR, obj_width)) {
				log_warning("Cell %s in scope %s has no usable RTL bind stamp\n",
						log_id(cell->name), vcd_scope.c_str());
				stats.no_stamp++;
				continue;
			}
			std::string obj = cell->get_string_attribute(RTL_OBJ_ATTR);

			for (auto &conn : cell->connections()) {
				if (conn.first != ID::Q || !conn.second.is_chunk())
					continue;

				// A field of a split struct port drives a slice of a wider wire, so take the
				// flop's own bits rather than assuming it owns all of old_wire.
				SigChunk qbits = conn.second.as_chunk();
				Wire *old_wire = qbits.wire;
				if (!old_wire || old_wire->port_input)
					continue;

				// Locate obj[obj_bit] among the signals the waveform dumped for it
				auto obj_it = objects.find(vcd_scope + "." + obj);
				DumpLeaf leaf;
				int leaf_bit = 0;
				std::string dump_path;
				bool placed = obj_it != objects.end() &&
						resolve(obj_it->second, obj_width, obj_bit, leaf, leaf_bit);

				// A flattened interface pin is dumped under the parent's actual, so it is not
				// in this scope's object map. bind_interface_ports already put that path on the
				// pin, so rename onto the pin itself and let sim_src do the lookup.
				Wire *pin = placed ? nullptr : module->wire(RTLIL::escape_id(obj));
				if (pin && pin->has_attribute(ID(sim_src)) && GetSize(pin) == obj_width &&
						obj_bit >= 0 && obj_bit < obj_width) {
					dump_path = pin->get_string_attribute(ID(sim_src));
					leaf = {obj, "", GetSize(pin), pin->start_offset};
					leaf_bit = obj_bit;
					placed = true;
				}

				if (!placed) {
					if (obj_it == objects.end()) {
						log_warning("Object %s of cell %s is not in the waveform, scope %s\n",
								obj.c_str(), log_id(cell->name), vcd_scope.c_str());
						stats.no_object++;
					} else {
						log_warning("Cannot place bit %d of %d-bit object %s, dumped as %d "
								"signal(s), for cell %s in scope %s\n", obj_bit, obj_width,
								obj.c_str(), GetSize(obj_it->second), log_id(cell->name),
								vcd_scope.c_str());
						stats.no_bit++;
					}
					continue;
				}

				// The flop must fit inside the single dumped element it landed in
				if (leaf_bit < 0 || leaf_bit + qbits.width > leaf.width) {
					log_warning("Bit index %d is invalid for wire indices [%d:%d] for '%s'\n",
							leaf.offset + leaf_bit, leaf.offset + leaf.width - 1, leaf.offset,
							leaf.name.c_str());
					stats.no_bit++;
					continue;
				}

				Wire *target = dump_wire(target_wires, leaf, dump_path);
				if (target == old_wire)
					continue; // already the wire the dump expects

				// Multiple-driver guard: another flop may have claimed these bits
				bool taken = false;
				for (int i = 0; i < qbits.width && !taken; i++)
					taken = claimed_bits.count(SigBit(target, leaf_bit + i));
				if (taken) {
					log_warning("Skipping cell %s: target %s[%d] already driven by another cell\n",
							log_id(cell->name), leaf.name.c_str(), leaf.offset + leaf_bit);
					continue;
				}

				if (debug)
					log("Connecting %s (%s[%d]) to %s[%d]\n", log_id(old_wire), obj.c_str(),
							obj_bit, leaf.name.c_str(), leaf.offset + leaf_bit);

				for (int i = 0; i < qbits.width; i++) {
					SigBit old(old_wire, qbits.offset + i);
					SigBit renamed(target, leaf_bit + i);
					bit_map[old] = renamed;
					claimed_bits.insert(renamed);
					// Moving the flop off an output port leaves it undriven; alias it back.
					if (old_wire->port_output)
						port_aliases.emplace_back(old, renamed);
				}
				// Drop the old wire only when the flop drove all of it and nothing else can.
				if (qbits.width == GetSize(old_wire) && !old_wire->port_id)
					drop_wires.insert(old_wire);
				stats.bound++;
			}
		}

		commit(bit_map, claimed_bits, port_aliases, drop_wires);
	}

	// Handle SV interface ports.
	void bind_interface_ports(FstData &fst)
	{
		for (auto &it : children) {
			Cell *cell = it.first;
			RegRenameInstance *child = it.second;
			for (auto wire : child->module->wires()) {
				if (!wire->get_bool_attribute(ID(interface_port)) || !cell->hasPort(wire->name))
					continue;
				SigSpec sig = cell->getPort(wire->name);
				// Parent ties the pin off; the cut removes that driver, so carry the value.
				if (sig.is_fully_const()) {
					wire->set_string_attribute(ID(sim_const), sig.as_const().as_string());
					continue;
				}
				if (!sig.is_wire())
					continue; // slices/concats span more than one dumped signal
				Wire *actual = sig.as_wire();

				// A passthrough pin's parent may itself be tied off, which only the level
				// above could see, so carry that value one more hop.
				if (actual->has_attribute(ID(sim_const))) {
					wire->set_string_attribute(ID(sim_const),
							actual->get_string_attribute(ID(sim_const)));
					continue;
				}
				std::string src = actual->has_attribute(ID(sim_src))
					? actual->get_string_attribute(ID(sim_src))
					: vcd_scope + "." + RTLIL::unescape_id(actual->name);
				fstHandle id = fst.getHandle(src);
				if (!id || fst.getWidth(id) != GetSize(wire))
					continue;
				wire->set_string_attribute(ID(sim_src), src);
				if (debug)
					log("Interface port %s.%s resolved to %s\n", child->vcd_scope.c_str(),
							RTLIL::unescape_id(wire->name).c_str(), src.c_str());
			}
			child->bind_interface_ports(fst);
		}
	}

	// Handle packed inputs.
	void bind_packed_inputs(const dict<std::string, std::vector<DumpLeaf>> &objects, FstData &fst)
	{
		// Split input ports whose dump is one packed vector
		dict<std::string, std::vector<std::tuple<int, int, Wire*>>> groups;
		int order = 0;
		for (auto wire : module->wires()) {
			if (!wire->port_input || wire->get_bool_attribute(ID(interface_port)))
				continue;
			std::string name = RTLIL::unescape_id(wire->name);
			std::string root = object_root(name);
			if (root == name)
				continue; // dumped under the same name as the port
			groups[root].emplace_back(wire->port_id ? wire->port_id : (1 << 30), order++, wire);
		}
		for (auto &kv : groups) {
			auto members = kv.second;
			std::sort(members.begin(), members.end());
			int total = 0;
			for (auto &m : members)
				total += GetSize(std::get<2>(m));
			auto obj_it = objects.find(vcd_scope + "." + kv.first);
			if (obj_it == objects.end())
				continue;
			int high = total;
			for (auto &m : members) {
				Wire *wire = std::get<2>(m);
				high -= GetSize(wire);
				DumpLeaf leaf;
				int leaf_bit = 0;
				if (!resolve(obj_it->second, total, high, leaf, leaf_bit))
					continue;
				std::string dump_path = leaf.name;
				if (dump_path.compare(0, vcd_scope.size(), vcd_scope) != 0)
					dump_path = vcd_scope + "." + dump_path;
				if (!fst.getHandle(dump_path))
					continue;
				wire->set_string_attribute(ID(sim_src), dump_path);
				if (leaf.width != GetSize(wire))
					wire->set_string_attribute(ID(sim_src_bit), std::to_string(leaf_bit));
				if (debug)
					log("Packed input %s.%s resolved to %s[%d]\n", vcd_scope.c_str(),
							log_id(wire), dump_path.c_str(), leaf_bit);
			}
		}
	}

	void process_all(const dict<std::string, std::vector<DumpLeaf>> &objects,
			 BindStats &stats, FstData &fst)
	{
		bind_packed_inputs(objects, fst);
		process_registers(objects, stats);
		for (auto &it : children)
			it.second->process_all(objects, stats, fst);
	}
};

// Group every dumped signal under the RTL object it belongs to.
static dict<std::string, std::vector<DumpLeaf>> collect_objects(FstData &fst,
								const pool<std::string> &scopes,
								bool debug)
{
	dict<std::string, std::vector<DumpLeaf>> objects;
	pool<std::string> seen; // dumpers may open the same scope twice and repeat declarations
	for (auto &var : fst.getVars()) {
		int offset = 0;
		std::string name = split_bit_range(RTLIL::unescape_id(var.name), offset);
		std::string full = var.scope.empty() ? name : var.scope + "." + name;

		// Longest enclosing module scope: the rest is the object and its member path
		std::string scope = var.scope;
		while (!scope.empty() && !scopes.count(scope)) {
			size_t dot = scope.find_last_of('.');
			scope = dot == std::string::npos ? "" : scope.substr(0, dot);
		}
		if (scope.empty() && !scopes.count(scope))
			continue; // outside the hierarchy being processed

		std::string rel = full.substr(scope.empty() ? 0 : scope.size() + 1);
		size_t split = rel.find_first_of(".[");
		std::string root = split == std::string::npos ? rel : rel.substr(0, split);

		// A repeat of a name already seen is the same signal again, not another member
		if (!seen.insert(full).second)
			continue;

		DumpLeaf leaf;
		leaf.name = rel;
		leaf.rel = split == std::string::npos ? "" : rel.substr(split);
		leaf.width = var.width;
		leaf.offset = offset;
		objects[scope + "." + root].push_back(leaf);
		if (debug)
			log("Dumped %s.%s as %s (width %d, lsb %d)\n", scope.c_str(), root.c_str(),
				leaf.rel.empty() ? "one flat signal" : leaf.rel.c_str(), leaf.width, offset);
	}
	return objects;
}

struct RegRenamePass : public Pass {
	RegRenamePass()
	    : Pass("reg_rename", "renames register output wires to the correct "
				"register name and creates new wires for multi-bit registers for "
				"correct VCD register annotations.")
	{
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    reg_rename [options]\n");
		log("\n");
		log("    -waveform <filename>\n");
		log("        waveform file (VCD or FST) to extract original register widths from.\n");
		log("        VCD inputs are converted via the external vcd2fst tool.\n");
		log("    -scope <scope>\n");
		log("        scope to process in the waveform\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		// Argument parsing
		std::string waveform_filename;
		std::string scope;
		bool debug = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-waveform" && argidx + 1 < args.size()) {
				waveform_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-scope" && argidx + 1 < args.size()) {
				scope = normalize_scope(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-d") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Extract top module
		Module *topmod = design->top_module();
		if (!topmod)
			log_error("No top module found!\n");

		if (waveform_filename.empty())
			log_error("No waveform file provided. Use -waveform option.\n");

		log("Reading waveform file: %s\n", waveform_filename.c_str());
		try {
			FstData fst(waveform_filename);
			if (scope.empty()) {
				scope = fst.autoScope(topmod);
				if (scope.empty())
					log_error("No scope found for module '%s'. Please specify -scope explicitly.\n",
						RTLIL::unescape_id(topmod->name).c_str());
			}
			log("Using scope: \"%s\"\n", scope.c_str());

			log("Building hierarchy from scope: %s\n", scope.c_str());
			RegRenameInstance root(scope, topmod, debug);

			// Module scopes first, so a dumped name can be split into instance path and object
			pool<std::string> scopes;
			root.collect_scopes(scopes);
			auto objects = collect_objects(fst, scopes, debug);
			log("Extracted %d RTL object(s) from waveform\n", GetSize(objects));

			root.bind_interface_ports(fst);
			BindStats stats;
			root.process_all(objects, stats, fst);
			log("Bound %d flop(s); unstamped %d, object absent %d, bit unplaced %d\n",
				stats.bound, stats.no_stamp, stats.no_object, stats.no_bit);
		} catch (const std::exception &e) {
			log_error("Failed to read waveform file '%s': %s\n", 
				waveform_filename.c_str(), e.what());
		}

		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
