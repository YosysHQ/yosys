/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Akash Levy <akash@silimate.com>
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

#include "kernel/celltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BoundaryConeWorker {
	Module *child, *parent;
	Cell *instance;
	SigMap child_sigmap;
	int max_cells;

	dict<SigBit, Cell*> bit_driver;
	dict<SigBit, SigBit> input_map;
	dict<SigBit, SigBit> copied_bits;
	dict<Cell*, Cell*> copied_cells;
	std::vector<Wire*> created_wires;
	std::vector<Cell*> created_cells;
	pool<Cell*> active_cells;
	int copied_cell_count = 0;
	bool failed = false;

	BoundaryConeWorker(Module *child, Module *parent, Cell *instance, int max_cells)
		: child(child), parent(parent), instance(instance), child_sigmap(child), max_cells(max_cells)
	{
		for (auto wire : child->wires()) {
			if (!wire->port_input || wire->port_output)
				continue;
			if (!instance->connections_.count(wire->name))
				continue;
			SigSpec conn = instance->connections_.at(wire->name);
			for (int i = 0; i < wire->width; i++)
				input_map[child_sigmap(SigBit(wire, i))] = conn[i];
		}

		for (auto cell : child->cells()) {
			if (!yosys_celltypes.cell_evaluable(cell->type) || cell->has_keep_attr())
				continue;
			for (auto &conn : cell->connections()) {
				if (!yosys_celltypes.cell_output(cell->type, conn.first))
					continue;
				for (auto bit : conn.second)
					if (bit.is_wire())
						bit_driver[child_sigmap(bit)] = cell;
			}
		}
	}

	SigSpec materialize(SigSpec sig)
	{
		SigSpec result;
		for (auto bit : sig)
			result.append(materialize(bit));
		return result;
	}

	SigBit materialize(SigBit bit)
	{
		bit = child_sigmap(bit);

		if (!bit.is_wire())
			return bit;

		if (input_map.count(bit))
			return input_map.at(bit);

		if (copied_bits.count(bit))
			return copied_bits.at(bit);

		if (!bit_driver.count(bit)) {
			failed = true;
			return RTLIL::Sx;
		}

		Cell *driver = bit_driver.at(bit);
		if (active_cells.count(driver) || copied_cell_count >= max_cells) {
			failed = true;
			return RTLIL::Sx;
		}

		copy_driver(driver);
		if (failed || !copied_bits.count(bit)) {
			failed = true;
			return RTLIL::Sx;
		}
		return copied_bits.at(bit);
	}

	void copy_driver(Cell *driver)
	{
		if (copied_cells.count(driver))
			return;

		active_cells.insert(driver);
		dict<IdString, SigSpec> new_connections;

		for (auto &conn : driver->connections()) {
			if (yosys_celltypes.cell_input(driver->type, conn.first)) {
				SigSpec mapped = materialize(conn.second);
				if (failed)
					break;
				new_connections[conn.first] = mapped;
				continue;
			}

			if (yosys_celltypes.cell_output(driver->type, conn.first)) {
				Wire *wire = parent->addWire(NEW_ID_SUFFIX("opt_boundary"), GetSize(conn.second));
				created_wires.push_back(wire);
				SigSpec mapped = wire;
				new_connections[conn.first] = mapped;
				for (int i = 0; i < GetSize(conn.second); i++) {
					if (conn.second[i].is_wire())
						copied_bits[child_sigmap(conn.second[i])] = mapped[i];
				}
				continue;
			}

			failed = true;
			break;
		}

		if (!failed && copied_cell_count >= max_cells)
			failed = true;

		if (!failed) {
			Cell *copy = parent->addCell(NEW_ID_SUFFIX("opt_boundary"), driver);
			for (auto &conn : new_connections)
				copy->setPort(conn.first, conn.second);
			copied_cells[driver] = copy;
			created_cells.push_back(copy);
			copied_cell_count++;
		}

		active_cells.erase(driver);
	}

	void rollback()
	{
		for (auto it = created_cells.rbegin(); it != created_cells.rend(); ++it)
			parent->remove(*it);
		for (auto it = created_wires.rbegin(); it != created_wires.rend(); ++it)
			parent->remove(pool<Wire*>{*it});
		created_cells.clear();
		created_wires.clear();
		copied_cells.clear();
		copied_bits.clear();
		copied_cell_count = 0;
	}
};

static bool protected_module(Module *module)
{
	return module->get_blackbox_attribute() ||
			module->get_bool_attribute(ID::keep) ||
			module->get_bool_attribute(ID::keep_hierarchy);
}

struct OptBoundaryPass : Pass {
	OptBoundaryPass() : Pass("opt_boundary", "perform conservative parent-side cross-boundary cone optimization") {}

	void help() override
	{
		log("\n");
		log("    opt_boundary [options] [selection]\n");
		log("\n");
		log("This pass performs a conservative form of hierarchical boundary optimization.\n");
		log("For each selected parent module, it looks through instances of non-blackbox,\n");
		log("non-keep child modules and copies small evaluable combinational cones that\n");
		log("drive child output ports into the parent.  The original child module body is\n");
		log("left unchanged; optimized instance outputs are disconnected only after an\n");
		log("equivalent parent-side cone has been created.\n");
		log("\n");
		log("    -max_cells <N>\n");
		log("        maximum number of child cells to copy for one output bit. Default: 8.\n");
		log("\n");
		log("    -no_disconnect\n");
		log("        copy eligible cones into the parent but leave instance output ports\n");
		log("        connected to their original nets.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_BOUNDARY pass.\n");

		int max_cells = 8;
		bool no_disconnect = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_cells" && argidx + 1 < args.size()) {
				max_cells = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-no_disconnect") {
				no_disconnect = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (max_cells < 1)
			log_cmd_error("The -max_cells value must be positive.\n");

		bool did_something = false;
		for (auto parent : design->selected_modules(RTLIL::SELECT_WHOLE_ONLY, RTLIL::SB_UNBOXED_CMDERR)) {
			if (protected_module(parent))
				continue;

			for (auto instance : parent->cells().to_vector()) {
				if (instance->has_keep_attr())
					continue;

				Module *child = design->module(instance->type);
				if (child == nullptr || protected_module(child))
					continue;

				for (auto &conn : instance->connections_) {
					Wire *port = child->wire(conn.first);
					if (port == nullptr || !port->port_output || port->port_input)
						continue;
					if (port->width != GetSize(conn.second))
						log_error("Port %s connected on instance %s not found in module %s or width is not matching\n",
								log_id(conn.first), log_id(instance), log_id(child));

					SigSpec new_conn = conn.second;
					bool changed_port = false;
					for (int i = 0; i < port->width; i++) {
						if (!conn.second[i].is_wire())
							continue;

						BoundaryConeWorker worker(child, parent, instance, max_cells);
						SigBit replacement = worker.materialize(SigBit(port, i));
						if (worker.failed) {
							worker.rollback();
							continue;
						}
						if (replacement == conn.second[i]) {
							worker.rollback();
							continue;
						}

						if (!no_disconnect) {
							parent->connect(conn.second[i], replacement);
							Wire *dummy = parent->addWire(NEW_ID_SUFFIX("opt_boundary_output"));
							new_conn[i] = SigBit(dummy, 0);
							changed_port = true;
						}
						did_something = true;

						if (worker.copied_cell_count > 0)
							log("Copied %d cells from cone driving %s[%d] of instance '%s' (type '%s') into '%s'\n",
									worker.copied_cell_count, log_id(port), i, log_id(instance), log_id(instance->type), log_id(parent));
						else
							log("Bypassed cone driving %s[%d] of instance '%s' (type '%s') in '%s'\n",
									log_id(port), i, log_id(instance), log_id(instance->type), log_id(parent));
					}

					if (changed_port)
						conn.second = new_conn;
				}
			}
		}

		if (did_something)
			design->scratchpad_set_bool("opt.did_something", true);
	}
} OptBoundaryPass;

PRIVATE_NAMESPACE_END
