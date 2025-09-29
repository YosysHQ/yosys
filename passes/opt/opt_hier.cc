/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C)  Martin Povišer <povik@cutebit.org>
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
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Used to propagate information out of a module
struct ModuleIndex {
	Module *module;
	SigMap sigmap;
	SigPool used;
	dict<SigBit, SigBit> constant_outputs;
	std::vector<SigSpec> tie_together_outputs;

	ModuleIndex(Module *module)
		: module(module), sigmap(module)
	{
		if (module->get_blackbox_attribute()) {
			for (auto wire : module->wires()) {
				for (auto bit : SigSpec(wire))
					used.add(sigmap(bit));
			}
			return;
		}

		auto count_usage = [&](const SigSpec &signal) {
			for (auto bit : signal)
				used.add(sigmap(bit));
		};
		for (auto wire : module->wires()) {
			if (wire->port_output) {
				SigSpec wire1 = wire;
				count_usage(wire1);
			}
		}
		for (auto [_, process] : module->processes)
			process->rewrite_sigspecs(count_usage);
		for (auto cell : module->cells()) {
			bool known = cell->known();
			for (auto &conn : cell->connections()) {
				if (!known || cell->input(conn.first))
					count_usage(conn.second);
			}
		}


		dict<SigBit, SigSpec> classes;
		for (auto &pair : module->connections_) {
			for (int i = 0; i < pair.first.size(); i++) {
				if (pair.first[i].wire
						&& pair.first[i].wire->port_output
						&& !pair.first[i].wire->port_input) {
					if (!pair.second[i].wire) {
						constant_outputs[pair.first[i]] = pair.second[i];
					} else {
						classes[pair.second[i]].append(pair.first[i]);
					}
				}	
			}
		}

		for (auto [key, new_class] : classes) {
			if (new_class.size() > 1) {
				new_class.sort_and_unify();
				tie_together_outputs.push_back(new_class);
			}
		}
	}

	bool apply_changes(ModuleIndex &parent, Cell *instantiation) {
		log_assert(instantiation->module == parent.module);

		if (module->get_blackbox_attribute()) {
			// no propagating out of blackboxes
			return false;
		}

		bool changed = false;
		for (auto &[port_name, value] : instantiation->connections_) {
			Wire *port = module->wire(port_name);
			if (!port || (!port->port_input && !port->port_output) || port->width != value.size()) {
				log_error("Port %s connected on instance %s not found in module %s"
						  " or width is not matching\n",
						  log_id(port_name), log_id(instantiation), log_id(module));
			}

			if (port->port_input && port->port_output) {
				// ignore bidirectional: hard to come up with sound handling
				continue;
			}

			int nunused = 0, nconstants = 0;
			// disconnect unused inputs
			if (port->port_input) {
				for (int i = 0; i < port->width; i++) {
					if (value[i].is_wire() && !used.check(sigmap(SigBit(port, i)))) {
						value[i] = RTLIL::Sx;
						nunused++;
					}
				}
			}

			// propagate constants
			if (port->port_output) {
				SigSpec port_new_const;

				for (int i = 0; i < port->width; i++) {
					SigBit port_bit(port, i);
					if (value[i].is_wire() && constant_outputs.count(port_bit) && parent.used.check(value[i])) {
						port_new_const.append(port_bit);
						nconstants++;
					}
				}

				for (auto chunk : port_new_const.chunks()) {
					RTLIL::SigSpec rhs = chunk;
					rhs.replace(constant_outputs);
					log_assert(rhs.is_fully_const());
					parent.module->connect(value.extract(chunk.offset, chunk.width), rhs);
					SigSpec dummy = parent.module->addWire(NEW_ID_SUFFIX("const_output"), chunk.width);
					for (int i = 0; i < chunk.width; i++)
						value[chunk.offset + i] = dummy[i];
				}
			}

			if (nunused > 0) {
				log("Disconnected %d input bits of instance '%s' (type '%s') in '%s'\n",
					nunused, log_id(instantiation), log_id(instantiation->type), log_id(parent.module));
				changed = true;
			}
			if (nconstants > 0) {
				log("Substituting constant for %d output bits of instance '%s' (type '%s') in '%s'\n",
					nconstants, log_id(instantiation), log_id(instantiation->type), log_id(parent.module));
				changed = true;
			}
		}

		// propagate tie-togethers
		int ntie_togethers = 0;
		SigSpec severed_port_bits;
		for (auto class_ : tie_together_outputs) {
			// filtered class represented by bits on the two sides of boundary
			SigSpec new_tie;

			for (auto port_bit : class_) {
				if (instantiation->connections_.count(port_bit.wire->name)) {
					SigBit bit = instantiation->connections_.at(port_bit.wire->name)[port_bit.offset];
					if (parent.used.check(bit)) {
						if (!new_tie.empty()) {
							severed_port_bits.append(port_bit);
							ntie_togethers++;
						}
						new_tie.append(bit);
					}
				}
			}

			if (new_tie.size() > 1)
				parent.module->connect(new_tie.extract_end(1), SigSpec(new_tie[0]).repeat(new_tie.size() - 1));
		}

		severed_port_bits.sort_and_unify();
		for (auto chunk : severed_port_bits.chunks()) {
			SigSpec &value = instantiation->connections_.at(chunk.wire->name);
			SigSpec dummy = parent.module->addWire(NEW_ID_SUFFIX("tie_together"), chunk.width);
			for (int i = 0; i < chunk.width; i++)
				value[chunk.offset + i] = dummy[i];
		}

		if (ntie_togethers > 0) {
			log("Replacing %d output bits with tie-togethers on instance '%s' of '%s' in '%s'\n",
				ntie_togethers, log_id(instantiation), log_id(instantiation->type), log_id(parent.module));
			changed = true;
		}

		return changed;
	}
};

// Used to propagate information into a module
struct UsageData {
	Module *module;
	SigPool used_outputs;
	// Values are constant nets. We're not using `dict<SigBit, State>`
	// since we want to use this with `SigSpec::replace()`
	dict<SigBit, SigBit> constant_inputs;
	std::vector<SigSpec> tie_together_inputs;

	SigSpec all_inputs;
	SigSpec all_outputs;

	UsageData(Module *module)
		: module(module)
	{
		SigSpec all_inputs;

		for (auto port_name : module->ports) {
			Wire *port = module->wire(port_name);
			log_assert(port);
			
			if (port->port_input && port->port_output) {
				// ignore bidirectional: hard to come up with sound handling
				continue;
			}

			if (port->port_input) {
				for (int i = 0; i < port->width; i++) {
					constant_inputs[SigBit(port, i)] = RTLIL::Sx;
				}
				all_inputs.append(port);
			} else {
				all_outputs.append(port);
			}
		}

		tie_together_inputs.push_back(all_inputs);
	}

	void refine_used_outputs(Wire *port, SigSpec connection, ModuleIndex &index) {
		for (int i = 0; i < port->width; i++) {
			if (connection[i].is_wire() && index.used.check(index.sigmap(connection[i]))) {
				used_outputs.add(SigBit(port, i));
			}
		}
	}

	void refine_input_constants(Wire *port, SigSpec connection) {
		for (int i = 0; i < port->width; i++) {
			SigBit port_bit(port, i);
			// is connnected constant incompatible with candidate constant?
			if (connection[i] != RTLIL::Sx
					&& constant_inputs.count(port_bit)
					&& constant_inputs.at(port_bit) != connection[i]) {
				// we can go Sx -> S1/S0, otherwise erase the candidate constant
				if (constant_inputs.at(port_bit) == RTLIL::Sx && !connection[i].is_wire()) {
					constant_inputs[port_bit] = connection[i];
				} else {
					constant_inputs.erase(port_bit);
				}
			}
		}
	}

	void refine_tie_togethers(const dict<SigBit, SigBit> &inputs) {
		std::vector<SigSpec> new_tie_togethers;

		for (auto &class_ : tie_together_inputs) {
			dict<SigBit, SigSpec> new_classes;

			for (auto bit : class_) {
				SigBit connected_bit = inputs.count(bit) ? inputs.at(bit) : RTLIL::Sx;
				new_classes[connected_bit].append(bit);
			}

			for (auto [key, new_class] : new_classes) {
				if (new_class.size() > 1)
					new_tie_togethers.push_back(new_class);
			}
		}

		new_tie_togethers.swap(tie_together_inputs);
	}

	// inspect the given instantiation and refine usage data accordingly
	void refine(Cell *instance, ModuleIndex &index) {
		dict<SigBit, SigBit> inputs;

		for (auto &[port_name, value] : instance->connections_) {
			Wire *port = module->wire(port_name);
			if (!port || (!port->port_input && !port->port_output) || port->width != value.size()) {
				log_error("Port %s connected on instance %s not found in module %s"
						  " or width is not matching\n",
						  log_id(port_name), log_id(instance), log_id(module));
			}

			if (port->port_input && port->port_output) {
				// ignore bidirectional: hard to come up with sound handling
				continue;
			}

			if (port->port_output) {
				refine_used_outputs(port, value, index);
			} else {
				refine_input_constants(port, value);
				for (int i = 0; i < port->width; i++)
					inputs[SigBit(port, i)] = value[i];
			}
		}

		refine_tie_togethers(inputs);
	}

	bool apply_changes(ModuleIndex &index) {
		bool did_something = false;

		if (module->get_blackbox_attribute()) {
			// no propagating into blackboxes
			return false;
		}

		// Disconnect unused outputs
		for (auto &pair : module->connections_) {
			for (int i = 0; i < pair.first.size(); i++) {
				// If an output is constant there's no benefit to disconnecting
				// so consider it "used"
				if (pair.first[i].wire
						&& pair.first[i].wire->port_output
						&& !pair.second[i].wire)
					used_outputs.add(pair.first[i]);
			}
		}

		SigSpec disconnect_outputs;
		for (auto bit : all_outputs) {
			if (!used_outputs.check(bit))
				disconnect_outputs.append(bit);
		}

		dict<SigBit, SigBit> replacement_map;
		for (auto chunk : disconnect_outputs.chunks()) {
			Wire *repl_wire = module->addWire(module->uniquify(std::string("$") + chunk.wire->name.str()), chunk.size());
			for (int i = 0; i < repl_wire->width; i++)
				replacement_map[SigSpec(chunk)[i]] = SigBit(repl_wire, i);
		}
		auto disconnect_rewrite = [&](SigSpec &signal) {
			signal.replace(replacement_map);
		};
		module->rewrite_sigspecs(disconnect_rewrite);
		for (auto chunk : disconnect_outputs.chunks()) {
			log("Disconnected unused output terminal '%s' in module '%s'\n", log_signal(chunk), log_id(module));
			did_something = true;
			module->connect(chunk, SigSpec(RTLIL::Sx, chunk.size()));
		}

		// Connect constant inputs
		SigPool applied_constants;
		auto constant_rewrite = [&](SigSpec &signal) {
			for (auto bit : signal) {
				if (constant_inputs.count(bit))
					applied_constants.add(bit);
			}
			signal.replace(constant_inputs);
		};
		module->rewrite_sigspecs(constant_rewrite);
		SigSpec applied_constants2 = applied_constants.export_all();
		applied_constants2.sort_and_unify();
		for (auto chunk : applied_constants2.chunks()) {
			SigSpec const_ = chunk;
			const_.replace(constant_inputs);
			log("Substituting constant %s for input terminal '%s' in module '%s'\n",
				log_signal(const_), log_signal(chunk), log_id(module));
		}

		// Propagate tied-together inputs
		dict<SigBit, SigBit> ties;
		for (auto group : tie_together_inputs) {
			// Only consider used inputs for a tie-together group.
			// ModuleIndex::apply_changes might have disconnected
			// unused inputs.
			SigSpec filtered_group;
			for (auto bit : group) {
				if (index.used.check(bit))
					filtered_group.append(bit);
			}
			for (int i = 1; i < filtered_group.size(); i++)
				ties[filtered_group[i]] = filtered_group[0];
		}
		SigPool applied_ties;
		auto ties_rewrite = [&](SigSpec &signal) {
			for (auto bit : signal) {
				if (ties.count(bit)) {
					applied_ties.add(bit);
				}
			}
			signal.replace(ties);
		};
		module->rewrite_sigspecs(ties_rewrite);
		if (applied_ties.size()) {
			log("Replacing %zu input terminal bits with tie-togethers in module '%s'\n",
					applied_ties.size(), log_id(module));
		}
		return did_something;
	}
};

struct OptHierPass : Pass {
	OptHierPass() : Pass("opt_hier", "perform cross-boundary optimization") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_hier [selection]\n");
		log("\n");
		log("This pass considers the design hierarchy and propagates unused signals, constant\n");
		log("signals, and tied-together signals across module boundaries to facilitate\n");
		log("optimization. Only the selected modules are affected.\n");
		log("\n");
		log("Note this pass changes port semantics on modules which are not the top.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing OPT_HIER pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, d);

		if (!d->top_module())
			log_cmd_error("Top module needs to be selected for opt_hier\n");

		dict<IdString, ModuleIndex> indices;
		for (auto module : d->modules()) {
			log_debug("Building index for %s\n", log_id(module));
			indices.emplace(module->name, ModuleIndex(module));
		}

		dict<IdString, UsageData> usage_datas;
		for (auto module : d->selected_modules(RTLIL::SELECT_WHOLE_ONLY, RTLIL::SB_UNBOXED_CMDERR)) {
			if (module->get_bool_attribute(ID::top))
				continue;

			log_debug("Starting usage data for %s\n", log_id(module));
			usage_datas.emplace(module->name, UsageData(module));
		}

		for (auto module : d->modules()) {
			for (auto cell : module->cells()) {
				if (usage_datas.count(cell->type)) {
					log_debug("Account for instance %s of %s in %s\n", log_id(cell), log_id(cell->type), log_id(module));
					usage_datas.at(cell->type).refine(cell, indices.at(module->name));
				}
			}
		}

		bool did_something = false;
		for (auto module : d->selected_modules(RTLIL::SELECT_WHOLE_ONLY, RTLIL::SB_UNBOXED_CMDERR)) {
			ModuleIndex &parent_index = indices.at(module->name);

			if (usage_datas.count(module->name)) {
				log_debug("Applying usage data changes to %s\n", log_id(module));
				did_something |= usage_datas.at(module->name).apply_changes(parent_index);
			}

			for (auto cell : module->cells()) {
				if (indices.count(cell->type)) {
					log_debug("Applying changes to instance %s of %s in %s\n", log_id(cell), log_id(cell->type), log_id(module));
					did_something |= indices.at(cell->type).apply_changes(parent_index, cell);
				}
			}
		}
		if (did_something)
			d->scratchpad_set_bool("opt.did_something", true);
	}
} OptHierPass;

PRIVATE_NAMESPACE_END
