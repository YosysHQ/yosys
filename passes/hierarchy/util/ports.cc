/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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

#include "kernel/yosys_common.h"
#include "passes/hierarchy/util/ports.h"
#include "passes/hierarchy/util/interfaces.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {
	enum class SigDirection {
		UNKNOWN,
		INPUT,
		OUTPUT,
		INOUT,
		DRIVEN,
		CONFLICT
	};

	static void build_driven_signals_index(Module *module, SigMap &sigmap, SigPool &driven_signals) {
		for (auto cell : module->cells()) {
			for (const auto& [port, sig] : cell->connections()) {
				if (cell->output(port)) {
					SigSpec mapped_sig = sigmap(sig);
					driven_signals.add(mapped_sig);
				}
			}
		}

		for (auto &conn : module->connections()) {
			if (conn.second.is_fully_const()) {
				SigSpec lhs = sigmap(conn.first);
				driven_signals.add(lhs);
			}
		}
	}

	static SigDirection get_signal_direction(const SigSpec &sig, SigMap &sigmap, const SigPool &driven_signals) {
		if (sig.is_fully_const())
			return SigDirection::DRIVEN;

		bool has_input = false;
		bool has_output = false;
		bool has_driven = false;
		bool has_unknown = false;

		for (auto &chunk : sig.chunks()) {
			if (chunk.is_wire()) {
				Wire *w = chunk.wire;

				if (w->port_input && w->port_output) {
					has_input = true;
					has_output = true;
				} else if (w->port_input) {
					has_input = true;
				} else if (w->port_output) {
					has_output = true;
				} else {
					SigSpec chunk_sig = sigmap(SigSpec(chunk));

					if (driven_signals.check_any(chunk_sig)) {
						has_driven = true;
					} else {
						has_unknown = true;
					}
				}
			} else {
				has_driven = true;
			}
		}

		if (has_input && has_driven)
			return SigDirection::CONFLICT;
		if (has_input && has_output)
			return SigDirection::INOUT;
		if (has_output)
			return SigDirection::OUTPUT;
		if (has_driven)
			return SigDirection::DRIVEN;
		if (has_input)
			return SigDirection::INPUT;
		if (has_unknown)
			return SigDirection::UNKNOWN;

		return SigDirection::DRIVEN;
	}

	std::pair<Module*, bool> derive_blackbox_dynports(Module* module, Cell* cell, Design* design, std::set<Module*>& blackbox_derivatives) {
		bool boxed_params = false;

		if (!module->get_blackbox_attribute() || cell->parameters.empty()) {
			return {module, boxed_params};
		}

		if (module->get_bool_attribute(ID::dynports)) {
			IdString new_m_name = module->derive(design, cell->parameters, true);

			if (new_m_name.empty())
				return {nullptr, boxed_params};
			if (new_m_name != module->name) {
				module = design->module(new_m_name);
				blackbox_derivatives.insert(module);
			}
		} else {
			boxed_params = true;
		}

		return {module, boxed_params};
	}

	void check_and_adjust_ports(Module* module, std::set<Module*>& blackbox_derivatives, bool keep_portwidths, bool top_is_from_verific) {
		Design* design = module->design;

		for (auto cell : module->cells())
		{
			Module *m = design->module(cell->type);

			if (m == nullptr)
				continue;

			auto [derived_m, boxed_params] = derive_blackbox_dynports(m, cell, design, blackbox_derivatives);
			if (derived_m == nullptr)
				continue;
			m = derived_m;

			for (const auto& [port, sig] : cell->connections())
			{
				Wire *w = m->wire(port);

				if (w == nullptr || w->port_id == 0)
					continue;

				if (GetSize(sig) == 0)
					continue;

				SigSpec conn_sig = sig;

				bool resize_widths = !keep_portwidths && GetSize(w) != GetSize(sig);
				if (resize_widths && top_is_from_verific && boxed_params)
					log_debug("Ignoring width mismatch on %s.%s.%s from verific\n",
							log_id(module), log_id(cell), log_id(port)
					);
				else if (resize_widths) {
					if (GetSize(w) < GetSize(sig))
					{
						int n = GetSize(sig) - GetSize(w);
						if (!w->port_input && w->port_output)
						{
							RTLIL::SigSpec out = conn_sig.extract(0, GetSize(w));
							out.extend_u0(GetSize(conn_sig), w->is_signed);
							module->connect(conn_sig.extract(GetSize(w), n), out.extract(GetSize(w), n));
						}
						conn_sig.remove(GetSize(w), n);
					}
					else
					{
						int n = GetSize(w) - GetSize(sig);
						if (w->port_input && !w->port_output)
							conn_sig.extend_u0(GetSize(w), conn_sig.is_wire() && conn_sig.as_wire()->is_signed);
						else
							conn_sig.append(module->addWire(NEW_ID, n));
					}

					if (!sig.is_fully_const() || !w->port_input || w->port_output)
						log_warning("Resizing cell port %s.%s.%s from %d bits to %d bits.\n", log_id(module), log_id(cell),
								log_id(port), GetSize(sig), GetSize(conn_sig));
					cell->setPort(port, conn_sig);
				}

				if (w->port_output && !w->port_input && conn_sig.has_const())
					log_error("Output port %s.%s.%s (%s) is connected to constants: %s\n",
							log_id(module), log_id(cell), log_id(port), log_id(cell->type), log_signal(conn_sig));
			}
		}
	}

	void resolve_acc_connects(Design* design, const ConnectAccumulator& connect_acc) {
		std::vector<IdString> sorted_module_names;
		for (const auto& [mod_name, cell_names] : connect_acc.module_connect_cells)
			sorted_module_names.push_back(mod_name);
		std::sort(sorted_module_names.begin(), sorted_module_names.end());

		for (auto mod_name : sorted_module_names) {
			Module* module = design->module(mod_name);
			if (!module)
				continue;

			const pool<IdString>& cell_names = connect_acc.module_connect_cells.at(mod_name);
			pool<IdString> remaining_cell_names = cell_names;
			int iteration = 0;

			while (true) {
				iteration++;
				pool<Cell*> cells_to_remove;
				vector<SigSig> new_connections;
				SigMap sigmap(module);
				SigPool driven_signals;

				build_driven_signals_index(module, sigmap, driven_signals);

				for (auto cell_name : remaining_cell_names) {
					Cell* cell = module->cell(cell_name);
					if (!cell || cell->type != ID($connect) || cell->has_keep_attr())
						continue;

					SigSpec sig_a = cell->getPort(ID::A);
					SigSpec sig_b = cell->getPort(ID::B);

					if (sig_a.size() == 0 || sig_b.size() == 0)
						continue;

					SigDirection dir_a = get_signal_direction(sig_a, sigmap, driven_signals);
					SigDirection dir_b = get_signal_direction(sig_b, sigmap, driven_signals);

					if (dir_a == SigDirection::CONFLICT || dir_b == SigDirection::CONFLICT)
						continue;

					SigSpec driver, driven;
					bool can_resolve = false;

					if ((dir_a == SigDirection::OUTPUT || dir_a == SigDirection::DRIVEN) && dir_b == SigDirection::INPUT) {
						driver = sig_a;
						driven = sig_b;
						can_resolve = true;
					}
					else if (dir_a == SigDirection::INPUT && (dir_b == SigDirection::OUTPUT || dir_b == SigDirection::DRIVEN)) {
						driver = sig_b;
						driven = sig_a;
						can_resolve = true;
					}
					else if (dir_a == SigDirection::DRIVEN && dir_b == SigDirection::UNKNOWN) {
						driver = sig_a;
						driven = sig_b;
						can_resolve = true;
					}
					else if (dir_a == SigDirection::UNKNOWN && dir_b == SigDirection::DRIVEN) {
						driver = sig_b;
						driven = sig_a;
						can_resolve = true;
					}

					if (can_resolve) {
						log_debug("Resolving $connect %s: %s <- %s\n", log_id(cell), log_signal(driven), log_signal(driver));
						new_connections.push_back({driven, driver});
						cells_to_remove.insert(cell);
					}
				}

				for (auto &conn : new_connections)
					module->connect(conn);

				for (auto cell : cells_to_remove) {
					remaining_cell_names.erase(cell->name);
					module->remove(cell);
				}

				if (cells_to_remove.empty())
					break;

				log_debug("$connect res iteration %d: resolved %d cells\n", iteration, GetSize(cells_to_remove));
			}
		}
	}
};

YOSYS_NAMESPACE_END
