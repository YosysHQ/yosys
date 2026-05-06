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
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {
	enum class SigDirection {
		UNKNOWN,
		INPUT,
		OUTPUT,
		INOUT,
		DRIVEN
	};

	static void build_driven_signals_index(Module *module, SigMap &sigmap, SigPool &driven_signals) {
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					SigSpec sig = sigmap(conn.second);
					driven_signals.add(sig);
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
			}
		}

		if (has_input && has_output)
			return SigDirection::INOUT;
		if (has_output || has_driven)
			return SigDirection::OUTPUT;
		if (has_input)
			return SigDirection::INPUT;
		if (has_unknown)
			return SigDirection::UNKNOWN;

		return SigDirection::DRIVEN;
	}

	void check_and_adjust_ports(Module* module, std::set<Module*>& blackbox_derivatives, bool keep_portwidths, bool top_is_from_verific) {
		Design* design = module->design;

		for (auto cell : module->cells())
		{
			Module *m = design->module(cell->type);

			if (m == nullptr)
				continue;

			bool boxed_params = false;
			if (m->get_blackbox_attribute() && !cell->parameters.empty()) {
				if (m->get_bool_attribute(ID::dynports)) {
					IdString new_m_name = m->derive(design, cell->parameters, true);
					if (new_m_name.empty())
						continue;
					if (new_m_name != m->name) {
						m = design->module(new_m_name);
						blackbox_derivatives.insert(m);
					}
				} else {
					boxed_params = true;
				}
			}

			for (auto &conn : cell->connections())
			{
				Wire *w = m->wire(conn.first);

				if (w == nullptr || w->port_id == 0)
					continue;

				if (GetSize(conn.second) == 0)
					continue;

				SigSpec sig = conn.second;

				bool resize_widths = !keep_portwidths && GetSize(w) != GetSize(conn.second);
				if (resize_widths && top_is_from_verific && boxed_params)
					log_debug("Ignoring width mismatch on %s.%s.%s from verific, is port width parametrizable?\n",
							log_id(module), log_id(cell), log_id(conn.first)
					);
				else if (resize_widths) {
					if (GetSize(w) < GetSize(conn.second))
					{
						int n = GetSize(conn.second) - GetSize(w);
						if (!w->port_input && w->port_output)
						{
							RTLIL::SigSpec out = sig.extract(0, GetSize(w));
							out.extend_u0(GetSize(sig), w->is_signed);
							module->connect(sig.extract(GetSize(w), n), out.extract(GetSize(w), n));
						}
						sig.remove(GetSize(w), n);
					}
					else
					{
						int n = GetSize(w) - GetSize(conn.second);
						if (w->port_input && !w->port_output)
							sig.extend_u0(GetSize(w), sig.is_wire() && sig.as_wire()->is_signed);
						else
							sig.append(module->addWire(NEW_ID, n));
					}

					if (!conn.second.is_fully_const() || !w->port_input || w->port_output)
						log_warning("Resizing cell port %s.%s.%s from %d bits to %d bits.\n", log_id(module), log_id(cell),
								log_id(conn.first), GetSize(conn.second), GetSize(sig));
					cell->setPort(conn.first, sig);
				}

				if (w->port_output && !w->port_input && sig.has_const())
					log_error("Output port %s.%s.%s (%s) is connected to constants: %s\n",
							log_id(module), log_id(cell), log_id(conn.first), log_id(cell->type), log_signal(sig));
			}
		}
	}

	bool resolve_connect_directionality(Module* module) {
		bool did_something = false;
		int iteration = 0;

		while (true) {
			iteration++;
			pool<Cell*> cells_to_remove;
			vector<SigSig> new_connections;
			SigMap sigmap(module);
			SigPool driven_signals;

			build_driven_signals_index(module, sigmap, driven_signals);

			for (auto cell : module->cells())
			{
				if (cell->type != ID($connect))
					continue;

				if (cell->has_keep_attr())
					continue;

				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_b = cell->getPort(ID::B);

				if (sig_a.size() == 0 || sig_b.size() == 0)
					continue;

				SigDirection dir_a = get_signal_direction(sig_a, sigmap, driven_signals);
				SigDirection dir_b = get_signal_direction(sig_b, sigmap, driven_signals);

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
				else {
					continue;
				}

				if (can_resolve) {
					log_debug("Resolving $connect %s: %s <- %s\n", log_id(cell), log_signal(driven), log_signal(driver));
					new_connections.push_back({driven, driver});
					cells_to_remove.insert(cell);
				}
			}

			for (auto &conn : new_connections)
				module->connect(conn);

			for (auto cell : cells_to_remove)
				module->remove(cell);

			if (cells_to_remove.empty())
				break;

			did_something = true;
			log_debug("$connect res iteration %d: resolved %d cells\n", iteration, GetSize(cells_to_remove));
		}

		return did_something;
	}
};

YOSYS_NAMESPACE_END
