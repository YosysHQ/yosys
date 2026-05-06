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

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

	std::pair<Module*, bool> derive_blackbox_dynports(Module* module, Cell* cell, Design* design, ModuleSet& blackbox_derivatives) {
		bool boxed_params = false;

		if (!module->get_blackbox_attribute() || cell->parameters.empty()) {
			return {module, boxed_params};
		}

		if (module->get_bool_attribute(ID::dynports)) {
			IdString new_m_ref = module->derive(design, cell->parameters, true);

			if (new_m_ref == IdString{})
				return {nullptr, boxed_params};
			if (new_m_ref != module->name) {
				module = design->module(new_m_ref);
				blackbox_derivatives.insert(module);
			}
		} else {
			boxed_params = true;
		}

		return {module, boxed_params};
	}

	void check_and_adjust_ports(Module* module, ModuleSet& blackbox_derivatives, bool keep_portwidths, bool top_is_from_verific) {
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
							module, cell, PooledName(design, port).unescape()
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
						log_warning("Resizing cell port %s.%s.%s from %d bits to %d bits.\n", module, cell,
								PooledName(design, port).unescape(), GetSize(sig), GetSize(conn_sig));
					cell->setPort(port, conn_sig);
				}

				if (w->port_output && !w->port_input && conn_sig.has_const())
					log_error("Output port %s.%s.%s (%s) is connected to constants: %s\n",
							module, cell, PooledName(design, port).unescape(), cell->type.unescape(), log_signal(conn_sig));
			}
		}
	}

	bool resolve_connect_directionality(Module* module) {
		pool<Cell*> cells_to_remove;
		vector<SigSig> new_connections;

		for (auto cell : module->cells())
		{
			if (cell->type != ID($connect))
				continue;

			if (cell->has_keep_attr())
				continue;

			SigSpec sig_a = cell->getPort(ID::A);
			SigSpec sig_b = cell->getPort(ID::B);

			// TODO
			if (!sig_a.is_wire() || !sig_b.is_wire())
				continue;

			Wire *wire_a = sig_a.as_wire();
			Wire *wire_b = sig_b.as_wire();

			bool a_is_input = wire_a->port_input && !wire_a->port_output;
			bool a_is_output = wire_a->port_output && !wire_a->port_input;
			bool b_is_input = wire_b->port_input && !wire_b->port_output;
			bool b_is_output = wire_b->port_output && !wire_b->port_input;

			SigSpec driver, driven;

			if (a_is_output && b_is_input) {
				driver = sig_a;
				driven = sig_b;
			} else if (a_is_input && b_is_output) {
				driver = sig_b;
				driven = sig_a;
			} else {
				continue;
			}

			log_debug("Resolving $connect %s: %s <- %s\n", cell, log_signal(driven), log_signal(driver));

			new_connections.push_back({driven, driver});
			cells_to_remove.insert(cell);
		}

		// Apply the changes
		for (auto &conn : new_connections)
			module->connect(conn);

		for (auto cell : cells_to_remove)
			module->remove(cell);

		return !cells_to_remove.empty();
	}

};
YOSYS_NAMESPACE_END
