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

};
YOSYS_NAMESPACE_END
