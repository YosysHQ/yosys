/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Nick Allison <nick@yosyshq.com>
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

#include "frontends/common/rewriter/rewriter.h"

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

#include <type_traits>

namespace Yosys::Rewriter {

template<typename T>
bool RewriteRule<T>::rewrite(RTLIL::Design *design) const
{
	bool changed = false;
	for (auto module : design->selected_modules()) {
		auto sigmap = Rewriter::construct_sigmap(module);
		changed |= rewrite_mod(module, sigmap);
	}
	return changed;
}

template<typename T>
bool RewriteRule<T>::rewrite_mod(RTLIL::Module *module, SigMap &sigmap) const
{
	if constexpr (std::is_same_v<T, RTLIL::Module>)
		return apply(module, sigmap);

	if (module->get_bool_attribute(ID::blackbox))
		return false;

	bool changed = false;
	if constexpr (std::is_same_v<T, RTLIL::Wire>)
		for (auto *wire : module->selected_wires())
			changed |= apply(wire, sigmap);
	if constexpr (std::is_same_v<T, RTLIL::Cell>)
		for (auto *cell : module->selected_cells())
			changed |= apply(cell, sigmap);
	return changed;
}

template struct RewriteRule<RTLIL::Module>;
template struct RewriteRule<RTLIL::Wire>;
template struct RewriteRule<RTLIL::Cell>;

// Redirect existing drivers of `sig` to a dummy wire
// see connect.cc
void unset_drivers(RTLIL::Module *module, SigMap &sigmap, RTLIL::SigSpec &sig)
{
	RTLIL::Design* design = module->design;
	CellTypes ct(design);

	RTLIL::Wire *dummy_wire = module->addWire(NEW_ID, sig.size());

	for (auto cell : module->cells())
	for (auto &port : cell->connections_)
		if (ct.cell_output(cell->type, port.first))
			sigmap(port.second).replace(sig, dummy_wire, &port.second);

	for (auto &conn : module->connections_)
		sigmap(conn.first).replace(sig, dummy_wire, &conn.first);
}

SigMap construct_sigmap(RTLIL::Module *module) {
	// see connect.cc
	SigMap sigmap;
	for (auto &it : module->connections()) {
		std::vector<RTLIL::SigBit> lhs = it.first.to_sigbit_vector();
		std::vector<RTLIL::SigBit> rhs = it.second.to_sigbit_vector();
		for (size_t i = 0; i < lhs.size(); i++)
			if (rhs[i].wire != nullptr)
				sigmap.add(lhs[i], rhs[i]);
	}
	return sigmap;
}


} // namespace Yosys::Rewriter
