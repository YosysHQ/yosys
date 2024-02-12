/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

// build: yosys-config --build scopeinfo_example.so scopeinfo_example.cc
// use: yosys -m scopeinfo_example.so

#include "backends/rtlil/rtlil_backend.h"
#include "kernel/scopeinfo.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ScopeinfoExamplePass : public Pass {
	ScopeinfoExamplePass() : Pass("scopeinfo_example", "dump scopeinfo") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scopeinfo_example [options] [selection]\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing SCOPEINFO_EXAMPLE pass.\n");

		bool do_wires = false;
		bool do_common = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-wires") {
				do_wires = true;
				continue;
			}
			if (args[argidx] == "-common") {
				do_common = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);


		if (do_wires) {
			for (auto module : design->selected_modules()) {
				log("Source hierarchy for all selected wires within %s:\n", log_id(module));
				ModuleHdlnameIndex index(module);

				index.index_scopeinfo_cells();

				for (auto wire : module->selected_wires()) {
					if (!wire->name.isPublic())
						continue;

					auto wire_scope = index.containing_scope(wire);

					if (!wire_scope.first.valid()) {
						log_warning("Couldn't find containing scope for %s in index\n", log_id(wire));
						continue;
					}

					log("%s %s\n", wire_scope.first.path_str().c_str(), log_id(wire_scope.second));
					for (auto src : index.sources(wire))
						log(" - %s\n", src.c_str());
				}
			}
		}

		if (do_common) {
			for (auto module : design->selected_modules()) {
				std::vector<Wire *> wires = module->selected_wires();

				// Shuffle wires so this example produces more interesting outputs
				std::sort(wires.begin(), wires.end(), [](Wire *a, Wire *b) {
					return mkhash_xorshift(a->name.hash() * 0x2c9277b5) < mkhash_xorshift(b->name.hash() * 0x2c9277b5);
				});

				ModuleHdlnameIndex index(module);

				index.index_scopeinfo_cells();

				for (auto wire_i = wires.begin(), wire_end = wires.end(); wire_i != wire_end; ++wire_i) {
					if (!(*wire_i)->name.isPublic())
						continue;

					std::pair<ModuleHdlnameIndex::Cursor, IdString> scope_i = index.containing_scope(*wire_i);
					if (!scope_i.first.valid())
						continue;

					int limit = 0;

					for (auto wire_j = wire_i + 1; wire_j != wire_end; ++wire_j) {
						if (!(*wire_j)->name.isPublic())
							continue;

						std::pair<ModuleHdlnameIndex::Cursor, IdString> scope_j = index.containing_scope(*wire_j);
						if (!scope_j.first.valid())
							continue;

						// Skip wires in the same hierarchy level
						if (scope_i.first == scope_j.first)
							continue;


						ModuleHdlnameIndex::Cursor common = scope_i.first.common_ancestor(scope_j.first);

						// Try to show at least some non-root common ancestors
						if (common.is_root() && limit > 5)
							continue;

						log("common_ancestor(%s %s%s%s, %s %s%s%s) = %s %s\n",
							log_id(module), scope_i.first.path_str().c_str(), scope_i.first.is_root() ? "" : " ", log_id(scope_i.second),
							log_id(module), scope_j.first.path_str().c_str(), scope_j.first.is_root() ? "" : " ", log_id(scope_j.second),
							log_id(module), common.path_str().c_str()
						);

						if (++limit == 10)
							break;
					}
				}
			}
		}
	}
} ScopeinfoExamplePass;

PRIVATE_NAMESPACE_END
