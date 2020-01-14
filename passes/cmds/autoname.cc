/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

int autoname_worker(Module *module)
{
	dict<Cell*, pair<int, IdString>> proposed_cell_names;
	dict<Wire*, pair<int, IdString>> proposed_wire_names;
	dict<Wire*, int> wire_score;
	int best_score = -1;

	for (auto cell : module->selected_cells())
	for (auto &conn : cell->connections())
	for (auto bit : conn.second)
		if (bit.wire != nullptr)
			wire_score[bit.wire]++;

	for (auto cell : module->selected_cells()) {
		if (cell->name[0] == '$') {
			for (auto &conn : cell->connections()) {
				string suffix = stringf("_%s_%s", log_id(cell->type), log_id(conn.first));
				for (auto bit : conn.second)
					if (bit.wire != nullptr && bit.wire->name[0] != '$') {
						IdString new_name(bit.wire->name.str() + suffix);
						int score = wire_score.at(bit.wire);
						if (cell->output(conn.first)) score = 0;
						score = 10000*score + new_name.size();
						if (!proposed_cell_names.count(cell) || score < proposed_cell_names.at(cell).first) {
							if (best_score < 0 || score < best_score)
								best_score = score;
							proposed_cell_names[cell] = make_pair(score, new_name);
						}
					}
			}
		} else {
			for (auto &conn : cell->connections()) {
				string suffix = stringf("_%s", log_id(conn.first));
				for (auto bit : conn.second)
					if (bit.wire != nullptr && bit.wire->name[0] == '$' && !bit.wire->port_id) {
						IdString new_name(cell->name.str() + suffix);
						int score = wire_score.at(bit.wire);
						if (cell->output(conn.first)) score = 0;
						score = 10000*score + new_name.size();
						if (!proposed_wire_names.count(bit.wire) || score < proposed_wire_names.at(bit.wire).first) {
							if (best_score < 0 || score < best_score)
								best_score = score;
							proposed_wire_names[bit.wire] = make_pair(score, new_name);
						}
					}
			}
		}
	}

	for (auto &it : proposed_cell_names) {
		if (best_score*2 < it.second.first)
			continue;
		IdString n = module->uniquify(it.second.second);
		log_debug("Rename cell %s in %s to %s.\n", log_id(it.first), log_id(module), log_id(n));
		module->rename(it.first, n);
	}

	for (auto &it : proposed_wire_names) {
		if (best_score*2 < it.second.first)
			continue;
		IdString n = module->uniquify(it.second.second);
		log_debug("Rename wire %s in %s to %s.\n", log_id(it.first), log_id(module), log_id(n));
		module->rename(it.first, n);
	}

	return proposed_cell_names.size() + proposed_wire_names.size();
}

struct AutonamePass : public Pass {
	AutonamePass() : Pass("autoname", "automatically assign names to objects") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    autoname [selection]\n");
		log("\n");
		log("Assign auto-generated public names to objects with private names (the ones\n");
		log("with $-prefix).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-foo") {
			// 	foo = true;
			// 	continue;
			// }
			break;
		}

		log_header(design, "Executing AUTONAME pass.\n");

		for (auto module : design->selected_modules())
		{
			int count = 0, iter = 0;
			while (1) {
				iter++;
				int n = autoname_worker(module);
				if (!n) break;
				count += n;
			}
			if (count > 0)
				log("Renamed %d objects in module %s (%d iterations).\n", count, log_id(module), iter);
		}
	}
} AutonamePass;

PRIVATE_NAMESPACE_END
