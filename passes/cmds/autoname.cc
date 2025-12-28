/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

typedef struct name_proposal {
	string name;
	unsigned int score;
	name_proposal() : name(""), score(-1) { }
	name_proposal(string name, unsigned int score) : name(name), score(score) { }
	bool operator<(const name_proposal &other) const {
		if (score != other.score)
			return score < other.score;
		else
			return name.length() < other.name.length();
	}
} name_proposal;

int autoname_worker(Module *module, const dict<Wire*, unsigned int>& wire_score)
{
	dict<Cell*, name_proposal> proposed_cell_names;
	dict<Wire*, name_proposal> proposed_wire_names;
	name_proposal best_name;

	for (auto cell : module->selected_cells()) {
		if (cell->name[0] == '$') {
			for (auto &conn : cell->connections()) {
				string suffix;
				for (auto bit : conn.second)
					if (bit.wire != nullptr && bit.wire->name[0] != '$') {
						if (suffix.empty())
							suffix = stringf("_%s_%s", log_id(cell->type), log_id(conn.first));
						name_proposal proposed_name(
							bit.wire->name.str() + suffix,
							cell->output(conn.first) ? 0 : wire_score.at(bit.wire)
						);
						if (!proposed_cell_names.count(cell) || proposed_name < proposed_cell_names.at(cell)) {
							if (proposed_name < best_name)
								best_name = proposed_name;
							proposed_cell_names[cell] = proposed_name;
						}
					}
			}
		} else {
			for (auto &conn : cell->connections()) {
				string suffix;
				for (auto bit : conn.second)
					if (bit.wire != nullptr && bit.wire->name[0] == '$' && !bit.wire->port_id) {
						if (suffix.empty())
							suffix = stringf("_%s", log_id(conn.first));
						name_proposal proposed_name(
							cell->name.str() + suffix,
							cell->output(conn.first) ? 0 : wire_score.at(bit.wire)
						);
						if (!proposed_wire_names.count(bit.wire) || proposed_name < proposed_wire_names.at(bit.wire)) {
							if (proposed_name < best_name)
								best_name = proposed_name;
							proposed_wire_names[bit.wire] = proposed_name;
						}
					}
			}
		}
	}

	int count = 0;
	// compare against double best score for following comparisons so we don't
	// pre-empt a future iteration
	best_name.score *= 2;

	for (auto &it : proposed_cell_names) {
		if (best_name < it.second)
			continue;
		IdString n = module->uniquify(IdString(it.second.name));
		log_debug("Rename cell %s in %s to %s.\n", log_id(it.first), log_id(module), log_id(n));
		module->rename(it.first, n);
		count++;
	}

	for (auto &it : proposed_wire_names) {
		if (best_name < it.second)
			continue;
		IdString n = module->uniquify(IdString(it.second.name));
		log_debug("Rename wire %s in %s to %s.\n", log_id(it.first), log_id(module), log_id(n));
		module->rename(it.first, n);
		count++;
	}

	return count;
}

struct AutonamePass : public Pass {
	AutonamePass() : Pass("autoname", "automatically assign names to objects") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    autoname [selection]\n");
		log("\n");
		log("Assign auto-generated public names to objects with private names (the ones\n");
		log("with $-prefix).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
		extra_args(args, argidx, design);

		log_header(design, "Executing AUTONAME pass.\n");

		for (auto module : design->selected_modules())
		{
			dict<Wire*, unsigned int> wire_score;
			for (auto cell : module->selected_cells())
			for (auto &conn : cell->connections())
			for (auto bit : conn.second)
				if (bit.wire != nullptr)
					wire_score[bit.wire]++;

			int count = 0, iter = 0;
			while (1) {
				iter++;
				int n = autoname_worker(module, wire_score);
				if (!n) break;
				count += n;
			}
			if (count > 0)
				log("Renamed %d objects in module %s (%d iterations).\n", count, log_id(module), iter);
		}
	}
} AutonamePass;

PRIVATE_NAMESPACE_END
