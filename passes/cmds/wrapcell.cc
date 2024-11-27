/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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
#include "kernel/celltypes.h"
#include "backends/rtlil/rtlil_backend.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

std::optional<std::string> format(std::string fmt, const dict<IdString, Const> &parameters)
{
	std::stringstream result;

	auto it = fmt.begin();
	while (it != fmt.end()) {
		if (*it == '{') {
			it++;
			auto beg = it;
			while (it != fmt.end() && *it != '}') it++;
			if (it == fmt.end()) {
				log("Unclosed curly brackets in format string '%s'\n", fmt.c_str());
				return {};
			}

			auto id = RTLIL::escape_id(std::string(beg, it));
			if (!parameters.count(id)) {
				log("Parameter %s referenced in format string '%s' not found\n", log_id(id), fmt.c_str());
				return {};
			}

			RTLIL_BACKEND::dump_const(result, parameters.at(id));
		} else {
			result << *it;
		}
		it++;
	}

	return {result.str()};
}

struct WrapcellPass : Pass {
	WrapcellPass() : Pass("wrapcell", "wrap individual cells into new modules") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    wrapcell -name <format> [selection]\n");
		log("\n");
		log("This command wraps the selected cells individually into modules. The name for\n");
		log("each wrapper module is derived from the template <format> by substituting\n");
		log("parameter values as specified in curly brackets. If the named module already\n");
		log("exists, it is reused.\n");
		log("\n");
		log("    -setattr <attribute-name>\n");
		log("        set the given boolean attribute on each created wrapper module\n");
		log("\n");
		log("    -formatattr <attribute-name> <format>\n");
		log("        set a string attribute on the created wrapper module by substituting\n");
		log("        parameter values into <format>\n");
		log("\n");
		log("Currently this command only supports wrapping internal cell types.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *d) override
	{
		log_header(d, "Executing WRAPCELL pass. (wrap selected cells)\n");

		struct AttrRule {
			IdString name;
			std::string value_fmt;

			AttrRule(IdString name, std::string value_fmt)
				: name(name), value_fmt(value_fmt) {}
		};
		std::vector<AttrRule> attributes;
		std::string name_fmt;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-setattr" && argidx+1 < args.size()) {
				attributes.emplace_back(RTLIL::escape_id(args[++argidx]), "");
			} else if (args[argidx] == "-formatattr" && argidx+2 < args.size()) {
				IdString id = RTLIL::escape_id(args[++argidx]);
				attributes.emplace_back(id, args[++argidx]);
			} else if (args[argidx] == "-name" && argidx+1 < args.size()) {
				name_fmt = args[++argidx];
			} else {
				break;
			}
		}
		extra_args(args, argidx, d);

		if (name_fmt.empty())
			log_cmd_error("Argument -name required");

		CellTypes ct;
		ct.setup();

		for (auto module : d->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				std::optional<std::string> unescaped_name = format(name_fmt, cell->parameters);
				if (!unescaped_name)
					log_error("Formatting error when processing cell '%s' in module '%s'\n",
							  log_id(cell), log_id(module));

				IdString name = RTLIL::escape_id(unescaped_name.value());

				if (d->module(name)) {
					cell->type = name;
					cell->parameters.clear();
					continue;
				}

				if (!ct.cell_known(cell->type))
					log_error("Non-internal cell type '%s' on cell '%s' in module '%s' unsupported\n",
							  log_id(cell->type), log_id(cell), log_id(module));

				Module *subm = d->addModule(name);
				Cell *subcell = subm->addCell("$1", cell->type);
				for (auto conn : cell->connections()) {
					Wire *w = subm->addWire(conn.first, conn.second.size());
					if (ct.cell_output(cell->type, w->name))
						w->port_output = true;
					else
						w->port_input = true;
					subcell->setPort(conn.first, w);
				}
				subcell->parameters = cell->parameters;
				subm->fixup_ports();

				for (auto rule : attributes) {
					if (rule.value_fmt.empty()) {
						subm->set_bool_attribute(rule.name);
					} else {
						std::optional<std::string> value = format(rule.value_fmt, cell->parameters);

						if (!value)
							log_error("Formatting error when processing cell '%s' in module '%s'\n",
									  log_id(cell), log_id(module));

						subm->set_string_attribute(rule.name, value.value());
					}
				}

				cell->type = name;
				cell->parameters.clear();
			}
		}
	}
} WrapcellPass;

PRIVATE_NAMESPACE_END
