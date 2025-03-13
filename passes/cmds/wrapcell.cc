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
#include "kernel/sigtools.h"
#include "backends/rtlil/rtlil_backend.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool has_fmt_field(std::string fmt, std::string field_name)
{
	auto it = fmt.begin();
	while (it != fmt.end()) {
		if (*it == '{') {
			it++;
			auto beg = it;
			while (it != fmt.end() && *it != '}') it++;
			if (it == fmt.end())
				return false;

			if (std::string(beg, it) == field_name)
				return true;
		}
		it++;
	}
	return false;
}

struct ContextData {
	std::string unused_outputs;
};

std::optional<std::string> format(std::string fmt, const dict<IdString, Const> &parameters,
								  const ContextData &context)
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

			std::string param_name = {beg, it};

			if (param_name == "%unused") {
				result << context.unused_outputs;
			} else {
				auto id = RTLIL::escape_id(std::string(beg, it));
				if (!parameters.count(id)) {
					log("Parameter %s referenced in format string '%s' not found\n", log_id(id), fmt.c_str());
					return {};
				}

				RTLIL_BACKEND::dump_const(result, parameters.at(id));
			}
		} else {
			result << *it;
		}
		it++;
	}

	return {result.str()};
}

struct Chunk {
	IdString port;
	int base, len;

	Chunk(IdString id, int base, int len)
		: port(id), base(base), len(len) {}

	IdString format(Cell *cell)
	{
		if (len == cell->getPort(port).size())
			return port;
		else if (len == 1)
			return stringf("%s[%d]", port.c_str(), base);
		else
			return stringf("%s[%d:%d]", port.c_str(), base + len - 1, base);
	}

	SigSpec sample(Cell *cell)
	{
		return cell->getPort(port).extract(base, len);
	}
};

// Joins contiguous runs of bits into a 'Chunk'
std::vector<Chunk> collect_chunks(std::vector<std::pair<IdString, int>> bits)
{
	std::vector<Chunk> ret;
	std::sort(bits.begin(), bits.end());
	for (auto it = bits.begin(); it != bits.end();) {
		auto sep = it + 1;
		for (; sep != bits.end() &&
				sep->first == it->first &&
				sep->second == (sep - 1)->second + 1; sep++);
		ret.emplace_back(it->first, it->second, sep - it);
		it = sep;
	}
	return ret;
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
		log("If the template contains the special string '{%%unused}', the command tracks\n");
		log("unused output ports -- specialized wrapper modules will be generated per every\n");
		log("distinct set of unused port bits as appearing on any selected cell.\n");
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

		bool tracking_unused = has_fmt_field(name_fmt, "%unused");

		for (auto module : d->selected_modules()) {
			SigPool unused;

			for (auto wire : module->wires())
			if (wire->has_attribute(ID::unused_bits)) {
				std::string str = wire->get_string_attribute(ID::unused_bits);
				for (auto it = str.begin(); it != str.end();) {
					auto sep = it;
					for (; sep != str.end() && *sep != ' '; sep++);
					unused.add(SigBit(wire, std::stoi(std::string(it, sep))));
					for (it = sep; it != str.end() && *it == ' '; it++);
				}
			}

			for (auto cell : module->selected_cells()) {
				Module *subm;
				Cell *subcell;

				if (!ct.cell_known(cell->type))
					log_error("Non-internal cell type '%s' on cell '%s' in module '%s' unsupported\n",
							  log_id(cell->type), log_id(cell), log_id(module));

				std::vector<std::pair<IdString, int>> unused_outputs, used_outputs;
				for (auto conn : cell->connections()) {
					if (ct.cell_output(cell->type, conn.first))
					for (int i = 0; i < conn.second.size(); i++) {
						if (tracking_unused && unused.check(conn.second[i]))
							unused_outputs.emplace_back(conn.first, i);
						else
							used_outputs.emplace_back(conn.first, i);
					}
				}

				ContextData context;
				if (!unused_outputs.empty()) {
					context.unused_outputs += "_unused";
					for (auto chunk : collect_chunks(unused_outputs))
						context.unused_outputs += "_" + RTLIL::unescape_id(chunk.format(cell));
				}

				std::optional<std::string> unescaped_name = format(name_fmt, cell->parameters, context);
				if (!unescaped_name)
					log_error("Formatting error when processing cell '%s' in module '%s'\n",
							  log_id(cell), log_id(module));

				IdString name = RTLIL::escape_id(unescaped_name.value());
				if (d->module(name))
					goto replace_cell;

				subm = d->addModule(name);
				subcell = subm->addCell("$1", cell->type);
				for (auto conn : cell->connections()) {
					if (ct.cell_output(cell->type, conn.first)) {
						// Insert marker bits as placehodlers which need to be replaced
						subcell->setPort(conn.first, SigSpec(RTLIL::Sm, conn.second.size()));
					} else {
						Wire *w = subm->addWire(conn.first, conn.second.size());
						w->port_input = true;
						subcell->setPort(conn.first, w);
					}
				}

				for (auto chunk : collect_chunks(used_outputs)) {
					Wire *w = subm->addWire(chunk.format(cell), chunk.len);
					w->port_output = true;
					subcell->connections_[chunk.port].replace(chunk.base, w);
				}

				for (auto chunk : collect_chunks(unused_outputs)) {
					Wire *w = subm->addWire(chunk.format(cell), chunk.len);
					subcell->connections_[chunk.port].replace(chunk.base, w);
				}

				subcell->parameters = cell->parameters;
				subm->fixup_ports();

				for (auto rule : attributes) {
					if (rule.value_fmt.empty()) {
						subm->set_bool_attribute(rule.name);
					} else {
						std::optional<std::string> value = format(rule.value_fmt, cell->parameters, context);

						if (!value)
							log_error("Formatting error when processing cell '%s' in module '%s'\n",
									  log_id(cell), log_id(module));

						subm->set_string_attribute(rule.name, value.value());
					}
				}

			replace_cell:
				cell->parameters.clear();

				dict<IdString, SigSpec> new_connections;

				for (auto conn : cell->connections())
				if (!ct.cell_output(cell->type, conn.first))
					new_connections[conn.first] = conn.second;

				for (auto chunk : collect_chunks(used_outputs))
					new_connections[chunk.format(cell)] = chunk.sample(cell);

				cell->type = name;
				cell->connections_ = new_connections;
			}
		}
	}
} WrapcellPass;

PRIVATE_NAMESPACE_END
