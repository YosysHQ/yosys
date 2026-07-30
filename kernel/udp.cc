/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  YosysHQ contributors
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
 */

#include "kernel/udp.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"
#include <cassert>
#include <cctype>
#include <iterator>

YOSYS_NAMESPACE_BEGIN

namespace RTLIL
{
std::string serialize_udp_table(const std::vector<UdpTableEntry> &entries)
{
	std::string result;
	for (const auto &entry : entries) {
		result += entry.inputs;
		result += ':';
		if (entry.curr != 0)
			result += entry.curr;
		result += ':';
		result += entry.next;
		result += '\n';
	}
	return result;
}

std::vector<UdpTableEntry> deserialize_udp_table(const std::string &table)
{
	std::vector<UdpTableEntry> result;
	size_t pos = 0;
	while (pos < table.size()) {
		size_t end = table.find('\n', pos);
		if (end == std::string::npos)
			end = table.size();

		std::string_view row(table.data() + pos, end - pos);
		size_t colon1 = row.find(':');
		size_t colon2 = colon1 == std::string_view::npos ? colon1 : row.find(':', colon1 + 1);
		if (colon1 == std::string_view::npos || colon2 == std::string_view::npos || colon2 + 2 != row.size())
			log_error("Malformed encoded UDP table row `%.*s'.\n", int(row.size()), row.data());

		UdpTableEntry entry;
		entry.inputs = std::string(row.substr(0, colon1));
		if (colon2 != colon1 + 1) {
			if (colon2 != colon1 + 2)
				log_error("Malformed encoded UDP current-state field in row `%.*s'.\n", int(row.size()), row.data());
			entry.curr = row[colon1 + 1];
		}
		entry.next = row[colon2 + 1];
		result.push_back(std::move(entry));
		pos = end + 1;
	}
	return result;
}

// static bool has_edge_symbol(const std::string &inputs)
// {
// 	for (char c : inputs)
// 		if (c == '(' || c == '*' || c == 'r' || c == 'f' || c == 'p' || c == 'n')
// 			return true;
// 	return false;
// }

// static void append_level_symbol(std::vector<Const> &patterns, char symbol)
// {
// 	switch (symbol) {
// 	case '0':
// 		for (auto &pattern : patterns)
// 			pattern.bits().push_back(State::S0);
// 		break;
// 	case '1':
// 		for (auto &pattern : patterns)
// 			pattern.bits().push_back(State::S1);
// 		break;
// 	case 'x':
// 		// A high-impedance value on a UDP input is interpreted as unknown.
// 		// Match both RTLIL states here to preserve that four-state behavior.
// 		for (size_t i = 0, count = patterns.size(); i < count; i++) {
// 			Const high_impedance = patterns[i];
// 			patterns[i].bits().push_back(State::Sx);
// 			high_impedance.bits().push_back(State::Sz);
// 			patterns.push_back(std::move(high_impedance));
// 		}
// 		break;
// 	case '?':
// 		for (auto &pattern : patterns)
// 			pattern.bits().push_back(State::Sa);
// 		break;
// 	case 'b': {
// 		size_t count = patterns.size();
// 		for (size_t i = 0; i < count; i++) {
// 			Const one = patterns[i];
// 			patterns[i].bits().push_back(State::S0);
// 			one.bits().push_back(State::S1);
// 			patterns.push_back(std::move(one));
// 		}
// 		break;
// 	}
// 	default:
// 		log_error("Unsupported level symbol `%c' in normalized UDP table.\n", symbol);
// 	}
// }

// static std::vector<Const> make_patterns(const UdpTableEntry &entry, bool sequential)
// {
// 	std::vector<Const> patterns(1);
// 	for (char symbol : entry.inputs)
// 		append_level_symbol(patterns, symbol);
// 	if (sequential)
// 		append_level_symbol(patterns, entry.current);
// 	return patterns;
// }

// static SigSpec get_udp_inputs(Module *module, const UdpDefinition &udp)
// {
// 	SigSpec inputs;
// 	for (size_t i = 1; i < udp.ports.size(); i++) {
// 		Wire *wire = module->wire(udp.ports[i]);
// 		if (wire == nullptr || wire->width != 1)
// 			log_error("UDP module `%s' has a missing or non-scalar input port `%s'.\n", log_id(module), log_id(udp.ports[i]));
// 		inputs.append(wire);
// 	}
// 	return inputs;
// }

// static void preserve_edge_udp(Module *module, const UdpDefinition &udp, const SigSpec &inputs, Wire *output)
// {
// 	Cell *cell = module->addCell(NEW_ID, ID($udp));
// 	cell->parameters[ID(A_WIDTH)] = Const(GetSize(inputs));
// 	cell->parameters[ID(TABLE)] = Const(serialize_udp_table(udp.entries));
// 	cell->parameters[ID(SEQUENTIAL)] = Const(udp.sequential);
// 	cell->setPort(ID::A, inputs);
// 	cell->setPort(ID::Y, output);
// }

namespace
{
struct NormalizedUdpTableEntry {
	std::vector<std::string> inputs;
	char curr = 0;
	char next = 0;
};

struct UDPImporter {
	const UdpDefinition &udp;
	std::vector<NormalizedUdpTableEntry> entries;
	Module *container;
	std::vector<Wire *> inputs;
	Wire *output;

	explicit UDPImporter(Module *module, const UdpDefinition &udp) : udp{udp}, container{module}
	{
		output = module->wire(udp.ports.front());
		if (!output || output->width != 1)
			log_error("UDP module `%s' has a missing or non-scalar output port `%s'.\n", log_id(module), log_id(udp.ports.front()));

		for (auto it = std::next(udp.ports.begin()); it != udp.ports.end(); ++it) {
			auto *n = module->wire(*it);
			if (!n || n->width != 1)
				log_error("UDP module `%s' has a missing or non-scalar input port `%s'.\n", log_id(module), log_id(*it));
			inputs.push_back(n);
		}
	}

	void run()
	{
		normalize();
		if (udp.sequential) {
			import_seq();
		} else {
			import_comb();
		}
	}

	void normalize()
	{
		entries.clear();
		entries.reserve(udp.entries.size());
		for (const auto &entry : udp.entries) {
			NormalizedUdpTableEntry normalized;
			normalized.curr = tolower(entry.curr);
			normalized.next = tolower(entry.next);

			for (size_t i = 0; i < entry.inputs.size();) {
				std::string state;
				if (entry.inputs[i] == '(') {
					log_assert(i + 3 < entry.inputs.size());
					log_assert(entry.inputs[i + 3] == ')');
					state = entry.inputs.substr(i, 4);
					i += 4;
					if (state == "(01)")
						state = "r";
					else if (state == "(10)")
						state = "f";
					else if (state == "(?"
							  "?)") // Separate to avoid the 'trigraph' warning
						state = "*";
					else {
						state = state.substr(1, 2);
					}
				} else {
					state.push_back(entry.inputs[i++]);
				}
				for (auto &c : state) {
					c = std::tolower(c);
				}
				normalized.inputs.push_back(std::move(state));
			}
			log_assert(normalized.inputs.size() == inputs.size());
			entries.push_back(std::move(normalized));
		}
	}

	void import_comb()
	{
		auto *sw = new SwitchRule;
		sw->signal = [&] {
			SigSpec ans;
			for (auto *n : inputs) {
				ans.append(n);
			}
			return ans;
		}();
		auto *next = container->addWire(NEW_ID);
		for (const auto &item : entries) {
			auto *br = new CaseRule;
			br->compare.emplace_back(mk_pattern(item));
			br->actions.emplace_back(next, mk_output_value(item.next));
			sw->cases.push_back(br);
		}

		auto *sync = new SyncRule;
		sync->type = STa;
		sync->actions.emplace_back(output, next);

		auto *proc = container->addProcess(NEW_ID);
		proc->root_case.switches.push_back(sw);
		proc->root_case.actions.emplace_back(next, State::Sx);  // Defaults to x.
		proc->syncs.push_back(sync);
	}

	Const mk_pattern(const NormalizedUdpTableEntry &entry, std::optional<std::size_t> ignore_index = std::nullopt)
	{
		std::vector<State> ans;
		for (std::size_t i = 0; i < entry.inputs.size(); ++i) {
			if (ignore_index && *ignore_index == i)
				continue;
			const auto &state = entry.inputs[i];
			if (state.size() != 1)
				log_error("Invalid state '%s' in combinational UDP table.\n", state.c_str());
			auto c = state.front();
			switch (c) {
			case '0':
				ans.push_back(State::S0);
				break;
			case '1':
				ans.push_back(State::S1);
				break;
			case '?':
			case 'b':
				ans.push_back(State::Sa);
				break;
			case 'x':
				ans.push_back(State::Sx);
				break;
			default:
				log_error("Invalid pattern bit '%c'", c);
			}
		}
		return ans;
	}

	Const mk_output_value(char c)
	{
		switch (c) {
		case '0':
			return State::S0;
		case '1':
			return State::S1;
		case 'x':
			return State::Sx;
		default:
			log_error("Invalid output value '%c'", c);
		}
	}

	void import_seq()
	{
		std::optional<std::size_t> clock_index;
		std::optional<std::string> edge_symbol;
		std::vector<std::size_t> edge_entries;
		std::vector<std::size_t> level_entries;
		std::vector<std::size_t> no_change_entries;
		for (std::size_t i = 0; i < entries.size(); ++i) {
			const auto &entry = entries[i];
			for (std::size_t j = 0; j < entry.inputs.size(); ++j) {
				const auto no_change = is_no_change(entry);
				if (is_edge_sensitive(entry.inputs[j])) {
					if (!clock_index) {
						clock_index = j;
						edge_symbol = entry.inputs[j];
					} else if (clock_index.value() != j && !no_change) {
						log_error("Multiple edge-sensitive inputs found in UDP definition. Only one edge-sensitive input is "
							  "allowed for sequential UDPs.");
					} else if (edge_symbol.value() != entry.inputs[j] && !no_change) {
						log_error("Conflicting edge-sensitive symbols found for input %zu in UDP definition. Only one "
							  "edge-sensitive symbol is allowed for sequential UDPs.",
							  j);
					}
					edge_entries.push_back(i);
				} else {
					level_entries.push_back(i);
				}
			}
		}

		if (clock_index) {
			// FF
			auto *clk = inputs[clock_index.value()];

			auto *next = container->addWire(NEW_ID);
			auto *sw = new SwitchRule;
			sw->signal = [&] {
				SigSpec ans;
				for (std::size_t i = 0; i < inputs.size(); ++i) {
					if (i != clock_index.value()) {
						ans.append(inputs[i]);
					}
				}
				return ans;
			}();

			if (!no_change_entries.empty()) {
				auto *br = new CaseRule;
				for (auto index : no_change_entries) {
					const auto &entry = entries[index];
					br->compare.emplace_back(mk_pattern(entry, clock_index));
					br->actions.emplace_back(next, sw->signal);
					sw->cases.push_back(br);
				}
			}
			if (!level_entries.empty()) {
				auto *br = new CaseRule;
				for (auto index : level_entries) {
					const auto &entry = entries[index];
					br->compare.emplace_back(mk_pattern(entry, clock_index));
					br->actions.emplace_back(next, mk_output_value(entry.next));
					sw->cases.push_back(br);
				}
			}
			for (auto index : edge_entries) {
				const auto &entry = entries[index];
				auto *br = new CaseRule;
				br->compare.emplace_back(mk_pattern(entry, clock_index));
				br->actions.emplace_back(next, mk_output_value(entry.next));
				sw->cases.push_back(br);
			}

			auto *sync = new SyncRule;
			if (const auto &e = edge_symbol.value(); e == "r" || e == "p") {
				sync->type = STp;
			} else if (e == "f" || e == "n") {
				sync->type = STn;
			} else if (e == "*") {
				sync->type = STa;
			} else {
				log_error("Invalid edge-sensitive symbol '%s' in sequential UDP table.\n", edge_symbol.value().c_str());
			}
			sync->signal = clk;
			sync->actions.emplace_back(output, next);

			auto *proc = container->addProcess(NEW_ID);
			proc->root_case.switches.push_back(sw);
			proc->syncs.push_back(sync);
			if (udp.init) {
				proc->root_case.actions.emplace_back(next, mk_output_value(udp.init));
			}
		} else {
			// Latch
		}
	}

	bool is_edge_sensitive(const std::string &state)
	{
		return state == "r" || state == "f" || state == "p" || state == "n" || state == "*" ||
		       (state.size() == 4 && state.front() == '(' && state.back() == ')');
	}

	bool is_no_change(const NormalizedUdpTableEntry &entry)
	{
		assert(udp.sequential);
		const auto curr = entry.curr;
		const auto next = entry.next;
		if (curr == '0' && next == '0')
			return true;
		if (curr == '1' && next == '1')
			return true;
		if (curr == '?' && next == '-')
			return true;
		return false;
	}

	std::tuple<std::size_t, std::string> extract_clock()
	{
		std::optional<std::size_t> clock_index;
		std::optional<std::string> edge;
		for (const auto &item : entries) {
			for (std::size_t i = 0; i < item.inputs.size(); ++i) {
				if (is_edge_sensitive(item.inputs[i])) {
					if (!clock_index) {
						clock_index = i;
						edge = item.inputs[i];
					} else if (clock_index.value() != i) {
						log_error("Multiple edge-sensitive inputs found in UDP definition. Only one edge-sensitive input is "
							  "allowed for sequential UDPs.");
					} else if (edge.value() != item.inputs[i]) {
						log_error("Conflicting edge-sensitive symbols found for input %zu in UDP definition. Only one "
							  "edge-sensitive symbol is allowed for sequential UDPs.",
							  i);
					}
					break;
				}
			}
			if (clock_index)
				break;
		}
		if (!clock_index)
			log_error("No edge-sensitive input found in sequential UDP definition.\n");
		return std::make_tuple(clock_index.value(), edge.value());
	}
};
} // namespace

void import_udp(Module *module, const UdpDefinition &udp)
{
	if (udp.ports.size() < 2)
		log_error("UDP module `%s' must have one output and at least one input.\n", log_id(module));

	UDPImporter imp(module, udp);
	imp.run();
}
} // namespace RTLIL

YOSYS_NAMESPACE_END
