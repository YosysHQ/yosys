/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/yw.h"
#include "libs/json11/json11.hpp"

USING_YOSYS_NAMESPACE

// Use the same formatting as witness.py uses
static const char *pretty_name(IdString id)
{
	const char *c_str = id.c_str();
	const char *p = c_str;

	if (*p != '\\')
		return c_str;
	p++;

	if (*p == '[') {
		p++;
		while (*p >= '0' && *p <= '9')
			p++;
		if (p[0] != ']' || p[1] != 0)
			return c_str;
		return c_str + 1;
	}

	if (!(*p >= 'a' && *p <= 'z') && !(*p >= 'A' && *p <= 'Z') && *p != '_')
		return c_str;
	p++;
	while ((*p >= '0' && *p <= '9') || (*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || *p == '_')
		p++;

	if (*p != 0)
		return c_str;
	return c_str + 1;
}

std::string IdPath::str() const
{
	std::string result;

	for (auto &item : *this) {
		const char *pretty = pretty_name(item);
		if (pretty[0] == '[') {
			result += pretty;
			continue;
		}
		if (!result.empty())
			result += '.';
		result += pretty;
		if (pretty[0] == '\\' || pretty[0] == '$')
			result += ' ';
	}

	return result;
}

bool IdPath::get_address(int &addr) const
{
	if (empty())
		return false;
	auto &last = back();
	if (!last.begins_with("\\["))
		return false;
	if (last == "\\[0]") {
		addr = 0;
		return true;
	}
	char first = last.c_str()[2];
	if (first < '1' || first > '9')
		return false;
	char *endptr;
	addr = std::strtol(last.c_str() + 2, &endptr, 10);
	return endptr[0] == ']' && endptr[1] == 0;
}

static std::vector<IdString> get_path(const json11::Json &json)
{
	std::vector<IdString> result;
	for (auto &path_item : json.array_items()) {
		auto const &path_item_str = path_item.string_value();
		if (path_item_str.empty())
			return {};;
		result.push_back(path_item_str);
	}
	return result;
}

ReadWitness::ReadWitness(const std::string &filename) :
	filename(filename)
{
	std::ifstream f(filename.c_str());
	if (f.fail() || GetSize(filename) == 0)
		log_error("Cannot open file `%s`\n", filename.c_str());
	std::stringstream buf;
	buf << f.rdbuf();
	std::string err;
	json11::Json json = json11::Json::parse(buf.str(), err);
	if (!err.empty())
		log_error("Failed to parse `%s`: %s\n", filename.c_str(), err.c_str());

	std::string format = json["format"].string_value();

	if (format.empty())
		log_error("Failed to parse `%s`: Unknown format\n", filename.c_str());
	if (format != "Yosys Witness Trace")
		log_error("Failed to parse `%s`: Unsupported format `%s`\n", filename.c_str(), format.c_str());

	for (auto &clock_json : json["clocks"].array_items()) {
		Clock clock;
		clock.path = get_path(clock_json["path"]);
		if (clock.path.empty())
			log_error("Failed to parse `%s`: Missing path for clock `%s`\n", filename.c_str(), clock_json.dump().c_str());
		auto edge_str = clock_json["edge"];
		if (edge_str.string_value() == "posedge")
			clock.is_posedge = true;
		else if (edge_str.string_value() == "negedge")
			clock.is_negedge = true;
		else
			log_error("Failed to parse `%s`: Unknown edge type for clock `%s`\n", filename.c_str(), clock_json.dump().c_str());
		if (!clock_json["offset"].is_number())
			log_error("Failed to parse `%s`: Unknown offset for clock `%s`\n", filename.c_str(), clock_json.dump().c_str());
		clock.offset = clock_json["offset"].int_value();
		if (clock.offset < 0)
			log_error("Failed to parse `%s`: Invalid offset for clock `%s`\n", filename.c_str(), clock_json.dump().c_str());
		clocks.push_back(clock);
	}

	int bits_offset = 0;
	for (auto &signal_json : json["signals"].array_items()) {
		Signal signal;
		signal.bits_offset = bits_offset;
		signal.path = get_path(signal_json["path"]);
		if (signal.path.empty())
			log_error("Failed to parse `%s`: Missing path for signal `%s`\n", filename.c_str(), signal_json.dump().c_str());
		if (!signal_json["width"].is_number())
			log_error("Failed to parse `%s`: Unknown width for signal `%s`\n", filename.c_str(), signal_json.dump().c_str());
		signal.width = signal_json["width"].int_value();
		if (signal.width < 0)
			log_error("Failed to parse `%s`: Invalid width for signal `%s`\n", filename.c_str(), signal_json.dump().c_str());
		bits_offset += signal.width;
		if (!signal_json["offset"].is_number())
			log_error("Failed to parse `%s`: Unknown offset for signal `%s`\n", filename.c_str(), signal_json.dump().c_str());
		signal.offset = signal_json["offset"].int_value();
		if (signal.offset < 0)
			log_error("Failed to parse `%s`: Invalid offset for signal `%s`\n", filename.c_str(), signal_json.dump().c_str());
		signal.init_only = signal_json["init_only"].bool_value();
		signals.push_back(signal);
	}

	for (auto &step_json : json["steps"].array_items()) {
		Step step;
		if (!step_json["bits"].is_string())
			log_error("Failed to parse `%s`: Expected string as bits value for step %d\n", filename.c_str(), GetSize(steps));
		step.bits = step_json["bits"].string_value();
		for (char c : step.bits) {
			if (c != '0' && c != '1' && c != 'x' && c != '?')
				log_error("Failed to parse `%s`: Invalid bit '%c' value for step %d\n", filename.c_str(), c, GetSize(steps));
		}
		steps.push_back(step);
	}
}

RTLIL::Const ReadWitness::get_bits(int t, int bits_offset, int width) const
{
	log_assert(t >= 0 && t < GetSize(steps));

	const std::string &bits = steps[t].bits;

	RTLIL::Const result(State::Sa, width);
	result.bits().reserve(width);

	int read_begin = GetSize(bits) - 1 - bits_offset;
	int read_end = max(-1, read_begin - width);

	for (int i = read_begin, j = 0; i > read_end; i--, j++) {
		RTLIL::State bit = State::Sa;
		switch (bits[i]) {
			case '0': bit = State::S0; break;
			case '1': bit = State::S1; break;
			case 'x': bit = State::Sx; break;
			case '?': bit = State::Sa; break;
			default:
				log_abort();
		}
		result.bits()[j] = bit;
	}

	return result;
}
