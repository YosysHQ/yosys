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

struct rules_t
{
	struct portinfo_t {
		int group, index;
		int wrmode, enable, transp, clocks, clkpol;
	};

	struct bram_t {
		IdString name;
		int groups, abits, dbits, init;
		vector<int> ports, wrmode, enable, transp, clocks, clkpol;

		vector<portinfo_t> make_portinfos() const
		{
			vector<portinfo_t> portinfos;
			for (int i = 0; i < groups && i < GetSize(ports); i++)
			for (int j = 0; j < ports[i]; j++) {
				portinfo_t pi;
				pi.group = i;
				pi.index = j;
				pi.wrmode = i < GetSize(wrmode) ? wrmode[i] : 0;
				pi.enable = i < GetSize(enable) ? enable[i] : 0;
				pi.transp = i < GetSize(transp) ? transp[i] : 0;
				pi.clocks = i < GetSize(clocks) ? clocks[i] : 0;
				pi.clkpol = i < GetSize(clkpol) ? clkpol[i] : 0;
				portinfos.push_back(pi);
			}
			return portinfos;
		}
	};

	struct match_t {
		IdString name;
		dict<string, int> min_limits, max_limits;
	};

	dict<IdString, bram_t> brams;
	vector<match_t> matches;

	std::ifstream infile;
	vector<string> tokens;
	int linecount;
	string line;

	void syntax_error()
	{
		if (line.empty())
			log_error("Unexpected end of rules file in line %d.\n", linecount);
		log_error("Syntax error in rules file line %d: %s\n", linecount, line.c_str());
	}

	bool next_line()
	{
		linecount++;
		tokens.clear();
		while (std::getline(infile, line)) {
			for (string tok = next_token(line); !tok.empty(); tok = next_token(line)) {
				if (tok[0] == '#')
					break;
				tokens.push_back(tok);
			}
			if (!tokens.empty())
				return true;
		}
		return false;
	}

	bool parse_single_int(const char *stmt, int &value)
	{
		if (GetSize(tokens) == 2 && tokens[0] == stmt) {
			value = atoi(tokens[1].c_str());
			return true;
		}
		return false;
	}

	bool parse_int_vect(const char *stmt, vector<int> &value)
	{
		if (GetSize(tokens) >= 2 && tokens[0] == stmt) {
			value.resize(GetSize(tokens)-1);
			for (int i = 1; i < GetSize(tokens); i++)
				value[i-1] = atoi(tokens[i].c_str());
			return true;
		}
		return false;
	}

	void parse_bram()
	{
		if (GetSize(tokens) != 2)
			syntax_error();

		bram_t data;
		data.name = RTLIL::escape_id(tokens[1]);

		while (next_line())
		{
			if (GetSize(tokens) == 1 && tokens[0] == "endbram") {
				brams[data.name] = data;
				return;
			}

			if (parse_single_int("groups", data.groups))
				continue;

			if (parse_single_int("abits", data.abits))
				continue;

			if (parse_single_int("dbits", data.dbits))
				continue;

			if (parse_single_int("init", data.init))
				continue;

			if (parse_int_vect("ports", data.ports))
				continue;

			if (parse_int_vect("wrmode", data.wrmode))
				continue;

			if (parse_int_vect("enable", data.enable))
				continue;

			if (parse_int_vect("transp", data.transp))
				continue;

			if (parse_int_vect("clocks", data.clocks))
				continue;

			if (parse_int_vect("clkpol", data.clkpol))
				continue;

			break;
		}

		syntax_error();
	}

	void parse_match()
	{
		if (GetSize(tokens) != 2)
			syntax_error();

		match_t data;
		data.name = RTLIL::escape_id(tokens[1]);

		while (next_line())
		{
			if (GetSize(tokens) == 1 && tokens[0] == "endmatch") {
				matches.push_back(data);
				return;
			}

			if (GetSize(tokens) == 3 && tokens[0] == "min") {
				data.min_limits[tokens[1]] = atoi(tokens[2].c_str());
				continue;
			}

			if (GetSize(tokens) == 3 && tokens[0] == "max") {
				data.max_limits[tokens[1]] = atoi(tokens[2].c_str());
				continue;
			}

			break;
		}

		syntax_error();
	}

	void parse(std::string filename)
	{
		infile.open(filename);
		linecount = 0;

		if (infile.fail())
			log_error("Can't open rules file `%s'.\n", filename.c_str());

		while (next_line())
		{
			if (tokens[0] == "bram") parse_bram();
			else if (tokens[0] == "match") parse_match();
			else syntax_error();
		}

		infile.close();
	}
};

bool replace_cell(Cell *cell, const rules_t::bram_t &bram, const rules_t::match_t&)
{
	auto portinfos = bram.make_portinfos();
	dict<int, pair<SigBit, bool>> clock_domains;
	vector<int> mapped_wr_ports;

	log("  Mapping to bram type %s:\n", log_id(bram.name));

	int wr_ports_n = cell->getParam("\\WR_PORTS").as_int();
	auto wr_clken = SigSpec(cell->getParam("\\WR_CLK_ENABLE"));
	auto wr_clkpol = SigSpec(cell->getParam("\\WR_CLK_POLARITY"));
	wr_clken.extend_u0(wr_ports_n);
	wr_clkpol.extend_u0(wr_ports_n);

	SigSpec wr_clk = cell->getPort("\\WR_CLK");
	SigSpec wr_en = cell->getPort("\\WR_EN");

	for (int cell_port_i = 0, bram_port_i = 0; cell_port_i < wr_ports_n; cell_port_i++)
	{
		bool clken = wr_clken[cell_port_i] == State::S1;
		auto clkpol = wr_clkpol[cell_port_i] == State::S1;
		auto clksig = wr_clk[cell_port_i];

		pair<SigBit, bool> clkdom(clksig, clkpol);
		if (!clken)
			clkdom = pair<SigBit, bool>(State::S1, false);

		log("    Write port #%d is in clock domain %s%s.\n",
				cell_port_i, clkdom.second ? "" : "!",
				clken ? log_signal(clkdom.first) : "~async~");

		for (; bram_port_i < GetSize(portinfos); bram_port_i++)
		{
			auto &pi = portinfos[bram_port_i];

			if (pi.wrmode != 1)
		skip_bram_wport:
				continue;

			if (clken) {
				if (pi.clocks == 0) {
					log("      Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
				if (clock_domains.count(pi.clocks) && clock_domains.at(pi.clocks) != clkdom) {
					log("      Bram port %c%d is in a different clock domain.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
			} else {
				if (pi.clocks != 0) {
					log("      Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
			}

			SigBit last_en_bit = State::S1;
			for (int i = 0; i < bram.dbits; i++) {
				if (pi.enable && i % (bram.dbits / pi.enable) == 0)
					last_en_bit = wr_en[i];
				if (last_en_bit != wr_en[i]) {
					log("      Bram port %c%d has incompatible enable structure.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
			}

			log("      Mapped to bram port %c%d.\n", pi.group + 'A', pi.index + 1);
			if (clken)
				clock_domains[pi.clocks] = clkdom;
			mapped_wr_ports.push_back(bram_port_i);
			goto mapped_port;
		}

		log("    Failed to map write port #%d.\n", cell_port_i);
		return false;
	mapped_port:;
	}

	log("  FIXME: The core of memory_bram is not implemented yet.\n");
	return false;
}

void handle_cell(Cell *cell, const rules_t &rules)
{
	log("Processing %s.%s:\n", log_id(cell->module), log_id(cell));

	dict<string, int> mem_properties;
	mem_properties["words"]  = cell->getParam("\\SIZE").as_int();
	mem_properties["abits"]  = cell->getParam("\\ABITS").as_int();
	mem_properties["dbits"]  = cell->getParam("\\WIDTH").as_int();
	mem_properties["wports"] = cell->getParam("\\WR_PORTS").as_int();
	mem_properties["rports"] = cell->getParam("\\RD_PORTS").as_int();
	mem_properties["bits"]   = mem_properties["words"] * mem_properties["dbits"];
	mem_properties["ports"]  = mem_properties["wports"] + mem_properties["rports"];

	log("  Properties:");
	for (auto &it : mem_properties)
		log(" %s=%d", it.first.c_str(), it.second);
	log("\n");

	pool<IdString> failed_brams;

	for (int i = 0; i < GetSize(rules.matches); i++)
	{
		if (rules.matches[i].name.in(failed_brams))
			continue;

		for (auto it : rules.matches[i].min_limits) {
			if (!mem_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(rules.matches[i].name));
			if (mem_properties[it.first] >= it.second)
				continue;
			log("  Rule #%d for bram type %s rejected: requirement 'min %s %d' not met.\n",
					i, log_id(rules.matches[i].name), it.first.c_str(), it.second);
			goto next_match_rule;
		}
		for (auto it : rules.matches[i].max_limits) {
			if (!mem_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(rules.matches[i].name));
			if (mem_properties[it.first] <= it.second)
				continue;
			log("  Rule #%d for bram type %s rejected: requirement 'max %s %d' not met.\n",
					i, log_id(rules.matches[i].name), it.first.c_str(), it.second);
			goto next_match_rule;
		}

		log("  Rule #%d for bram type %s accepted.\n", i, log_id(rules.matches[i].name));
		if (!rules.brams.count(rules.matches[i].name))
			log_error("No bram description for resource %s found!\n", log_id(rules.matches[i].name));

		if (!replace_cell(cell, rules.brams.at(rules.matches[i].name), rules.matches[i])) {
			log("  Mapping to bram type %s failed.\n", log_id(rules.matches[i].name));
			failed_brams.insert(rules.matches[i].name);
			goto next_match_rule;
		}
		return;

	next_match_rule:;
	}

	log("  No acceptable bram resources found.\n");
}

struct MemoryBramPass : public Pass {
	MemoryBramPass() : Pass("memory_bram", "map memories to block rams") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_bram -rules <rule_file> [selection]\n");
		log("\n");
		log("This pass converts the multi-port $mem memory cells into block ram instances.\n");
		log("The given rules file describes the available resources and how they should be\n");
		log("used.\n");
		log("\n");
	}
	virtual void execute(vector<string> args, Design *design)
	{
		rules_t rules;

		log_header("Executing MEMORY_BRAM pass (mapping $mem cells to block memories).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-rules" && argidx+1 < args.size()) {
				rules.parse(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
		for (auto cell : mod->selected_cells())
			if (cell->type == "$mem")
				handle_cell(cell, rules);
	}
} MemoryBramPass;

PRIVATE_NAMESPACE_END
