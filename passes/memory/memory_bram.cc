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
	vector<int> mapped_wr_ports, mapped_rd_ports;
	dict<int, int> used_rd_ports;
	int rd_port_dups = 1;

	log("  Mapping to bram type %s:\n", log_id(bram.name));

	int mem_size = cell->getParam("\\SIZE").as_int();
	int mem_abits = cell->getParam("\\ABITS").as_int();
	int mem_width = cell->getParam("\\WIDTH").as_int();
	int mem_offset = cell->getParam("\\OFFSET").as_int();

	int wr_ports = cell->getParam("\\WR_PORTS").as_int();
	auto wr_clken = SigSpec(cell->getParam("\\WR_CLK_ENABLE"));
	auto wr_clkpol = SigSpec(cell->getParam("\\WR_CLK_POLARITY"));
	wr_clken.extend_u0(wr_ports);
	wr_clkpol.extend_u0(wr_ports);

	SigSpec wr_en = cell->getPort("\\WR_EN");
	SigSpec wr_clk = cell->getPort("\\WR_CLK");
	SigSpec wr_data = cell->getPort("\\WR_DATA");
	SigSpec wr_addr = cell->getPort("\\WR_ADDR");

	int rd_ports = cell->getParam("\\RD_PORTS").as_int();
	auto rd_clken = SigSpec(cell->getParam("\\RD_CLK_ENABLE"));
	auto rd_clkpol = SigSpec(cell->getParam("\\RD_CLK_POLARITY"));
	auto rd_transp = SigSpec(cell->getParam("\\RD_TRANSPARENT"));
	rd_clken.extend_u0(rd_ports);
	rd_clkpol.extend_u0(rd_ports);
	rd_transp.extend_u0(rd_ports);

	SigSpec rd_clk = cell->getPort("\\RD_CLK");
	SigSpec rd_data = cell->getPort("\\RD_DATA");
	SigSpec rd_addr = cell->getPort("\\RD_ADDR");

	for (int cell_port_i = 0, bram_port_i = 0; cell_port_i < wr_ports; cell_port_i++)
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
			goto mapped_wr_port;
		}

		log("      Failed to map write port #%d.\n", cell_port_i);
		return false;
	mapped_wr_port:;
	}

	int grow_read_ports_cursor = -1;
	bool try_growing_more_read_ports = false;

	if (0) {
grow_read_ports:;
		rd_port_dups++;
		mapped_rd_ports.clear();
		used_rd_ports.clear();
	}

	for (int cell_port_i = 0; cell_port_i < rd_ports; cell_port_i++)
	{
		bool clken = rd_clken[cell_port_i] == State::S1;
		auto clkpol = rd_clkpol[cell_port_i] == State::S1;
		auto clksig = rd_clk[cell_port_i];

		pair<SigBit, bool> clkdom(clksig, clkpol);
		if (!clken)
			clkdom = pair<SigBit, bool>(State::S1, false);

		log("    Read port #%d is in clock domain %s%s.\n",
				cell_port_i, clkdom.second ? "" : "!",
				clken ? log_signal(clkdom.first) : "~async~");

		for (int bram_port_i = 0; bram_port_i < GetSize(portinfos); bram_port_i++)
		{
			auto &pi = portinfos[bram_port_i];

			if (pi.wrmode != 0 || used_rd_ports[bram_port_i] >= rd_port_dups)
		skip_bram_rport:
				continue;

			if (clken) {
				if (pi.clocks == 0) {
					log("      Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_rport;
				}
				if (clock_domains.count(pi.clocks) && clock_domains.at(pi.clocks) != clkdom) {
					log("      Bram port %c%d is in a different clock domain.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_rport;
				}
			} else {
				if (pi.clocks != 0) {
					log("      Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_rport;
				}
			}

			log("      Mapped to bram port %c%d.%d.\n", pi.group + 'A', pi.index + 1, used_rd_ports[bram_port_i] + 1);
			if (clken)
				clock_domains[pi.clocks] = clkdom;
			if (grow_read_ports_cursor < bram_port_i) {
				grow_read_ports_cursor = bram_port_i;
				try_growing_more_read_ports = true;
			}
			mapped_rd_ports.push_back(bram_port_i);
			used_rd_ports[bram_port_i]++;
			goto mapped_rd_port;
		}

		log("      Failed to map read port #%d.\n", cell_port_i);
		if (try_growing_more_read_ports) {
			log("    Growing more read ports by duplicating bram cells.\n");
			goto grow_read_ports;
		}
		return false;
	mapped_rd_port:;
	}

	log("    FIXME: The core of memory_bram is not implemented yet.\n");
	return false;
}

void handle_cell(Cell *cell, const rules_t &rules)
{
	log("Processing %s.%s:\n", log_id(cell->module), log_id(cell));

	dict<string, int> match_properties;
	match_properties["words"]  = cell->getParam("\\SIZE").as_int();
	match_properties["abits"]  = cell->getParam("\\ABITS").as_int();
	match_properties["dbits"]  = cell->getParam("\\WIDTH").as_int();
	match_properties["wports"] = cell->getParam("\\WR_PORTS").as_int();
	match_properties["rports"] = cell->getParam("\\RD_PORTS").as_int();
	match_properties["bits"]   = match_properties["words"] * match_properties["dbits"];
	match_properties["ports"]  = match_properties["wports"] + match_properties["rports"];

	log("  Properties:");
	for (auto &it : match_properties)
		log(" %s=%d", it.first.c_str(), it.second);
	log("\n");

	pool<IdString> failed_brams;

	for (int i = 0; i < GetSize(rules.matches); i++)
	{
		if (!rules.brams.count(rules.matches[i].name))
			log_error("No bram description for resource %s found!\n", log_id(rules.matches[i].name));

		auto &match = rules.matches.at(i);
		auto &bram = rules.brams.at(match.name);

		if (match.name.in(failed_brams))
			continue;

		int aover = match_properties["words"] % (1 << bram.abits);
		int awaste = aover ? (1 << bram.abits) - aover : 0;
		match_properties["awaste"] = awaste;

		int dover = match_properties["dbits"] % bram.dbits;
		int dwaste = dover ? bram.dbits - dover : 0;
		match_properties["dwaste"] = dwaste;

		int waste = awaste * bram.dbits + dwaste * (1 << bram.abits) - awaste * dwaste;
		match_properties["waste"] = waste;

		log("  Wasted bits for bram type %s: awaste=%d dwaste=%d waste=%d\n",
				log_id(match.name), awaste, dwaste, waste);

		for (auto it : match.min_limits) {
			if (!match_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(match.name));
			if (match_properties[it.first] >= it.second)
				continue;
			log("  Rule #%d for bram type %s rejected: requirement 'min %s %d' not met.\n",
					i, log_id(match.name), it.first.c_str(), it.second);
			goto next_match_rule;
		}
		for (auto it : match.max_limits) {
			if (!match_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(match.name));
			if (match_properties[it.first] <= it.second)
				continue;
			log("  Rule #%d for bram type %s rejected: requirement 'max %s %d' not met.\n",
					i, log_id(match.name), it.first.c_str(), it.second);
			goto next_match_rule;
		}

		log("  Rule #%d for bram type %s accepted.\n", i, log_id(match.name));

		if (!replace_cell(cell, bram, match)) {
			log("  Mapping to bram type %s failed.\n", log_id(match.name));
			failed_brams.insert(match.name);
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
