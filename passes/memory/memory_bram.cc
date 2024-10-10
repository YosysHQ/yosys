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
#include "kernel/mem.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct rules_t
{
	struct portinfo_t {
		int group, index, dupidx;
		int wrmode, enable, transp, clocks, clkpol;

		bool make_transp;
		bool make_outreg;
		int mapped_port;
	};

	struct bram_t {
		IdString name;
		int variant;

		int groups, abits, dbits, init;
		vector<int> ports, wrmode, enable, transp, clocks, clkpol;

		void dump_config() const
		{
			log("      bram %s # variant %d\n", log_id(name), variant);
			log("        init %d\n", init);
			log("        abits %d\n", abits);
			log("        dbits %d\n", dbits);
			log("        groups %d\n", groups);

			log("        ports "); for (int v : ports)  log("%4d", v); log("\n");
			log("        wrmode"); for (int v : wrmode) log("%4d", v); log("\n");
			log("        enable"); for (int v : enable) log("%4d", v); log("\n");
			log("        transp"); for (int v : transp) log("%4d", v); log("\n");
			log("        clocks"); for (int v : clocks) log("%4d", v); log("\n");
			log("        clkpol"); for (int v : clkpol) log("%4d", v); log("\n");
			log("      endbram\n");
		}

		void check_vectors() const
		{
			if (groups != GetSize(ports))  log_error("Bram %s variant %d has %d groups but only %d entries in 'ports'.\n",  log_id(name), variant, groups, GetSize(ports));
			if (groups != GetSize(wrmode)) log_error("Bram %s variant %d has %d groups but only %d entries in 'wrmode'.\n", log_id(name), variant, groups, GetSize(wrmode));
			if (groups != GetSize(enable)) log_error("Bram %s variant %d has %d groups but only %d entries in 'enable'.\n", log_id(name), variant, groups, GetSize(enable));
			if (groups != GetSize(transp)) log_error("Bram %s variant %d has %d groups but only %d entries in 'transp'.\n", log_id(name), variant, groups, GetSize(transp));
			if (groups != GetSize(clocks)) log_error("Bram %s variant %d has %d groups but only %d entries in 'clocks'.\n", log_id(name), variant, groups, GetSize(clocks));
			if (groups != GetSize(clkpol)) log_error("Bram %s variant %d has %d groups but only %d entries in 'clkpol'.\n", log_id(name), variant, groups, GetSize(clkpol));

			int group = 0;
			for (auto e : enable)
				if (e > dbits) log_error("Bram %s variant %d group %d has %d enable bits but only %d dbits.\n", log_id(name), variant, group, e, dbits);
		}

		vector<portinfo_t> make_portinfos() const
		{
			vector<portinfo_t> portinfos;
			for (int i = 0; i < groups; i++)
			for (int j = 0; j < ports[i]; j++) {
				portinfo_t pi;
				pi.group = i;
				pi.index = j;
				pi.dupidx = 0;
				pi.wrmode = wrmode[i];
				pi.enable = enable[i];
				pi.transp = transp[i];
				pi.clocks = clocks[i];
				pi.clkpol = clkpol[i];
				pi.mapped_port = -1;
				pi.make_transp = false;
				pi.make_outreg = false;
				portinfos.push_back(pi);
			}
			return portinfos;
		}

		void find_variant_params(dict<IdString, Const> &variant_params, const bram_t &other) const
		{
			log_assert(name == other.name);

			if (groups != other.groups)
				log_error("Bram %s variants %d and %d have different values for 'groups'.\n", log_id(name), variant, other.variant);

			if (abits != other.abits)
				variant_params[ID::CFG_ABITS] = abits;
			if (dbits != other.dbits)
				variant_params[ID::CFG_DBITS] = dbits;
			if (init != other.init)
				variant_params[ID::CFG_INIT] = init;

			for (int i = 0; i < groups; i++)
			{
				if (ports[i] != other.ports[i])
					log_error("Bram %s variants %d and %d have different number of %c-ports.\n", log_id(name), variant, other.variant, 'A'+i);
				if (wrmode[i] != other.wrmode[i])
					variant_params[stringf("\\CFG_WRMODE_%c", 'A' + i)] = wrmode[i];
				if (enable[i] != other.enable[i])
					variant_params[stringf("\\CFG_ENABLE_%c", 'A' + i)] = enable[i];
				if (transp[i] != other.transp[i])
					variant_params[stringf("\\CFG_TRANSP_%c", 'A' + i)] = transp[i];
				if (clocks[i] != other.clocks[i])
					variant_params[stringf("\\CFG_CLOCKS_%c", 'A' + i)] = clocks[i];
				if (clkpol[i] != other.clkpol[i])
					variant_params[stringf("\\CFG_CLKPOL_%c", 'A' + i)] = clkpol[i];
			}
		}
	};

	struct match_t {
		IdString name;
		dict<string, int> min_limits, max_limits;
		bool or_next_if_better, make_transp, make_outreg;
		char shuffle_enable;
		vector<vector<std::tuple<bool,IdString,Const>>> attributes;
	};

	bool attr_icase;
	dict<IdString, vector<bram_t>> brams;
	vector<match_t> matches;

	std::string map_case(std::string value) const
	{
		if (attr_icase) {
			for (char &c : value)
				c = tolower(c);
		}
		return value;
	}

	RTLIL::Const map_case(RTLIL::Const value) const
	{
		if (value.flags & RTLIL::CONST_FLAG_STRING)
			return map_case(value.decode_string());
		return value;
	}

	std::ifstream infile;
	vector<string> tokens;
	vector<string> labels;
	int linecount;

	void syntax_error()
	{
		if (tokens.empty())
			log_error("Unexpected end of rules file in line %d.\n", linecount);
		log_error("Syntax error in rules file line %d.\n", linecount);
	}

	bool next_line()
	{
		string line;
		while (std::getline(infile, line)) {
			tokens.clear();
			labels.clear();
			linecount++;
			for (string tok = next_token(line); !tok.empty(); tok = next_token(line)) {
				if (tok[0] == '@') {
					labels.push_back(tok.substr(1));
					continue;
				}
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
		IdString bram_name = RTLIL::escape_id(tokens[1]);

		if (GetSize(tokens) != 2)
			syntax_error();

		vector<vector<string>> lines_nolabels;
		std::map<string, vector<vector<string>>> lines_labels;

		while (next_line())
		{
			if (GetSize(tokens) == 1 && tokens[0] == "endbram")
				break;
			if (labels.empty())
				lines_nolabels.push_back(tokens);
			for (auto lab : labels)
				lines_labels[lab].push_back(tokens);
		}

		std::map<string, vector<vector<string>>> variant_lines;

		if (lines_labels.empty())
			variant_lines[""] = lines_nolabels;
		for (auto &it : lines_labels) {
			variant_lines[it.first] = lines_nolabels;
			variant_lines[it.first].insert(variant_lines[it.first].end(), it.second.begin(), it.second.end());
		}

		for (auto &it : variant_lines)
		{
			bram_t data;
			data.name = bram_name;
			data.variant = GetSize(brams[data.name]) + 1;
			data.groups = 0;
			data.abits = 0;
			data.dbits = 0;
			data.init = 0;

			for (auto &line_tokens : it.second)
			{
				tokens = line_tokens;

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

				syntax_error();
			}

			data.check_vectors();
			brams[data.name].push_back(data);
		}
	}

	void parse_match()
	{
		if (GetSize(tokens) != 2)
			syntax_error();

		match_t data;
		data.name = RTLIL::escape_id(tokens[1]);
		data.or_next_if_better = false;
		data.make_transp = false;
		data.make_outreg = false;
		data.shuffle_enable = 0;

		while (next_line())
		{
			if (!labels.empty())
				syntax_error();

			if (GetSize(tokens) == 1 && tokens[0] == "endmatch") {
				matches.push_back(data);
				break;
			}

			if (GetSize(tokens) == 3 && tokens[0] == "min") {
				data.min_limits[tokens[1]] = atoi(tokens[2].c_str());
				continue;
			}

			if (GetSize(tokens) == 3 && tokens[0] == "max") {
				data.max_limits[tokens[1]] = atoi(tokens[2].c_str());
				continue;
			}

			if (GetSize(tokens) == 2 && tokens[0] == "shuffle_enable" && GetSize(tokens[1]) == 1 && 'A' <= tokens[1][0] && tokens[1][0] <= 'Z') {
				data.shuffle_enable = tokens[1][0];
				continue;
			}

			if (GetSize(tokens) == 1 && tokens[0] == "make_transp") {
				data.make_transp = true;
				continue;
			}

			if (GetSize(tokens) == 1 && tokens[0] == "make_outreg") {
				data.make_transp = true;
				data.make_outreg = true;
				continue;
			}

			if (GetSize(tokens) == 1 && tokens[0] == "or_next_if_better") {
				data.or_next_if_better = true;
				continue;
			}

			if (GetSize(tokens) >= 2 && tokens[0] == "attribute") {
				data.attributes.emplace_back();
				for (int idx = 1; idx < GetSize(tokens); idx++) {
					size_t c1 = tokens[idx][0] == '!' ? 1 : 0;
					size_t c2 = tokens[idx].find("=");
					bool exists = (c1 == 0);
					IdString key = RTLIL::escape_id(tokens[idx].substr(c1, c2));
					Const val = c2 != std::string::npos ? tokens[idx].substr(c2+1) : RTLIL::Const(1);

					data.attributes.back().emplace_back(exists, key, map_case(val));
				}
				continue;
			}

			syntax_error();
		}
	}

	void parse(string filename)
	{
		rewrite_filename(filename);
		infile.open(filename);
		linecount = 0;
		attr_icase = false;

		if (infile.fail())
			log_error("Can't open rules file `%s'.\n", filename.c_str());

		while (next_line())
		{
			if (!labels.empty())
				syntax_error();

			if (GetSize(tokens) == 2 && tokens[0] == "attr_icase") {
				attr_icase = atoi(tokens[1].c_str());
				continue;
			}

			if (tokens[0] == "bram") {
				parse_bram();
				continue;
			}

			if (tokens[0] == "match") {
				parse_match();
				continue;
			}

			syntax_error();
		}

		infile.close();
	}
};

bool replace_memory(Mem &mem, const rules_t &rules, FfInitVals *initvals, const rules_t::bram_t &bram, const rules_t::match_t &match, dict<string, int> &match_properties, int mode)
{
	Module *module = mem.module;

	auto portinfos = bram.make_portinfos();
	int dup_count = 1;

	dict<int, pair<SigBit, bool>> clock_domains;
	dict<int, bool> clock_polarities;
	dict<int, bool> read_transp;
	pool<int> clocks_wr_ports;
	pool<int> clkpol_wr_ports;
	int clocks_max = 0;
	int clkpol_max = 0;
	int transp_max = 0;

	clock_polarities[0] = false;
	clock_polarities[1] = true;

	for (auto &pi : portinfos) {
		if (pi.wrmode) {
			clocks_wr_ports.insert(pi.clocks);
			if (pi.clkpol > 1)
				clkpol_wr_ports.insert(pi.clkpol);
		}
		clocks_max = max(clocks_max, pi.clocks);
		clkpol_max = max(clkpol_max, pi.clkpol);
		transp_max = max(transp_max, pi.transp);
	}

	log("    Mapping to bram type %s (variant %d):\n", log_id(bram.name), bram.variant);
	// bram.dump_config();

	std::vector<int> shuffle_map;
	if (match.shuffle_enable && bram.dbits >= portinfos.at(match.shuffle_enable - 'A').enable*2 && portinfos.at(match.shuffle_enable - 'A').enable > 0 && !mem.wr_ports.empty())
	{
		int bucket_size = bram.dbits / portinfos.at(match.shuffle_enable - 'A').enable;
		log("      Shuffle bit order to accommodate enable buckets of size %d..\n", bucket_size);

		// analyze enable structure

		std::vector<SigSpec> en_order;
		dict<SigSpec, vector<int>> bits_wr_en;

		for (int i = 0; i < mem.width; i++) {
			SigSpec sig;
			for (auto &port : mem.wr_ports)
				sig.append(port.en[i]);
			if (bits_wr_en.count(sig) == 0)
				en_order.push_back(sig);
			bits_wr_en[sig].push_back(i);
		}

		for (auto &it : en_order)
		{
			for (auto bit : bits_wr_en.at(it))
				shuffle_map.push_back(bit);

			while (GetSize(shuffle_map) % bucket_size)
				shuffle_map.push_back(-1);
		}

		log("      Results of bit order shuffling:");
		for (int v : shuffle_map)
			log(" %d", v);
		log("\n");

		// update mem_*, wr_*, and rd_* variables
	} else {
		for (int i = 0; i < mem.width; i++)
			shuffle_map.push_back(i);
	}

	// Align width up to dbits.
	while (GetSize(shuffle_map) % bram.dbits)
		shuffle_map.push_back(-1);

	// assign write ports
	pair<SigBit, bool> wr_clkdom;
	for (int cell_port_i = 0, bram_port_i = 0; cell_port_i < GetSize(mem.wr_ports); cell_port_i++)
	{
		auto &port = mem.wr_ports[cell_port_i];

		pair<SigBit, bool> clkdom(port.clk, port.clk_polarity);
		if (!port.clk_enable)
			clkdom = pair<SigBit, bool>(State::S1, false);
		wr_clkdom = clkdom;
		log("      Write port #%d is in clock domain %s%s.\n",
				cell_port_i, clkdom.second ? "" : "!",
				port.clk_enable ? log_signal(clkdom.first) : "~async~");

		for (; bram_port_i < GetSize(portinfos); bram_port_i++)
		{
			auto &pi = portinfos[bram_port_i];

			if (pi.wrmode != 1)
		skip_bram_wport:
				continue;

			if (port.clk_enable) {
				if (pi.clocks == 0) {
					log("        Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
				if (clock_domains.count(pi.clocks) && clock_domains.at(pi.clocks) != clkdom) {
					log("        Bram port %c%d is in a different clock domain.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
				if (clock_polarities.count(pi.clkpol) && clock_polarities.at(pi.clkpol) != port.clk_polarity) {
					log("        Bram port %c%d has incompatible clock polarity.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
			} else {
				if (pi.clocks != 0) {
					log("        Bram port %c%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1);
					goto skip_bram_wport;
				}
			}

			// We need to check enable compatibility of this port, as well as all
			// ports that have priority over this one (because they will be involved
			// in emulate_priority logic).

			for (int i = 0; i < GetSize(mem.wr_ports); i++) {
				auto &oport = mem.wr_ports[i];
				if (i != cell_port_i && !oport.priority_mask[cell_port_i])
					continue;
				SigBit last_en_bit = State::S1;
				for (int j = 0; j < GetSize(shuffle_map); j++) {
					if (shuffle_map[j] == -1)
						continue;
					SigBit en_bit = oport.en[shuffle_map[j]];
					if (pi.enable && j % (bram.dbits / pi.enable) == 0)
						last_en_bit = en_bit;
					if (last_en_bit != en_bit) {
						log("        Bram port %c%d has incompatible enable structure.\n", pi.group + 'A', pi.index + 1);
						goto skip_bram_wport;
					}
				}
			}

			log("        Mapped to bram port %c%d.\n", pi.group + 'A', pi.index + 1);
			pi.mapped_port = cell_port_i;

			if (port.clk_enable) {
				clock_domains[pi.clocks] = clkdom;
				clock_polarities[pi.clkpol] = clkdom.second;
			}

			bram_port_i++;
			goto mapped_wr_port;
		}

		log("        Failed to map write port #%d.\n", cell_port_i);
		return false;
	mapped_wr_port:;
	}

	// housekeeping stuff for growing more read ports and restarting read port assignments

	int grow_read_ports_cursor = -1;
	bool try_growing_more_read_ports = false;
	auto backup_clock_domains = clock_domains;
	auto backup_clock_polarities = clock_polarities;

	if (0) {
grow_read_ports:;
		vector<rules_t::portinfo_t> new_portinfos;
		for (auto &pi : portinfos) {
			if (pi.wrmode == 0) {
				pi.mapped_port = -1;
				pi.make_outreg = false;
				pi.make_transp = false;
			}
			new_portinfos.push_back(pi);
			if (pi.dupidx == dup_count-1) {
				if (pi.clocks && !clocks_wr_ports[pi.clocks])
					pi.clocks += clocks_max;
				if (pi.clkpol > 1 && !clkpol_wr_ports[pi.clkpol])
					pi.clkpol += clkpol_max;
				if (pi.transp > 1)
					pi.transp += transp_max;
				pi.dupidx++;
				new_portinfos.push_back(pi);
			}
		}
		try_growing_more_read_ports = false;
		portinfos.swap(new_portinfos);
		clock_domains = backup_clock_domains;
		clock_polarities = backup_clock_polarities;
		dup_count++;
	}

	read_transp.clear();
	read_transp[0] = false;
	read_transp[1] = true;

	// assign read ports

	for (int cell_port_i = 0; cell_port_i < GetSize(mem.rd_ports); cell_port_i++)
	{
		auto &port = mem.rd_ports[cell_port_i];
		bool transp = false;
		bool non_transp = false;

		if (port.clk_enable) {
			for (int i = 0; i < GetSize(mem.wr_ports); i++)
				if (port.transparency_mask[i])
					transp = true;
				else if (!port.collision_x_mask[i])
					non_transp = true;
		}

		pair<SigBit, bool> clkdom(port.clk, port.clk_polarity);
		if (!port.clk_enable)
			clkdom = pair<SigBit, bool>(State::S1, false);

		log("      Read port #%d is in clock domain %s%s.\n",
				cell_port_i, clkdom.second ? "" : "!",
				port.clk_enable ? log_signal(clkdom.first) : "~async~");

		for (int bram_port_i = 0; bram_port_i < GetSize(portinfos); bram_port_i++)
		{
			auto &pi = portinfos[bram_port_i];

			if (pi.wrmode != 0 || pi.mapped_port >= 0)
		skip_bram_rport:
				continue;

			if (port.clk_enable) {
				if (pi.clocks == 0) {
					if (match.make_outreg) {
						pi.make_outreg = true;
						goto skip_bram_rport_clkcheck;
					}
					log("        Bram port %c%d.%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
					goto skip_bram_rport;
				}
				if (clock_domains.count(pi.clocks) && clock_domains.at(pi.clocks) != clkdom) {
					log("        Bram port %c%d.%d is in a different clock domain.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
					goto skip_bram_rport;
				}
				if (clock_polarities.count(pi.clkpol) && clock_polarities.at(pi.clkpol) != port.clk_polarity) {
					log("        Bram port %c%d.%d has incompatible clock polarity.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
					goto skip_bram_rport;
				}
				if (non_transp && read_transp.count(pi.transp) && read_transp.at(pi.transp)) {
					log("        Bram port %c%d.%d has incompatible read transparency.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
					goto skip_bram_rport;
				}
				if (transp && (non_transp || (read_transp.count(pi.transp) && !read_transp.at(pi.transp)))) {
					if (match.make_transp) {
						pi.make_transp = true;
					} else {
						log("        Bram port %c%d.%d has incompatible read transparency.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
						goto skip_bram_rport;
					}
				}
			} else {
				if (pi.clocks != 0) {
					log("        Bram port %c%d.%d has incompatible clock type.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
					goto skip_bram_rport;
				}
			}

		skip_bram_rport_clkcheck:
			log("        Mapped to bram port %c%d.%d.\n", pi.group + 'A', pi.index + 1, pi.dupidx + 1);
			pi.mapped_port = cell_port_i;

			if (pi.clocks) {
				clock_domains[pi.clocks] = clkdom;
				clock_polarities[pi.clkpol] = clkdom.second;
				if (non_transp)
					read_transp[pi.transp] = false;
				if (transp && !pi.make_transp)
					read_transp[pi.transp] = true;
			}

			if (grow_read_ports_cursor < cell_port_i) {
				grow_read_ports_cursor = cell_port_i;
				try_growing_more_read_ports = true;
			}

			goto mapped_rd_port;
		}

		log("        Failed to map read port #%d.\n", cell_port_i);
		if (try_growing_more_read_ports) {
			log("      Growing more read ports by duplicating bram cells.\n");
			goto grow_read_ports;
		}
		return false;
	mapped_rd_port:;
	}

	// update properties and re-check conditions

	int dcells = GetSize(shuffle_map) / bram.dbits;
	int acells = (mem.size + (1 << bram.abits) - 1) / (1 << bram.abits);
	if (mode <= 1)
	{
		match_properties["dups"] = dup_count;
		match_properties["waste"] = match_properties["dups"] * match_properties["bwaste"];

		int cells = dcells * acells;
		match_properties["efficiency"] = (100 * match_properties["bits"]) / (dup_count * cells * bram.dbits * (1 << bram.abits));

		match_properties["dcells"] = dcells;
		match_properties["acells"] = acells;
		match_properties["cells"] = cells * dup_count;

		log("      Updated properties: dups=%d waste=%d efficiency=%d\n",
				match_properties["dups"], match_properties["waste"], match_properties["efficiency"]);

		for (auto it : match.min_limits) {
			if (!match_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(match.name));
			if (match_properties[it.first] >= it.second)
				continue;
			log("    Rule for bram type %s rejected: requirement 'min %s %d' not met.\n",
					log_id(match.name), it.first.c_str(), it.second);
			return false;
		}
		for (auto it : match.max_limits) {
			if (!match_properties.count(it.first))
				log_error("Unknown property '%s' in match rule for bram type %s.\n",
						it.first.c_str(), log_id(match.name));
			if (match_properties[it.first] <= it.second)
				continue;
			log("    Rule for bram type %s rejected: requirement 'max %s %d' not met.\n",
					log_id(match.name), it.first.c_str(), it.second);
			return false;
		}

		for (const auto &sums : match.attributes) {
			bool found = false;
			for (const auto &term : sums) {
				bool exists = std::get<0>(term);
				IdString key = std::get<1>(term);
				const Const &value = std::get<2>(term);
				auto it = mem.attributes.find(key);
				if (it == mem.attributes.end()) {
					if (exists)
						continue;
					found = true;
					break;
				}
				else if (!exists)
					continue;
				if (rules.map_case(it->second) != value)
					continue;
				found = true;
				break;
			}
			if (!found) {
				std::stringstream ss;
				bool exists = std::get<0>(sums.front());
				if (!exists)
					ss << "!";
				IdString key = std::get<1>(sums.front());
				ss << log_id(key);
				const Const &value = rules.map_case(std::get<2>(sums.front()));
				if (exists && value != Const(1))
					ss << "=\"" << value.decode_string() << "\"";

				log("    Rule for bram type %s rejected: requirement 'attribute %s ...' not met.\n",
						log_id(match.name), ss.str().c_str());
				return false;
			}
		}

		if (mode == 1)
			return true;
	}

	// At this point we are commited to replacing the RAM, and can mutate mem.

	// Apply make_outreg and make_transp where necessary.
	for (auto &pi : portinfos) {
		if (pi.mapped_port == -1 || pi.wrmode)
			continue;
		auto &port = mem.rd_ports[pi.mapped_port];
		if (pi.make_outreg) {
			mem.extract_rdff(pi.mapped_port, initvals);
		} else if (port.clk_enable) {
			if (!pi.enable && port.en != State::S1)
				mem.emulate_rden(pi.mapped_port, initvals);
			else
				mem.emulate_reset(pi.mapped_port, true, true, true, initvals);
		}
		if (pi.make_transp) {
			for (int i = 0; i < GetSize(mem.wr_ports); i++)
				if (port.transparency_mask[i])
					mem.emulate_transparency(i, pi.mapped_port, initvals);
		}
	}

	// We don't really support priorities, emulate them.
	for (int i = 0; i < GetSize(mem.wr_ports); i++)
		for (int j = 0; j < i; j++)
			mem.emulate_priority(j, i, initvals);

	// Swizzle the init data.  Do this before changing mem.width, so that get_init_data works.
	bool cell_init = !mem.inits.empty();
	vector<Const> initdata;
	if (cell_init) {
		Const initparam = mem.get_init_data();
		initdata.reserve(mem.size);
		for (int i = 0; i < mem.size; i++) {
			std::vector<State> val;
			for (auto idx : shuffle_map) {
				if (idx == -1)
					val.push_back(State::Sx);
				else
					val.push_back(initparam[mem.width * i + idx]);
			}
			initdata.push_back(Const(val));
		}
	}

	// Now the big swizzle.
	mem.width = GetSize(shuffle_map);

	// Swizzle write ports.
	for (auto &port : mem.wr_ports) {
		SigSpec new_en, new_data;
		SigBit en_bit = State::S1;
		for (auto idx : shuffle_map) {
			if (idx == -1) {
				new_data.append(State::Sx);
			} else {
				new_data.append(port.data[idx]);
				en_bit = port.en[idx];
			}
			new_en.append(en_bit);
		}
		port.en = new_en;
		port.data = new_data;
	}

	// Swizzle read ports.
	for (auto &port : mem.rd_ports) {
		SigSpec new_data = module->addWire(NEW_ID, mem.width);
		Const new_init_value = Const(State::Sx, mem.width);
		Const new_arst_value = Const(State::Sx, mem.width);
		Const new_srst_value = Const(State::Sx, mem.width);
		for (int i = 0; i < mem.width; i++)
			if (shuffle_map[i] != -1) {
				module->connect(port.data[shuffle_map[i]], new_data[i]);
				new_init_value.bits()[i] = port.init_value[shuffle_map[i]];
				new_arst_value.bits()[i] = port.arst_value[shuffle_map[i]];
				new_srst_value.bits()[i] = port.srst_value[shuffle_map[i]];
			}
		port.data = new_data;
		port.init_value = new_init_value;
		port.arst_value = new_arst_value;
		port.srst_value = new_srst_value;
	}

	// prepare variant parameters

	dict<IdString, Const> variant_params;
	for (auto &other_bram : rules.brams.at(bram.name))
		bram.find_variant_params(variant_params, other_bram);

	// actually replace that memory cell

	dict<SigSpec, pair<SigSpec, SigSpec>> dout_cache;

	for (int grid_d = 0; grid_d < dcells; grid_d++)
	{
		for (int grid_a = 0; grid_a < acells; grid_a++)
		for (int dupidx = 0; dupidx < dup_count; dupidx++)
		{
			Cell *c = module->addCell(module->uniquify(stringf("%s.%d.%d.%d", mem.memid.c_str(), grid_d, grid_a, dupidx)), bram.name);
			log("      Creating %s cell at grid position <%d %d %d>: %s\n", log_id(bram.name), grid_d, grid_a, dupidx, log_id(c));

			for (auto &vp : variant_params)
				c->setParam(vp.first, vp.second);

			if (cell_init) {
				int init_offset = grid_a*(1 << bram.abits) - mem.start_offset;
				int init_shift = grid_d*bram.dbits;
				int init_size = (1 << bram.abits);
				Const initparam(State::Sx, init_size*bram.dbits);
				for (int i = 0; i < init_size; i++)
					for (int j = 0; j < bram.dbits; j++)
						if (init_offset+i < GetSize(initdata) && init_offset+i >= 0)
							initparam.bits()[i*bram.dbits+j] = initdata[init_offset+i][init_shift+j];
						else
							initparam.bits()[i*bram.dbits+j] = State::Sx;
				c->setParam(ID::INIT, initparam);
			}

			for (auto &pi : portinfos)
			{
				if (pi.dupidx != dupidx)
					continue;

				string prefix = stringf("%c%d", pi.group + 'A', pi.index + 1);
				const char *pf = prefix.c_str();

				if (pi.clocks && clock_domains.count(pi.clocks))
					c->setPort(stringf("\\CLK%d", (pi.clocks-1) % clocks_max + 1), clock_domains.at(pi.clocks).first);
				if (pi.clkpol > 1 && clock_polarities.count(pi.clkpol))
					c->setParam(stringf("\\CLKPOL%d", (pi.clkpol-1) % clkpol_max + 1), clock_polarities.at(pi.clkpol));
				if (pi.transp > 1 && read_transp.count(pi.transp))
					c->setParam(stringf("\\TRANSP%d", (pi.transp-1) % transp_max + 1), read_transp.at(pi.transp));

				SigSpec addr_ok;
				SigSpec sig_addr;
				if (pi.mapped_port >= 0) {
					if (pi.wrmode == 1)
						sig_addr = mem.wr_ports[pi.mapped_port].addr;
					else
						sig_addr = mem.rd_ports[pi.mapped_port].addr;
				}

				if (GetSize(sig_addr) > bram.abits) {
					SigSpec extra_addr = sig_addr.extract(bram.abits, GetSize(sig_addr) - bram.abits);
					SigSpec extra_addr_sel = SigSpec(grid_a, GetSize(extra_addr));
					addr_ok = module->Eq(NEW_ID, extra_addr, extra_addr_sel);
				}

				sig_addr.extend_u0(bram.abits);
				c->setPort(stringf("\\%sADDR", pf), sig_addr);

				if (pi.wrmode == 1) {
					if (pi.mapped_port == -1)
					{
						if (pi.enable)
							c->setPort(stringf("\\%sEN", pf), Const(State::S0, pi.enable));
						continue;
					}

					auto &port = mem.wr_ports[pi.mapped_port];
					SigSpec sig_data = port.data.extract(grid_d * bram.dbits, bram.dbits);
					c->setPort(stringf("\\%sDATA", pf), sig_data);

					if (pi.enable)
					{
						SigSpec sig_en;
						int stride = bram.dbits / pi.enable;
						for (int i = 0; i < pi.enable; i++)
							sig_en.append(port.en[stride * i + grid_d * bram.dbits]);

						if (!addr_ok.empty())
							sig_en = module->Mux(NEW_ID, SigSpec(0, GetSize(sig_en)), sig_en, addr_ok);

						c->setPort(stringf("\\%sEN", pf), sig_en);

					}
				} else {
					if (pi.mapped_port == -1)
					{
						if (pi.enable)
							c->setPort(stringf("\\%sEN", pf), State::S0);
						continue;
					}
					auto &port = mem.rd_ports[pi.mapped_port];
					SigSpec sig_data = port.data.extract(grid_d * bram.dbits, bram.dbits);

					SigSpec bram_dout = module->addWire(NEW_ID, bram.dbits);
					c->setPort(stringf("\\%sDATA", pf), bram_dout);

					SigSpec addr_ok_q = addr_ok;
					if (port.clk_enable && !addr_ok.empty()) {
						addr_ok_q = module->addWire(NEW_ID);
						module->addDffe(NEW_ID, port.clk, port.en, addr_ok, addr_ok_q, port.clk_polarity);
					}

					dout_cache[sig_data].first.append(addr_ok_q);
					dout_cache[sig_data].second.append(bram_dout);

					if (pi.enable) {
						SigSpec sig_en = port.en;
						if (!addr_ok.empty())
							sig_en = module->And(NEW_ID, sig_en, addr_ok);
						c->setPort(stringf("\\%sEN", pf), sig_en);
					}
				}
			}
		}
	}

	for (auto &it : dout_cache)
	{
		if (it.second.first.empty())
		{
			log_assert(GetSize(it.first) == GetSize(it.second.second));
			module->connect(it.first, it.second.second);
		}
		else
		{
			log_assert(GetSize(it.first)*GetSize(it.second.first) == GetSize(it.second.second));
			module->addPmux(NEW_ID, SigSpec(State::Sx, GetSize(it.first)), it.second.second, it.second.first, it.first);
		}
	}

	mem.remove();
	return true;
}

void handle_memory(Mem &mem, const rules_t &rules, FfInitVals *initvals)
{
	log("Processing %s.%s:\n", log_id(mem.module), log_id(mem.memid));
	mem.narrow();

	bool cell_init = !mem.inits.empty();

	dict<string, int> match_properties;
	match_properties["words"]  = mem.size;
	match_properties["abits"]  = ceil_log2(mem.size);
	match_properties["dbits"]  = mem.width;
	match_properties["wports"] = GetSize(mem.wr_ports);
	match_properties["rports"] = GetSize(mem.rd_ports);
	match_properties["bits"]   = match_properties["words"] * match_properties["dbits"];
	match_properties["ports"]  = match_properties["wports"] + match_properties["rports"];

	log("  Properties:");
	for (auto &it : match_properties)
		log(" %s=%d", it.first.c_str(), it.second);
	log("\n");

	pool<pair<IdString, int>> failed_brams;
	dict<pair<int, int>, tuple<int, int, int>> best_rule_cache;

	for (int i = 0; i < GetSize(rules.matches); i++)
	{
		auto &match = rules.matches.at(i);

		if (!rules.brams.count(rules.matches[i].name))
			log_error("No bram description for resource %s found!\n", log_id(rules.matches[i].name));

		for (int vi = 0; vi < GetSize(rules.brams.at(match.name)); vi++)
		{
			auto &bram = rules.brams.at(match.name).at(vi);
			bool or_next_if_better = match.or_next_if_better || vi+1 < GetSize(rules.brams.at(match.name));

			int avail_rd_ports = 0;
			int avail_wr_ports = 0;
			for (int j = 0; j < bram.groups; j++) {
				if (GetSize(bram.wrmode) < j || bram.wrmode.at(j) == 0)
					avail_rd_ports += GetSize(bram.ports) < j ? bram.ports.at(j) : 0;
				if (GetSize(bram.wrmode) < j || bram.wrmode.at(j) != 0)
					avail_wr_ports += GetSize(bram.ports) < j ? bram.ports.at(j) : 0;
			}

			log("  Checking rule #%d for bram type %s (variant %d):\n", i+1, log_id(bram.name), bram.variant);
			log("    Bram geometry: abits=%d dbits=%d wports=%d rports=%d\n", bram.abits, bram.dbits, avail_wr_ports, avail_rd_ports);

			int dups = avail_rd_ports ? (match_properties["rports"] + avail_rd_ports - 1) / avail_rd_ports : 1;
			match_properties["dups"] = dups;

			log("    Estimated number of duplicates for more read ports: dups=%d\n", match_properties["dups"]);

			int aover = match_properties["words"] % (1 << bram.abits);
			int awaste = aover ? (1 << bram.abits) - aover : 0;
			match_properties["awaste"] = awaste;

			int dover = match_properties["dbits"] % bram.dbits;
			int dwaste = dover ? bram.dbits - dover : 0;
			match_properties["dwaste"] = dwaste;

			int bwaste = awaste * bram.dbits + dwaste * (1 << bram.abits) - awaste * dwaste;
			match_properties["bwaste"] = bwaste;

			int waste = match_properties["dups"] * bwaste;
			match_properties["waste"] = waste;

			int cells = ((match_properties["dbits"] + bram.dbits - 1) / bram.dbits) * ((match_properties["words"] + (1 << bram.abits) - 1) / (1 << bram.abits));
			int efficiency = (100 * match_properties["bits"]) / (dups * cells * bram.dbits * (1 << bram.abits));
			match_properties["efficiency"] = efficiency;

			if (failed_brams.count(pair<IdString, int>(bram.name, bram.variant)))
				goto next_match_rule;

			log("    Metrics for %s: awaste=%d dwaste=%d bwaste=%d waste=%d efficiency=%d\n",
					log_id(match.name), awaste, dwaste, bwaste, waste, efficiency);

			if (cell_init && bram.init == 0) {
				log("    Rule #%d for bram type %s (variant %d) rejected: cannot be initialized.\n",
						i+1, log_id(bram.name), bram.variant);
				goto next_match_rule;
			}

			for (auto it : match.min_limits) {
				if (it.first == "waste" || it.first == "dups" || it.first == "acells" || it.first == "dcells" || it.first == "cells")
					continue;
				if (!match_properties.count(it.first))
					log_error("Unknown property '%s' in match rule for bram type %s.\n",
							it.first.c_str(), log_id(match.name));
				if (match_properties[it.first] >= it.second)
					continue;
				log("    Rule #%d for bram type %s (variant %d) rejected: requirement 'min %s %d' not met.\n",
						i+1, log_id(bram.name), bram.variant, it.first.c_str(), it.second);
				goto next_match_rule;
			}

			for (auto it : match.max_limits) {
				if (it.first == "acells" || it.first == "dcells" || it.first == "cells")
					continue;
				if (!match_properties.count(it.first))
					log_error("Unknown property '%s' in match rule for bram type %s.\n",
							it.first.c_str(), log_id(match.name));
				if (match_properties[it.first] <= it.second)
					continue;
				log("    Rule #%d for bram type %s (variant %d) rejected: requirement 'max %s %d' not met.\n",
						i+1, log_id(bram.name), bram.variant, it.first.c_str(), it.second);
				goto next_match_rule;
			}

			for (const auto &sums : match.attributes) {
				bool found = false;
				for (const auto &term : sums) {
					bool exists = std::get<0>(term);
					IdString key = std::get<1>(term);
					const Const &value = std::get<2>(term);
					auto it = mem.attributes.find(key);
					if (it == mem.attributes.end()) {
						if (exists)
							continue;
						found = true;
						break;
					}
					else if (!exists)
						continue;
					if (rules.map_case(it->second) != value)
						continue;
					found = true;
					break;
				}
				if (!found) {
					std::stringstream ss;
					bool exists = std::get<0>(sums.front());
					if (!exists)
						ss << "!";
					IdString key = std::get<1>(sums.front());
					ss << log_id(key);
					const Const &value = rules.map_case(std::get<2>(sums.front()));
					if (exists && value != Const(1))
						ss << "=\"" << value.decode_string() << "\"";

					log("    Rule for bram type %s (variant %d) rejected: requirement 'attribute %s ...' not met.\n",
							log_id(bram.name), bram.variant, ss.str().c_str());
					goto next_match_rule;
				}
			}

			log("    Rule #%d for bram type %s (variant %d) accepted.\n", i+1, log_id(bram.name), bram.variant);

			if (or_next_if_better || !best_rule_cache.empty())
			{
				if (or_next_if_better && i+1 == GetSize(rules.matches) && vi+1 == GetSize(rules.brams.at(match.name)))
					log_error("Found 'or_next_if_better' in last match rule.\n");

				if (!replace_memory(mem, rules, initvals, bram, match, match_properties, 1)) {
					log("    Mapping to bram type %s failed.\n", log_id(match.name));
					failed_brams.insert(pair<IdString, int>(bram.name, bram.variant));
					goto next_match_rule;
				}

				log("      Storing for later selection.\n");
				best_rule_cache[pair<int, int>(i, vi)] = tuple<int, int, int>(match_properties["efficiency"], -match_properties["cells"], -match_properties["acells"]);

		next_match_rule:
				if (or_next_if_better || best_rule_cache.empty())
					continue;

				log("  Selecting best of %d rules:\n", GetSize(best_rule_cache));
				pair<int, int> best_rule = best_rule_cache.begin()->first;

				for (auto &it : best_rule_cache) {
					if (it.second > best_rule_cache[best_rule])
						best_rule = it.first;
					log("    Efficiency for rule %d.%d: efficiency=%d, cells=%d, acells=%d\n", it.first.first+1, it.first.second+1,
							std::get<0>(it.second), -std::get<1>(it.second), -std::get<2>(it.second));
				}

				log("    Selected rule %d.%d with efficiency %d.\n", best_rule.first+1, best_rule.second+1, std::get<0>(best_rule_cache[best_rule]));
				best_rule_cache.clear();

				auto &best_bram = rules.brams.at(rules.matches.at(best_rule.first).name).at(best_rule.second);
				if (!replace_memory(mem, rules, initvals, best_bram, rules.matches.at(best_rule.first), match_properties, 2))
					log_error("Mapping to bram type %s (variant %d) after pre-selection failed.\n", log_id(best_bram.name), best_bram.variant);
				return;
			}

			if (!replace_memory(mem, rules, initvals, bram, match, match_properties, 0)) {
				log("    Mapping to bram type %s failed.\n", log_id(match.name));
				failed_brams.insert(pair<IdString, int>(bram.name, bram.variant));
				goto next_match_rule;
			}
			return;
		}
	}

	log("  No acceptable bram resources found.\n");
}

struct MemoryBramPass : public Pass {
	MemoryBramPass() : Pass("memory_bram", "map memories to block rams") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_bram -rules <rule_file> [selection]\n");
		log("\n");
		log("This pass converts the multi-port $mem memory cells into block ram instances.\n");
		log("The given rules file describes the available resources and how they should be\n");
		log("used.\n");
		log("\n");
		log("The rules file contains configuration options, a set of block ram description\n");
		log("and a sequence of match rules.\n");
		log("\n");
		log("The option 'attr_icase' configures how attribute values are matched. The value 0\n");
		log("means case-sensitive, 1 means case-insensitive.\n");
		log("\n");
		log("A block ram description looks like this:\n");
		log("\n");
		log("    bram RAMB1024X32     # name of BRAM cell\n");
		log("      init 1             # set to '1' if BRAM can be initialized\n");
		log("      abits 10           # number of address bits\n");
		log("      dbits 32           # number of data bits\n");
		log("      groups 2           # number of port groups\n");
		log("      ports  1 1         # number of ports in each group\n");
		log("      wrmode 1 0         # set to '1' if this groups is write ports\n");
		log("      enable 4 1         # number of enable bits\n");
		log("      transp 0 2         # transparent (for read ports)\n");
		log("      clocks 1 2         # clock configuration\n");
		log("      clkpol 2 2         # clock polarity configuration\n");
		log("    endbram\n");
		log("\n");
		log("For the option 'transp' the value 0 means non-transparent, 1 means transparent\n");
		log("and a value greater than 1 means configurable. All groups with the same\n");
		log("value greater than 1 share the same configuration bit.\n");
		log("\n");
		log("For the option 'clocks' the value 0 means non-clocked, and a value greater\n");
		log("than 0 means clocked. All groups with the same value share the same clock\n");
		log("signal.\n");
		log("\n");
		log("For the option 'clkpol' the value 0 means negative edge, 1 means positive edge\n");
		log("and a value greater than 1 means configurable. All groups with the same value\n");
		log("greater than 1 share the same configuration bit.\n");
		log("\n");
		log("Using the same bram name in different bram blocks will create different variants\n");
		log("of the bram. Verilog configuration parameters for the bram are created as\n");
		log("needed.\n");
		log("\n");
		log("It is also possible to create variants by repeating statements in the bram block\n");
		log("and appending '@<label>' to the individual statements.\n");
		log("\n");
		log("A match rule looks like this:\n");
		log("\n");
		log("    match RAMB1024X32\n");
		log("      max waste 16384    # only use this bram if <= 16k ram bits are unused\n");
		log("      min efficiency 80  # only use this bram if efficiency is at least 80%%\n");
		log("    endmatch\n");
		log("\n");
		log("It is possible to match against the following values with min/max rules:\n");
		log("\n");
		log("    words  ........  number of words in memory in design\n");
		log("    abits  ........  number of address bits on memory in design\n");
		log("    dbits  ........  number of data bits on memory in design\n");
		log("    wports  .......  number of write ports on memory in design\n");
		log("    rports  .......  number of read ports on memory in design\n");
		log("    ports  ........  number of ports on memory in design\n");
		log("    bits  .........  number of bits in memory in design\n");
		log("    dups ..........  number of duplications for more read ports\n");
		log("\n");
		log("    awaste  .......  number of unused address slots for this match\n");
		log("    dwaste  .......  number of unused data bits for this match\n");
		log("    bwaste  .......  number of unused bram bits for this match\n");
		log("    waste  ........  total number of unused bram bits (bwaste*dups)\n");
		log("    efficiency  ...  total percentage of used and non-duplicated bits\n");
		log("\n");
		log("    acells  .......  number of cells in 'address-direction'\n");
		log("    dcells  .......  number of cells in 'data-direction'\n");
		log("    cells  ........  total number of cells (acells*dcells*dups)\n");
		log("\n");
		log("A match containing the command 'attribute' followed by a list of space\n");
		log("separated 'name[=string_value]' values requires that the memory contains any\n");
		log("one of the given attribute name and string values (where specified), or name\n");
		log("and integer 1 value (if no string_value given, since Verilog will interpret\n");
		log("'(* attr *)' as '(* attr=1 *)').\n");
		log("A name prefixed with '!' indicates that the attribute must not exist.\n");
		log("\n");
		log("The interface for the created bram instances is derived from the bram\n");
		log("description. Use 'techmap' to convert the created bram instances into\n");
		log("instances of the actual bram cells of your target architecture.\n");
		log("\n");
		log("A match containing the command 'or_next_if_better' is only used if it\n");
		log("has a higher efficiency than the next match (and the one after that if\n");
		log("the next also has 'or_next_if_better' set, and so forth).\n");
		log("\n");
		log("A match containing the command 'make_transp' will add external circuitry\n");
		log("to simulate 'transparent read', if necessary.\n");
		log("\n");
		log("A match containing the command 'make_outreg' will add external flip-flops\n");
		log("to implement synchronous read ports, if necessary.\n");
		log("\n");
		log("A match containing the command 'shuffle_enable A' will re-organize\n");
		log("the data bits to accommodate the enable pattern of port A.\n");
		log("\n");
	}
	void execute(vector<string> args, Design *design) override
	{
		rules_t rules;

		log_header(design, "Executing MEMORY_BRAM pass (mapping $mem cells to block memories).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-rules" && argidx+1 < args.size()) {
				rules.parse(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			SigMap sigmap(mod);
			FfInitVals initvals(&sigmap, mod);
			for (auto &mem : Mem::get_selected_memories(mod))
				handle_memory(mem, rules, &initvals);
		}
	}
} MemoryBramPass;

PRIVATE_NAMESPACE_END
