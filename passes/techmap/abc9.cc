/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung <eddie@fpgeh.com>
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

// [[CITE]] ABC
// Berkeley Logic Synthesis and Verification Group, ABC: A System for Sequential Synthesis and Verification
// http://www.eecs.berkeley.edu/~alanmi/abc/

#if 0
// Based on &flow3 - better QoR but more experimental
#define ABC_COMMAND_LUT "&st; &ps -l; &sweep -v; &scorr; " \
						"&st; &if {W}; &save; &st; &syn2; &if {W} -v; &save; &load; "\
						"&st; &if -g -K 6; &dch -f; &if {W} -v; &save; &load; "\
						"&st; &if -g -K 6; &synch2; &if {W} -v; &save; &load; "\
						"&mfs; &ps -l"
#else
#define ABC_COMMAND_LUT "&st; &scorr; &sweep; &dc2; &st; &dch -f; &ps; &if {W} {D} -v; &mfs; &ps -l"
#endif


#define ABC_FAST_COMMAND_LUT "&st; &if {W} {D}"

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/cost.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <cerrno>
#include <sstream>
#include <climits>

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

#include "frontends/aiger/aigerparse.h"
#include "kernel/utils.h"

#ifdef YOSYS_LINK_ABC
extern "C" int Abc_RealMain(int argc, char *argv[]);
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool markgroups;
int map_autoidx;
SigMap assign_map;
RTLIL::Module *module;

bool clk_polarity, en_polarity;
RTLIL::SigSpec clk_sig, en_sig;

inline std::string remap_name(RTLIL::IdString abc_name)
{
	return stringf("$abc$%d$%s", map_autoidx, abc_name.c_str()+1);
}

void handle_loops(RTLIL::Design *design)
{
	Pass::call(design, "scc -set_attr abc_scc_id {}");

	// For every unique SCC found, (arbitrarily) find the first
	// cell in the component, and select (and mark) all its output
	// wires
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->cells()) {
		auto it = cell->attributes.find(ID(abc_scc_id));
		if (it != cell->attributes.end()) {
			auto r = ids_seen.insert(it->second);
			if (r.second) {
				for (auto &c : cell->connections_) {
					if (c.second.is_fully_const()) continue;
					if (cell->output(c.first)) {
						SigBit b = c.second.as_bit();
						Wire *w = b.wire;
						log_assert(!w->port_input);
						w->port_input = true;
						w = module->wire(stringf("%s.abci", w->name.c_str()));
						if (!w) {
							w = module->addWire(stringf("%s.abci", b.wire->name.c_str()), GetSize(b.wire));
							w->port_output = true;
						}
						else {
							log_assert(w->port_input);
							log_assert(b.offset < GetSize(w));
						}
						w->set_bool_attribute(ID(abc_scc_break));
						module->swap_names(b.wire, w);
						c.second = RTLIL::SigBit(w, b.offset);
					}
				}
			}
			cell->attributes.erase(it);
		}
	}

	module->fixup_ports();
}

std::string add_echos_to_abc_cmd(std::string str)
{
	std::string new_str, token;
	for (size_t i = 0; i < str.size(); i++) {
		token += str[i];
		if (str[i] == ';') {
			while (i+1 < str.size() && str[i+1] == ' ')
				i++;
			new_str += "echo + " + token + " " + token + " ";
			token.clear();
		}
	}

	if (!token.empty()) {
		if (!new_str.empty())
			new_str += "echo + " + token + "; ";
		new_str += token;
	}

	return new_str;
}

std::string fold_abc_cmd(std::string str)
{
	std::string token, new_str = "          ";
	int char_counter = 10;

	for (size_t i = 0; i <= str.size(); i++) {
		if (i < str.size())
			token += str[i];
		if (i == str.size() || str[i] == ';') {
			if (char_counter + token.size() > 75)
				new_str += "\n              ", char_counter = 14;
			new_str += token, char_counter += token.size();
			token.clear();
		}
	}

	return new_str;
}

std::string replace_tempdir(std::string text, std::string tempdir_name, bool show_tempdir)
{
	if (show_tempdir)
		return text;

	while (1) {
		size_t pos = text.find(tempdir_name);
		if (pos == std::string::npos)
			break;
		text = text.substr(0, pos) + "<abc-temp-dir>" + text.substr(pos + GetSize(tempdir_name));
	}

	std::string  selfdir_name = proc_self_dirname();
	if (selfdir_name != "/") {
		while (1) {
			size_t pos = text.find(selfdir_name);
			if (pos == std::string::npos)
				break;
			text = text.substr(0, pos) + "<yosys-exe-dir>/" + text.substr(pos + GetSize(selfdir_name));
		}
	}

	return text;
}

struct abc_output_filter
{
	bool got_cr;
	int escape_seq_state;
	std::string linebuf;
	std::string tempdir_name;
	bool show_tempdir;

	abc_output_filter(std::string tempdir_name, bool show_tempdir) : tempdir_name(tempdir_name), show_tempdir(show_tempdir)
	{
		got_cr = false;
		escape_seq_state = 0;
	}

	void next_char(char ch)
	{
		if (escape_seq_state == 0 && ch == '\033') {
			escape_seq_state = 1;
			return;
		}
		if (escape_seq_state == 1) {
			escape_seq_state = ch == '[' ? 2 : 0;
			return;
		}
		if (escape_seq_state == 2) {
			if ((ch < '0' || '9' < ch) && ch != ';')
				escape_seq_state = 0;
			return;
		}
		escape_seq_state = 0;
		if (ch == '\r') {
			got_cr = true;
			return;
		}
		if (ch == '\n') {
			log("ABC: %s\n", replace_tempdir(linebuf, tempdir_name, show_tempdir).c_str());
			got_cr = false, linebuf.clear();
			return;
		}
		if (got_cr)
			got_cr = false, linebuf.clear();
		linebuf += ch;
	}

	void next_line(const std::string &line)
	{
		//int pi, po;
		//if (sscanf(line.c_str(), "Start-point = pi%d.  End-point = po%d.", &pi, &po) == 2) {
		//	log("ABC: Start-point = pi%d (%s).  End-point = po%d (%s).\n",
		//			pi, pi_map.count(pi) ? pi_map.at(pi).c_str() : "???",
		//			po, po_map.count(po) ? po_map.at(po).c_str() : "???");
		//	return;
		//}

		for (char ch : line)
			next_char(ch);
	}
};

void abc9_module(RTLIL::Design *design, RTLIL::Module *current_module, std::string script_file, std::string exe_file,
		bool cleanup, vector<int> lut_costs, bool dff_mode, std::string clk_str,
		bool /*keepff*/, std::string delay_target, std::string /*lutin_shared*/, bool fast_mode,
		bool show_tempdir, std::string box_file, std::string lut_file,
		std::string wire_delay, const dict<int,IdString> &box_lookup
)
{
	module = current_module;
	map_autoidx = autoidx++;

	if (clk_str != "$")
	{
		clk_polarity = true;
		clk_sig = RTLIL::SigSpec();

		en_polarity = true;
		en_sig = RTLIL::SigSpec();
	}

	if (!clk_str.empty() && clk_str != "$")
	{
		if (clk_str.find(',') != std::string::npos) {
			int pos = clk_str.find(',');
			std::string en_str = clk_str.substr(pos+1);
			clk_str = clk_str.substr(0, pos);
			if (en_str[0] == '!') {
				en_polarity = false;
				en_str = en_str.substr(1);
			}
			if (module->wires_.count(RTLIL::escape_id(en_str)) != 0)
				en_sig = assign_map(RTLIL::SigSpec(module->wires_.at(RTLIL::escape_id(en_str)), 0));
		}
		if (clk_str[0] == '!') {
			clk_polarity = false;
			clk_str = clk_str.substr(1);
		}
		if (module->wires_.count(RTLIL::escape_id(clk_str)) != 0)
			clk_sig = assign_map(RTLIL::SigSpec(module->wires_.at(RTLIL::escape_id(clk_str)), 0));
	}

	if (dff_mode && clk_sig.empty())
		log_cmd_error("Clock domain %s not found.\n", clk_str.c_str());

	std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
	if (!cleanup)
		tempdir_name[0] = tempdir_name[4] = '_';
	tempdir_name = make_temp_dir(tempdir_name);
	log_header(design, "Extracting gate netlist of module `%s' to `%s/input.xaig'..\n",
			module->name.c_str(), replace_tempdir(tempdir_name, tempdir_name, show_tempdir).c_str());

	std::string abc_script;

	if (!lut_costs.empty()) {
		abc_script += stringf("read_lut %s/lutdefs.txt; ", tempdir_name.c_str());
		if (!box_file.empty())
			abc_script += stringf("read_box -v %s; ", box_file.c_str());
	}
	else
	if (!lut_file.empty()) {
		abc_script += stringf("read_lut %s; ", lut_file.c_str());
		if (!box_file.empty())
			abc_script += stringf("read_box -v %s; ", box_file.c_str());
	}
	else
		log_abort();

	abc_script += stringf("&read %s/input.xaig; &ps; ", tempdir_name.c_str());

	if (!script_file.empty()) {
		if (script_file[0] == '+') {
			for (size_t i = 1; i < script_file.size(); i++)
				if (script_file[i] == '\'')
					abc_script += "'\\''";
				else if (script_file[i] == ',')
					abc_script += " ";
				else
					abc_script += script_file[i];
		} else
			abc_script += stringf("source %s", script_file.c_str());
	} else if (!lut_costs.empty() || !lut_file.empty()) {
		//bool all_luts_cost_same = true;
		//for (int this_cost : lut_costs)
		//	if (this_cost != lut_costs.front())
		//		all_luts_cost_same = false;
		abc_script += fast_mode ? ABC_FAST_COMMAND_LUT : ABC_COMMAND_LUT;
		//if (all_luts_cost_same && !fast_mode)
		//	abc_script += "; lutpack {S}";
	} else
		log_abort();

	//if (script_file.empty() && !delay_target.empty())
	//	for (size_t pos = abc_script.find("dretime;"); pos != std::string::npos; pos = abc_script.find("dretime;", pos+1))
	//		abc_script = abc_script.substr(0, pos) + "dretime; retime -o {D};" + abc_script.substr(pos+8);

	for (size_t pos = abc_script.find("{D}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + delay_target + abc_script.substr(pos+3);

	//for (size_t pos = abc_script.find("{S}"); pos != std::string::npos; pos = abc_script.find("{S}", pos))
	//	abc_script = abc_script.substr(0, pos) + lutin_shared + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{W}"); pos != std::string::npos; pos = abc_script.find("{W}", pos))
		abc_script = abc_script.substr(0, pos) + wire_delay + abc_script.substr(pos+3);

	abc_script += stringf("; &write %s/output.aig", tempdir_name.c_str());
	abc_script = add_echos_to_abc_cmd(abc_script);

	for (size_t i = 0; i+1 < abc_script.size(); i++)
		if (abc_script[i] == ';' && abc_script[i+1] == ' ')
			abc_script[i+1] = '\n';

	FILE *f = fopen(stringf("%s/abc.script", tempdir_name.c_str()).c_str(), "wt");
	fprintf(f, "%s\n", abc_script.c_str());
	fclose(f);

	if (dff_mode || !clk_str.empty())
	{
		if (clk_sig.size() == 0)
			log("No%s clock domain found. Not extracting any FF cells.\n", clk_str.empty() ? "" : " matching");
		else {
			log("Found%s %s clock domain: %s", clk_str.empty() ? "" : " matching", clk_polarity ? "posedge" : "negedge", log_signal(clk_sig));
			if (en_sig.size() != 0)
				log(", enabled by %s%s", en_polarity ? "" : "!", log_signal(en_sig));
			log("\n");
		}
	}

	bool count_output = false;
	for (auto port_name : module->ports) {
		RTLIL::Wire *port_wire = module->wire(port_name);
		log_assert(port_wire);
		if (port_wire->port_output) {
			count_output = true;
			break;
		}
	}

	log_push();

	if (count_output)
	{
		design->selection_stack.emplace_back(false);
		RTLIL::Selection& sel = design->selection_stack.back();
		sel.select(module);

		handle_loops(design);

		Pass::call(design, "aigmap");

		//log("Extracted %d gates and %d wires to a netlist network with %d inputs and %d outputs.\n",
		//		count_gates, GetSize(signal_list), count_input, count_output);

		Pass::call(design, stringf("write_xaiger -map %s/input.sym %s/input.xaig", tempdir_name.c_str(), tempdir_name.c_str()));

		std::string buffer;
		std::ifstream ifs;
#if 0
		buffer = stringf("%s/%s", tempdir_name.c_str(), "input.xaig");
		ifs.open(buffer);
		if (ifs.fail())
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());
		buffer = stringf("%s/%s", tempdir_name.c_str(), "input.sym");
		log_assert(!design->module(ID($__abc9__)));
		{
			AigerReader reader(design, ifs, ID($__abc9__), "" /* clk_name */, buffer.c_str() /* map_filename */, true /* wideports */);
			reader.parse_xaiger();
		}
		ifs.close();
		Pass::call(design, stringf("write_verilog -noexpr -norename"));
		design->remove(design->module(ID($__abc9__)));
#endif

		design->selection_stack.pop_back();

		// Now 'unexpose' those wires by undoing
		// the expose operation -- remove them from PO/PI
		// and re-connecting them back together
		for (auto wire : module->wires()) {
			auto it = wire->attributes.find(ID(abc_scc_break));
			if (it != wire->attributes.end()) {
				wire->attributes.erase(it);
				log_assert(wire->port_output);
				wire->port_output = false;
				RTLIL::Wire *i_wire = module->wire(wire->name.str() + ".abci");
				log_assert(i_wire);
				log_assert(i_wire->port_input);
				i_wire->port_input = false;
				module->connect(i_wire, wire);
			}
		}
		module->fixup_ports();

		log_header(design, "Executing ABC9.\n");

		if (!lut_costs.empty()) {
			buffer = stringf("%s/lutdefs.txt", tempdir_name.c_str());
			f = fopen(buffer.c_str(), "wt");
			if (f == NULL)
				log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
			for (int i = 0; i < GetSize(lut_costs); i++)
				fprintf(f, "%d %d.00 1.00\n", i+1, lut_costs.at(i));
			fclose(f);
		}

		buffer = stringf("%s -s -f %s/abc.script 2>&1", exe_file.c_str(), tempdir_name.c_str());
		log("Running ABC command: %s\n", replace_tempdir(buffer, tempdir_name, show_tempdir).c_str());

#ifndef YOSYS_LINK_ABC
		abc_output_filter filt(tempdir_name, show_tempdir);
		int ret = run_command(buffer, std::bind(&abc_output_filter::next_line, filt, std::placeholders::_1));
#else
		// These needs to be mutable, supposedly due to getopt
		char *abc_argv[5];
		string tmp_script_name = stringf("%s/abc.script", tempdir_name.c_str());
		abc_argv[0] = strdup(exe_file.c_str());
		abc_argv[1] = strdup("-s");
		abc_argv[2] = strdup("-f");
		abc_argv[3] = strdup(tmp_script_name.c_str());
		abc_argv[4] = 0;
		int ret = Abc_RealMain(4, abc_argv);
		free(abc_argv[0]);
		free(abc_argv[1]);
		free(abc_argv[2]);
		free(abc_argv[3]);
#endif
		if (ret != 0)
			log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);

		buffer = stringf("%s/%s", tempdir_name.c_str(), "output.aig");
		ifs.open(buffer);
		if (ifs.fail())
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());

		buffer = stringf("%s/%s", tempdir_name.c_str(), "input.sym");
		log_assert(!design->module(ID($__abc9__)));

		AigerReader reader(design, ifs, ID($__abc9__), "" /* clk_name */, buffer.c_str() /* map_filename */, true /* wideports */);
		reader.parse_xaiger(box_lookup);
		ifs.close();

#if 0
		Pass::call(design, stringf("write_verilog -noexpr -norename"));
#endif

		log_header(design, "Re-integrating ABC9 results.\n");
		RTLIL::Module *mapped_mod = design->module(ID($__abc9__));
		if (mapped_mod == NULL)
			log_error("ABC output file does not contain a module `$__abc9__'.\n");

		pool<RTLIL::SigBit> output_bits;
		for (auto &it : mapped_mod->wires_) {
			RTLIL::Wire *w = it.second;
			RTLIL::Wire *remap_wire = module->addWire(remap_name(w->name), GetSize(w));
			if (markgroups) remap_wire->attributes[ID(abcgroup)] = map_autoidx;
			if (w->port_output) {
				RTLIL::Wire *wire = module->wire(w->name);
				log_assert(wire);
				for (int i = 0; i < GetSize(w); i++)
					output_bits.insert({wire, i});
			}
		}

		for (auto &it : module->connections_) {
			auto &signal = it.first;
			auto bits = signal.bits();
			for (auto &b : bits)
				if (output_bits.count(b))
					b = module->addWire(NEW_ID);
			signal = std::move(bits);
		}

		dict<IdString, bool> abc_box;
		vector<RTLIL::Cell*> boxes;
		for (const auto &it : module->cells_) {
			auto cell = it.second;
			if (cell->type.in(ID($_AND_), ID($_NOT_))) {
				module->remove(cell);
				continue;
			}
			auto jt = abc_box.find(cell->type);
			if (jt == abc_box.end()) {
				RTLIL::Module* box_module = design->module(cell->type);
				jt = abc_box.insert(std::make_pair(cell->type, box_module && box_module->attributes.count(ID(abc_box_id)))).first;
			}
			if (jt->second)
				boxes.emplace_back(cell);
		}

		dict<SigBit, pool<IdString>> bit_drivers, bit_users;
		TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
		dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
		dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

		std::map<IdString, int> cell_stats;
		for (auto c : mapped_mod->cells())
		{
			toposort.node(c->name);

			RTLIL::Cell *cell = nullptr;
			if (c->type == ID($_NOT_)) {
				RTLIL::SigBit a_bit = c->getPort(ID::A);
				RTLIL::SigBit y_bit = c->getPort(ID::Y);
				bit_users[a_bit].insert(c->name);
				bit_drivers[y_bit].insert(c->name);

				if (!a_bit.wire) {
					c->setPort(ID::Y, module->addWire(NEW_ID));
					RTLIL::Wire *wire = module->wire(remap_name(y_bit.wire->name));
					log_assert(wire);
					module->connect(RTLIL::SigBit(wire, y_bit.offset), State::S1);
				}
				else if (!lut_costs.empty() || !lut_file.empty()) {
					RTLIL::Cell* driver_lut = nullptr;
					// ABC can return NOT gates that drive POs
					if (!a_bit.wire->port_input) {
						// If it's not a NOT gate that that comes from a PI directly,
						// find the driver LUT and clone that to guarantee that we won't
						// increase the max logic depth
						// (TODO: Optimise by not cloning unless will increase depth)
						RTLIL::IdString driver_name;
						if (GetSize(a_bit.wire) == 1)
							driver_name = stringf("%s$lut", a_bit.wire->name.c_str());
						else
							driver_name = stringf("%s[%d]$lut", a_bit.wire->name.c_str(), a_bit.offset);
						driver_lut = mapped_mod->cell(driver_name);
					}

					if (!driver_lut) {
						// If a driver couldn't be found (could be from PI or box CI)
						// then implement using a LUT
						cell = module->addLut(remap_name(stringf("%s$lut", c->name.c_str())),
								RTLIL::SigBit(module->wires_.at(remap_name(a_bit.wire->name)), a_bit.offset),
								RTLIL::SigBit(module->wires_.at(remap_name(y_bit.wire->name)), y_bit.offset),
								RTLIL::Const::from_string("01"));
						bit2sinks[cell->getPort(ID::A)].push_back(cell);
						cell_stats[ID($lut)]++;
					}
					else
						not2drivers[c] = driver_lut;
					continue;
				}
				else
					log_abort();
				if (cell && markgroups) cell->attributes[ID(abcgroup)] = map_autoidx;
				continue;
			}
			cell_stats[c->type]++;

			RTLIL::Cell *existing_cell = nullptr;
			if (c->type == ID($lut)) {
				if (GetSize(c->getPort(ID::A)) == 1 && c->getParam(ID(LUT)) == RTLIL::Const::from_string("01")) {
					SigSpec my_a = module->wires_.at(remap_name(c->getPort(ID::A).as_wire()->name));
					SigSpec my_y = module->wires_.at(remap_name(c->getPort(ID::Y).as_wire()->name));
					module->connect(my_y, my_a);
					if (markgroups) c->attributes[ID(abcgroup)] = map_autoidx;
					log_abort();
					continue;
				}
				cell = module->addCell(remap_name(c->name), c->type);
			}
			else {
				existing_cell = module->cell(c->name);
				log_assert(existing_cell);
				cell = module->addCell(remap_name(c->name), c->type);
				module->swap_names(cell, existing_cell);
			}

			if (markgroups) cell->attributes[ID(abcgroup)] = map_autoidx;
			if (existing_cell) {
				cell->parameters = existing_cell->parameters;
				cell->attributes = existing_cell->attributes;
			}
			else {
				cell->parameters = c->parameters;
				cell->attributes = c->attributes;
			}
			for (auto &conn : c->connections()) {
				RTLIL::SigSpec newsig;
				for (auto c : conn.second.chunks()) {
					if (c.width == 0)
						continue;
					//log_assert(c.width == 1);
					if (c.wire)
						c.wire = module->wires_.at(remap_name(c.wire->name));
					newsig.append(c);
				}
				cell->setPort(conn.first, newsig);

				if (cell->input(conn.first)) {
					for (auto i : newsig)
						bit2sinks[i].push_back(cell);
					for (auto i : conn.second)
						bit_users[i].insert(c->name);
				}
				if (cell->output(conn.first))
					for (auto i : conn.second)
						bit_drivers[i].insert(c->name);
			}
		}

		for (auto cell : boxes)
			module->remove(cell);

		// Copy connections (and rename) from mapped_mod to module
		for (auto conn : mapped_mod->connections()) {
			if (!conn.first.is_fully_const()) {
				auto chunks = conn.first.chunks();
				for (auto &c : chunks)
					c.wire = module->wires_.at(remap_name(c.wire->name));
				conn.first = std::move(chunks);
			}
			if (!conn.second.is_fully_const()) {
				auto chunks = conn.second.chunks();
				for (auto &c : chunks)
					if (c.wire)
						c.wire = module->wires_.at(remap_name(c.wire->name));
				conn.second = std::move(chunks);
			}
			module->connect(conn);
		}

		for (auto &it : cell_stats)
			log("ABC RESULTS:   %15s cells: %8d\n", it.first.c_str(), it.second);
		int in_wires = 0, out_wires = 0;

		// Stitch in mapped_mod's inputs/outputs into module
		for (auto port : mapped_mod->ports) {
			RTLIL::Wire *w = mapped_mod->wire(port);
			RTLIL::Wire *wire = module->wire(port);
			log_assert(wire);
			RTLIL::Wire *remap_wire = module->wire(remap_name(port));
			RTLIL::SigSpec signal = RTLIL::SigSpec(wire, 0, GetSize(remap_wire));
			log_assert(GetSize(signal) >= GetSize(remap_wire));

			RTLIL::SigSig conn;
			if (w->port_output) {
				conn.first = signal;
				conn.second = remap_wire;
				out_wires++;
				module->connect(conn);
			}
			else if (w->port_input) {
				conn.first = remap_wire;
				conn.second = signal;
				in_wires++;
				module->connect(conn);
			}
		}

		for (auto &it : bit_users)
			if (bit_drivers.count(it.first))
				for (auto driver_cell : bit_drivers.at(it.first))
				for (auto user_cell : it.second)
					toposort.edge(driver_cell, user_cell);
		bool no_loops YS_ATTRIBUTE(unused) = toposort.sort();
		log_assert(no_loops);

		for (auto ii = toposort.sorted.rbegin(); ii != toposort.sorted.rend(); ii++) {
			RTLIL::Cell *not_cell = mapped_mod->cell(*ii);
			log_assert(not_cell);
			if (not_cell->type != ID($_NOT_))
				continue;
			auto it = not2drivers.find(not_cell);
			if (it == not2drivers.end())
				continue;
			RTLIL::Cell *driver_lut = it->second;
			RTLIL::SigBit a_bit = not_cell->getPort(ID::A);
			RTLIL::SigBit y_bit = not_cell->getPort(ID::Y);
			RTLIL::Const driver_mask;

			a_bit.wire = module->wires_.at(remap_name(a_bit.wire->name));
			y_bit.wire = module->wires_.at(remap_name(y_bit.wire->name));

			auto jt = bit2sinks.find(a_bit);
			if (jt == bit2sinks.end())
				goto clone_lut;

			for (auto sink_cell : jt->second)
				if (sink_cell->type != ID($lut))
					goto clone_lut;

			// Push downstream LUTs past inverter
			for (auto sink_cell : jt->second) {
				SigSpec A = sink_cell->getPort(ID::A);
				RTLIL::Const mask = sink_cell->getParam(ID(LUT));
				int index = 0;
				for (; index < GetSize(A); index++)
					if (A[index] == a_bit)
						break;
				log_assert(index < GetSize(A));
				int i = 0;
				while (i < GetSize(mask)) {
					for (int j = 0; j < (1 << index); j++)
						std::swap(mask[i+j], mask[i+j+(1 << index)]);
					i += 1 << (index+1);
				}
				A[index] = y_bit;
				sink_cell->setPort(ID::A, A);
				sink_cell->setParam(ID(LUT), mask);
			}

			// Since we have rewritten all sinks (which we know
			// to be only LUTs) to be after the inverter, we can
			// go ahead and clone the LUT with the expectation
			// that the original driving LUT will become dangling
			// and get cleaned away
clone_lut:
			driver_mask = driver_lut->getParam(ID(LUT));
			for (auto &b : driver_mask.bits) {
				if (b == RTLIL::State::S0) b = RTLIL::State::S1;
				else if (b == RTLIL::State::S1) b = RTLIL::State::S0;
			}
			auto cell = module->addLut(NEW_ID,
					driver_lut->getPort(ID::A),
					y_bit,
					driver_mask);
			for (auto &bit : cell->connections_.at(ID::A)) {
				bit.wire = module->wires_.at(remap_name(bit.wire->name));
				bit2sinks[bit].push_back(cell);
			}
		}

		//log("ABC RESULTS:        internal signals: %8d\n", int(signal_list.size()) - in_wires - out_wires);
		log("ABC RESULTS:           input signals: %8d\n", in_wires);
		log("ABC RESULTS:          output signals: %8d\n", out_wires);

		design->remove(mapped_mod);
	}
	else
	{
		log("Don't call ABC as there is nothing to map.\n");
	}

	if (cleanup)
	{
		log("Removing temp directory.\n");
		remove_directory(tempdir_name);
	}

	log_pop();
}

struct Abc9Pass : public Pass {
	Abc9Pass() : Pass("abc9", "use ABC9 for technology mapping") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9 [options] [selection]\n");
		log("\n");
		log("This pass uses the ABC tool [1] for technology mapping of yosys's internal gate\n");
		log("library to a target architecture.\n");
		log("\n");
		log("    -exe <command>\n");
#ifdef ABCEXTERNAL
		log("        use the specified command instead of \"" ABCEXTERNAL "\" to execute ABC.\n");
#else
		log("        use the specified command instead of \"<yosys-bindir>/yosys-abc\" to execute ABC.\n");
#endif
		log("        This can e.g. be used to call a specific version of ABC or a wrapper.\n");
		log("\n");
		log("    -script <file>\n");
		log("        use the specified ABC script file instead of the default script.\n");
		log("\n");
		log("        if <file> starts with a plus sign (+), then the rest of the filename\n");
		log("        string is interpreted as the command string to be passed to ABC. The\n");
		log("        leading plus sign is removed and all commas (,) in the string are\n");
		log("        replaced with blanks before the string is passed to ABC.\n");
		log("\n");
		log("        if no -script parameter is given, the following scripts are used:\n");
		log("\n");
		log("        for -lut/-luts (only one LUT size):\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT /*"; lutpack {S}"*/).c_str());
		log("\n");
		log("        for -lut/-luts (different LUT sizes):\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT).c_str());
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("\n");
		log("        for -lut/-luts:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_LUT).c_str());
		log("\n");
		log("    -D <picoseconds>\n");
		log("        set delay target. the string {D} in the default scripts above is\n");
		log("        replaced by this option when used, and an empty string otherwise\n");
		log("        (indicating best possible delay).\n");
//		log("        This also replaces 'dretime' with 'dretime; retime -o {D}' in the\n");
//		log("        default scripts above.\n");
		log("\n");
//		log("    -S <num>\n");
//		log("        maximum number of LUT inputs shared.\n");
//		log("        (replaces {S} in the default scripts above, default: -S 1)\n");
//		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -lut <w1>:<w2>\n");
		log("        generate netlist using luts of (max) the specified width <w2>. All\n");
		log("        luts with width <= <w1> have constant cost. for luts larger than <w1>\n");
		log("        the area cost doubles with each additional input bit. the delay cost\n");
		log("        is still constant for all lut widths.\n");
		log("\n");
		log("    -lut <file>\n");
		log("        pass this file with lut library to ABC.\n");
		log("\n");
		log("    -luts <cost1>,<cost2>,<cost3>,<sizeN>:<cost4-N>,..\n");
		log("        generate netlist using luts. Use the specified costs for luts with 1,\n");
		log("        2, 3, .. inputs.\n");
		log("\n");
//		log("    -dff\n");
//		log("        also pass $_DFF_?_ and $_DFFE_??_ cells through ABC. modules with many\n");
//		log("        clock domains are automatically partitioned in clock domains and each\n");
//		log("        domain is passed through ABC independently.\n");
//		log("\n");
//		log("    -clk [!]<clock-signal-name>[,[!]<enable-signal-name>]\n");
//		log("        use only the specified clock domain. this is like -dff, but only FF\n");
//		log("        cells that belong to the specified clock domain are used.\n");
//		log("\n");
//		log("    -keepff\n");
//		log("        set the \"keep\" attribute on flip-flop output wires. (and thus preserve\n");
//		log("        them, for example for equivalence checking.)\n");
//		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("    -showtmp\n");
		log("        print the temp dir name in log. usually this is suppressed so that the\n");
		log("        command output is identical across runs.\n");
		log("\n");
		log("    -markgroups\n");
		log("        set a 'abcgroup' attribute on all objects created by ABC. The value of\n");
		log("        this attribute is a unique integer for each ABC process started. This\n");
		log("        is useful for debugging the partitioning of clock domains.\n");
		log("\n");
		log("    -box <file>\n");
		log("        pass this file with box library to ABC. Use with -lut.\n");
		log("\n");
		log("Note that this is a logic optimization pass within Yosys that is calling ABC\n");
		log("internally. This is not going to \"run ABC on your design\". It will instead run\n");
		log("ABC on logic snippets extracted from your design. You will not get any useful\n");
		log("output when passing an ABC script that writes a file. Instead write your full\n");
		log("design as BLIF file with write_blif and then load that into ABC externally if\n");
		log("you want to use ABC to convert your design into another format.\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9 pass (technology mapping using ABC9).\n");
		log_push();

		assign_map.clear();

#ifdef ABCEXTERNAL
		std::string exe_file = ABCEXTERNAL;
#else
		std::string exe_file = proc_self_dirname() + "yosys-abc";
#endif
		std::string script_file, clk_str, box_file, lut_file;
		std::string delay_target, lutin_shared = "-S 1", wire_delay;
		bool fast_mode = false, dff_mode = false, keepff = false, cleanup = true;
		bool show_tempdir = false;
		vector<int> lut_costs;
		markgroups = false;

#if 0
		cleanup = false;
		show_tempdir = true;
#endif

#ifdef _WIN32
#ifndef ABCEXTERNAL
		if (!check_file_exists(exe_file + ".exe") && check_file_exists(proc_self_dirname() + "..\\yosys-abc.exe"))
			exe_file = proc_self_dirname() + "..\\yosys-abc";
#endif
#endif

		size_t argidx;
		char pwd [PATH_MAX];
		if (!getcwd(pwd, sizeof(pwd))) {
			log_cmd_error("getcwd failed: %s\n", strerror(errno));
			log_abort();
		}
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exe" && argidx+1 < args.size()) {
				exe_file = args[++argidx];
				continue;
			}
			if (arg == "-script" && argidx+1 < args.size()) {
				script_file = args[++argidx];
				rewrite_filename(script_file);
				if (!script_file.empty() && !is_absolute_path(script_file) && script_file[0] != '+')
					script_file = std::string(pwd) + "/" + script_file;
				continue;
			}
			if (arg == "-D" && argidx+1 < args.size()) {
				delay_target = "-D " + args[++argidx];
				continue;
			}
			//if (arg == "-S" && argidx+1 < args.size()) {
			//	lutin_shared = "-S " + args[++argidx];
			//	continue;
			//}
			if (arg == "-lut" && argidx+1 < args.size()) {
				string arg = args[++argidx];
				size_t pos = arg.find_first_of(':');
				int lut_mode = 0, lut_mode2 = 0;
				if (pos != string::npos) {
					lut_mode = atoi(arg.substr(0, pos).c_str());
					lut_mode2 = atoi(arg.substr(pos+1).c_str());
				} else {
					pos = arg.find_first_of('.');
					if (pos != string::npos) {
						lut_file = arg;
						rewrite_filename(lut_file);
						if (!lut_file.empty() && !is_absolute_path(lut_file))
							lut_file = std::string(pwd) + "/" + lut_file;
					}
					else {
						lut_mode = atoi(arg.c_str());
						lut_mode2 = lut_mode;
					}
				}
				lut_costs.clear();
				for (int i = 0; i < lut_mode; i++)
					lut_costs.push_back(1);
				for (int i = lut_mode; i < lut_mode2; i++)
					lut_costs.push_back(2 << (i - lut_mode));
				continue;
			}
			if (arg == "-luts" && argidx+1 < args.size()) {
				lut_costs.clear();
				for (auto &tok : split_tokens(args[++argidx], ",")) {
					auto parts = split_tokens(tok, ":");
					if (GetSize(parts) == 0 && !lut_costs.empty())
						lut_costs.push_back(lut_costs.back());
					else if (GetSize(parts) == 1)
						lut_costs.push_back(atoi(parts.at(0).c_str()));
					else if (GetSize(parts) == 2)
						while (GetSize(lut_costs) < atoi(parts.at(0).c_str()))
							lut_costs.push_back(atoi(parts.at(1).c_str()));
					else
						log_cmd_error("Invalid -luts syntax.\n");
				}
				continue;
			}
			if (arg == "-fast") {
				fast_mode = true;
				continue;
			}
			//if (arg == "-dff") {
			//	dff_mode = true;
			//	continue;
			//}
			//if (arg == "-clk" && argidx+1 < args.size()) {
			//	clk_str = args[++argidx];
			//	dff_mode = true;
			//	continue;
			//}
			//if (arg == "-keepff") {
			//	keepff = true;
			//	continue;
			//}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			if (arg == "-showtmp") {
				show_tempdir = true;
				continue;
			}
			if (arg == "-markgroups") {
				markgroups = true;
				continue;
			}
			if (arg == "-box" && argidx+1 < args.size()) {
				box_file = args[++argidx];
				continue;
			}
			if (arg == "-W" && argidx+1 < args.size()) {
				wire_delay = "-W " + args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// ABC expects a box file for XAIG
		if (box_file.empty())
		    box_file = "+/dummy.box";

		rewrite_filename(box_file);
		if (!box_file.empty() && !is_absolute_path(box_file))
		    box_file = std::string(pwd) + "/" + box_file;

		dict<int,IdString> box_lookup;
		for (auto m : design->modules()) {
			auto it = m->attributes.find(ID(abc_box_id));
			if (it == m->attributes.end())
				continue;
			if (m->name.begins_with("$paramod"))
				continue;
			auto id = it->second.as_int();
			auto r = box_lookup.insert(std::make_pair(id, m->name));
			if (!r.second)
				log_error("Module '%s' has the same abc_box_id = %d value as '%s'.\n",
						log_id(m), id, log_id(r.first->second));
			log_assert(r.second);

			RTLIL::Wire *carry_in = nullptr, *carry_out = nullptr;
			for (auto p : m->ports) {
				auto w = m->wire(p);
				log_assert(w);
				if (w->attributes.count(ID(abc_carry))) {
					if (w->port_input) {
						if (carry_in)
							log_error("Module '%s' contains more than one 'abc_carry' input port.\n", log_id(m));
						carry_in = w;
					}
					else if (w->port_output) {
						if (carry_out)
							log_error("Module '%s' contains more than one 'abc_carry' input port.\n", log_id(m));
						carry_out = w;
					}
				}
			}
			if (carry_in || carry_out) {
				if (carry_in && !carry_out)
					log_error("Module '%s' contains an 'abc_carry' input port but no output port.\n", log_id(m));
				if (!carry_in && carry_out)
					log_error("Module '%s' contains an 'abc_carry' output port but no input port.\n", log_id(m));
				// Make carry_in the last PI, and carry_out the last PO
				//   since ABC requires it this way
				auto &ports = m->ports;
				for (auto it = ports.begin(); it != ports.end(); ) {
					RTLIL::Wire* w = m->wire(*it);
					log_assert(w);
					if (w == carry_in || w == carry_out) {
						it = ports.erase(it);
						continue;
					}
					if (w->port_id > carry_in->port_id)
						--w->port_id;
					if (w->port_id > carry_out->port_id)
						--w->port_id;
					log_assert(w->port_input || w->port_output);
					log_assert(ports[w->port_id-1] == w->name);
					++it;
				}
				ports.push_back(carry_in->name);
				carry_in->port_id = ports.size();
				ports.push_back(carry_out->name);
				carry_out->port_id = ports.size();
			}
		}

		for (auto mod : design->selected_modules())
		{
			if (mod->attributes.count(ID(abc_box_id)))
				continue;

			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			assign_map.set(mod);

			if (!dff_mode || !clk_str.empty()) {
				abc9_module(design, mod, script_file, exe_file, cleanup, lut_costs, dff_mode, clk_str, keepff,
						delay_target, lutin_shared, fast_mode, show_tempdir,
						box_file, lut_file, wire_delay, box_lookup);
				continue;
			}

			CellTypes ct(design);

			std::vector<RTLIL::Cell*> all_cells = mod->selected_cells();
			std::set<RTLIL::Cell*> unassigned_cells(all_cells.begin(), all_cells.end());

			std::set<RTLIL::Cell*> expand_queue, next_expand_queue;
			std::set<RTLIL::Cell*> expand_queue_up, next_expand_queue_up;
			std::set<RTLIL::Cell*> expand_queue_down, next_expand_queue_down;

			typedef tuple<bool, RTLIL::SigSpec, bool, RTLIL::SigSpec> clkdomain_t;
			std::map<clkdomain_t, std::vector<RTLIL::Cell*>> assigned_cells;
			std::map<RTLIL::Cell*, clkdomain_t> assigned_cells_reverse;

			std::map<RTLIL::Cell*, std::set<RTLIL::SigBit>> cell_to_bit, cell_to_bit_up, cell_to_bit_down;
			std::map<RTLIL::SigBit, std::set<RTLIL::Cell*>> bit_to_cell, bit_to_cell_up, bit_to_cell_down;

			for (auto cell : all_cells)
			{
				clkdomain_t key;

				for (auto &conn : cell->connections())
				for (auto bit : conn.second) {
					bit = assign_map(bit);
					if (bit.wire != nullptr) {
						cell_to_bit[cell].insert(bit);
						bit_to_cell[bit].insert(cell);
						if (ct.cell_input(cell->type, conn.first)) {
							cell_to_bit_up[cell].insert(bit);
							bit_to_cell_down[bit].insert(cell);
						}
						if (ct.cell_output(cell->type, conn.first)) {
							cell_to_bit_down[cell].insert(bit);
							bit_to_cell_up[bit].insert(cell);
						}
					}
				}

				if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_)))
				{
					key = clkdomain_t(cell->type == ID($_DFF_P_), assign_map(cell->getPort(ID(C))), true, RTLIL::SigSpec());
				}
				else
				if (cell->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
				{
					bool this_clk_pol = cell->type.in(ID($_DFFE_PN_), ID($_DFFE_PP_));
					bool this_en_pol = cell->type.in(ID($_DFFE_NP_), ID($_DFFE_PP_));
					key = clkdomain_t(this_clk_pol, assign_map(cell->getPort(ID(C))), this_en_pol, assign_map(cell->getPort(ID(E))));
				}
				else
					continue;

				unassigned_cells.erase(cell);
				expand_queue.insert(cell);
				expand_queue_up.insert(cell);
				expand_queue_down.insert(cell);

				assigned_cells[key].push_back(cell);
				assigned_cells_reverse[cell] = key;
			}

			while (!expand_queue_up.empty() || !expand_queue_down.empty())
			{
				if (!expand_queue_up.empty())
				{
					RTLIL::Cell *cell = *expand_queue_up.begin();
					clkdomain_t key = assigned_cells_reverse.at(cell);
					expand_queue_up.erase(cell);

					for (auto bit : cell_to_bit_up[cell])
					for (auto c : bit_to_cell_up[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue_up.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
							expand_queue.insert(c);
						}
				}

				if (!expand_queue_down.empty())
				{
					RTLIL::Cell *cell = *expand_queue_down.begin();
					clkdomain_t key = assigned_cells_reverse.at(cell);
					expand_queue_down.erase(cell);

					for (auto bit : cell_to_bit_down[cell])
					for (auto c : bit_to_cell_down[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue_up.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
							expand_queue.insert(c);
						}
				}

				if (expand_queue_up.empty() && expand_queue_down.empty()) {
					expand_queue_up.swap(next_expand_queue_up);
					expand_queue_down.swap(next_expand_queue_down);
				}
			}

			while (!expand_queue.empty())
			{
				RTLIL::Cell *cell = *expand_queue.begin();
				clkdomain_t key = assigned_cells_reverse.at(cell);
				expand_queue.erase(cell);

				for (auto bit : cell_to_bit.at(cell)) {
					for (auto c : bit_to_cell[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
						}
					bit_to_cell[bit].clear();
				}

				if (expand_queue.empty())
					expand_queue.swap(next_expand_queue);
			}

			clkdomain_t key(true, RTLIL::SigSpec(), true, RTLIL::SigSpec());
			for (auto cell : unassigned_cells) {
				assigned_cells[key].push_back(cell);
				assigned_cells_reverse[cell] = key;
			}

			log_header(design, "Summary of detected clock domains:\n");
			for (auto &it : assigned_cells)
				log("  %d cells in clk=%s%s, en=%s%s\n", GetSize(it.second),
						std::get<0>(it.first) ? "" : "!", log_signal(std::get<1>(it.first)),
						std::get<2>(it.first) ? "" : "!", log_signal(std::get<3>(it.first)));

			for (auto &it : assigned_cells) {
				clk_polarity = std::get<0>(it.first);
				clk_sig = assign_map(std::get<1>(it.first));
				en_polarity = std::get<2>(it.first);
				en_sig = assign_map(std::get<3>(it.first));
				abc9_module(design, mod, script_file, exe_file, cleanup, lut_costs, !clk_sig.empty(), "$",
						keepff, delay_target, lutin_shared, fast_mode, show_tempdir,
						box_file, lut_file, wire_delay, box_lookup);
				assign_map.set(mod);
			}
		}

		assign_map.clear();

		log_pop();
	}
} Abc9Pass;

PRIVATE_NAMESPACE_END
