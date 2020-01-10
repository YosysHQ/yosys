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

int map_autoidx;

inline std::string remap_name(RTLIL::IdString abc9_name)
{
	return stringf("$abc$%d$%s", map_autoidx, abc9_name.c_str()+1);
}

void handle_loops(RTLIL::Design *design, RTLIL::Module *module)
{
	Pass::call(design, "scc -set_attr abc9_scc_id {} % w:*");

	// For every unique SCC found, (arbitrarily) find the first
	// cell in the component, and select (and mark) all its output
	// wires
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->cells()) {
		auto it = cell->attributes.find(ID(abc9_scc_id));
		if (it != cell->attributes.end()) {
			auto r = ids_seen.insert(it->second);
			if (r.second) {
				for (auto &c : cell->connections_) {
					if (c.second.is_fully_const()) continue;
					if (cell->output(c.first)) {
						SigBit b = c.second.as_bit();
						Wire *w = b.wire;
						if (w->port_input) {
							// In this case, hopefully the loop break has been already created
							// Get the non-prefixed wire
							Wire *wo = module->wire(stringf("%s.abco", b.wire->name.c_str()));
							log_assert(wo != nullptr);
							log_assert(wo->port_output);
							log_assert(b.offset < GetSize(wo));
							c.second = RTLIL::SigBit(wo, b.offset);
						}
						else {
							// Create a new output/input loop break
							w->port_input = true;
							w = module->wire(stringf("%s.abco", w->name.c_str()));
							if (!w) {
								w = module->addWire(stringf("%s.abco", b.wire->name.c_str()), GetSize(b.wire));
								w->port_output = true;
							}
							else {
								log_assert(w->port_input);
								log_assert(b.offset < GetSize(w));
							}
							w->set_bool_attribute(ID(abc9_scc_break));
							c.second = RTLIL::SigBit(w, b.offset);
						}
					}
				}
			}
			cell->attributes.erase(it);
		}
	}

	module->fixup_ports();
}

std::string add_echos_to_abc9_cmd(std::string str)
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

std::string fold_abc9_cmd(std::string str)
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

struct abc9_output_filter
{
	bool got_cr;
	int escape_seq_state;
	std::string linebuf;
	std::string tempdir_name;
	bool show_tempdir;

	abc9_output_filter(std::string tempdir_name, bool show_tempdir) : tempdir_name(tempdir_name), show_tempdir(show_tempdir)
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

void abc9_module(RTLIL::Design *design, RTLIL::Module *module, std::string script_file, std::string exe_file,
		bool cleanup, vector<int> lut_costs, bool dff_mode, std::string delay_target, std::string /*lutin_shared*/, bool fast_mode,
		bool show_tempdir, std::string box_file, std::string lut_file,
		std::string wire_delay, bool nomfs
)
{
	map_autoidx = autoidx++;

	std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
	if (!cleanup)
		tempdir_name[0] = tempdir_name[4] = '_';
	tempdir_name = make_temp_dir(tempdir_name);
	log_header(design, "Extracting gate netlist of module `%s' to `%s/input.xaig'..\n",
			module->name.c_str(), replace_tempdir(tempdir_name, tempdir_name, show_tempdir).c_str());

	std::string abc9_script;

	if (!lut_costs.empty()) {
		abc9_script += stringf("read_lut %s/lutdefs.txt; ", tempdir_name.c_str());
		if (!box_file.empty())
			abc9_script += stringf("read_box %s; ", box_file.c_str());
	}
	else
	if (!lut_file.empty()) {
		abc9_script += stringf("read_lut %s; ", lut_file.c_str());
		if (!box_file.empty())
			abc9_script += stringf("read_box %s; ", box_file.c_str());
	}
	else
		log_abort();

	abc9_script += stringf("&read %s/input.xaig; &ps; ", tempdir_name.c_str());

	if (!script_file.empty()) {
		if (script_file[0] == '+') {
			for (size_t i = 1; i < script_file.size(); i++)
				if (script_file[i] == '\'')
					abc9_script += "'\\''";
				else if (script_file[i] == ',')
					abc9_script += " ";
				else
					abc9_script += script_file[i];
		} else
			abc9_script += stringf("source %s", script_file.c_str());
	} else if (!lut_costs.empty() || !lut_file.empty()) {
		abc9_script += fast_mode ? RTLIL::constpad.at("abc9.script.default.fast").substr(1,std::string::npos)
			: RTLIL::constpad.at("abc9.script.default").substr(1,std::string::npos);
	} else
		log_abort();

	for (size_t pos = abc9_script.find("{D}"); pos != std::string::npos; pos = abc9_script.find("{D}", pos))
		abc9_script = abc9_script.substr(0, pos) + delay_target + abc9_script.substr(pos+3);

	//for (size_t pos = abc9_script.find("{S}"); pos != std::string::npos; pos = abc9_script.find("{S}", pos))
	//	abc9_script = abc9_script.substr(0, pos) + lutin_shared + abc9_script.substr(pos+3);

	for (size_t pos = abc9_script.find("{W}"); pos != std::string::npos; pos = abc9_script.find("{W}", pos))
		abc9_script = abc9_script.substr(0, pos) + wire_delay + abc9_script.substr(pos+3);

	std::string C;
	if (design->scratchpad.count("abc9.if.C"))
		C = "-C " + design->scratchpad_get_string("abc9.if.C");
	for (size_t pos = abc9_script.find("{C}"); pos != std::string::npos; pos = abc9_script.find("{C}", pos))
		abc9_script = abc9_script.substr(0, pos) + C + abc9_script.substr(pos+3);

	std::string R;
	if (design->scratchpad.count("abc9.if.R"))
		R = "-R " + design->scratchpad_get_string("abc9.if.R");
	for (size_t pos = abc9_script.find("{R}"); pos != std::string::npos; pos = abc9_script.find("{R}", pos))
		abc9_script = abc9_script.substr(0, pos) + R + abc9_script.substr(pos+3);

	if (nomfs)
		for (size_t pos = abc9_script.find("&mfs"); pos != std::string::npos; pos = abc9_script.find("&mfs", pos))
			abc9_script = abc9_script.erase(pos, strlen("&mfs"));

	abc9_script += stringf("; &ps -l; &write -n %s/output.aig; time", tempdir_name.c_str());
	abc9_script = add_echos_to_abc9_cmd(abc9_script);

	for (size_t i = 0; i+1 < abc9_script.size(); i++)
		if (abc9_script[i] == ';' && abc9_script[i+1] == ' ')
			abc9_script[i+1] = '\n';

	FILE *f = fopen(stringf("%s/abc.script", tempdir_name.c_str()).c_str(), "wt");
	fprintf(f, "%s\n", abc9_script.c_str());
	fclose(f);

	log_push();

	handle_loops(design, module);

	Pass::call(design, "aigmap -select");

	Pass::call(design, stringf("write_xaiger -map %s/input.sym %s/input.xaig", tempdir_name.c_str(), tempdir_name.c_str()));

	int count_outputs = design->scratchpad_get_int("write_xaiger.num_outputs");
	log("Extracted %d AND gates and %d wires to a netlist network with %d inputs and %d outputs.\n",
			design->scratchpad_get_int("write_xaiger.num_ands"),
			design->scratchpad_get_int("write_xaiger.num_wires"),
			design->scratchpad_get_int("write_xaiger.num_inputs"),
			count_outputs);

	if (count_outputs > 0) {
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
			AigerReader reader(design, ifs, ID($__abc9__), "" /* clk_name */, /*buffer.c_str()*/ "" /* map_filename */, true /* wideports */);
			reader.parse_xaiger();
		}
		ifs.close();
		Pass::call_on_module(design, design->module(ID($__abc9__)), stringf("write_verilog -noexpr -norename -selected"));
		design->remove(design->module(ID($__abc9__)));
#endif

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
		abc9_output_filter filt(tempdir_name, show_tempdir);
		int ret = run_command(buffer, std::bind(&abc9_output_filter::next_line, filt, std::placeholders::_1));
#else
		// These needs to be mutable, supposedly due to getopt
		char *abc9_argv[5];
		string tmp_script_name = stringf("%s/abc.script", tempdir_name.c_str());
		abc9_argv[0] = strdup(exe_file.c_str());
		abc9_argv[1] = strdup("-s");
		abc9_argv[2] = strdup("-f");
		abc9_argv[3] = strdup(tmp_script_name.c_str());
		abc9_argv[4] = 0;
		int ret = Abc_RealMain(4, abc9_argv);
		free(abc9_argv[0]);
		free(abc9_argv[1]);
		free(abc9_argv[2]);
		free(abc9_argv[3]);
#endif
		if (ret != 0)
			log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);

		buffer = stringf("%s/%s", tempdir_name.c_str(), "output.aig");
		ifs.open(buffer, std::ifstream::binary);
		if (ifs.fail())
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());

		buffer = stringf("%s/%s", tempdir_name.c_str(), "input.sym");
		log_assert(!design->module(ID($__abc9__)));

		AigerReader reader(design, ifs, ID($__abc9__), "" /* clk_name */, buffer.c_str() /* map_filename */, true /* wideports */);
		reader.parse_xaiger();
		ifs.close();

#if 0
		Pass::call_on_module(design, design->module(ID($__abc9__)), stringf("write_verilog -noexpr -norename -selected"));
#endif

		log_header(design, "Re-integrating ABC9 results.\n");
		RTLIL::Module *mapped_mod = design->module(ID($__abc9__));
		if (mapped_mod == NULL)
			log_error("ABC output file does not contain a module `$__abc9__'.\n");

		for (auto w : mapped_mod->wires())
			module->addWire(remap_name(w->name), GetSize(w));

		dict<IdString, bool> abc9_box;
		vector<RTLIL::Cell*> boxes;
		for (auto it = module->cells_.begin(); it != module->cells_.end(); ) {
			auto cell = it->second;
			if (cell->type.in(ID($_AND_), ID($_NOT_), ID($__ABC9_FF_))) {
				it = module->cells_.erase(it);
				continue;
			}
			++it;
			RTLIL::Module* box_module = design->module(cell->type);
			auto jt = abc9_box.find(cell->type);
			if (jt == abc9_box.end())
				jt = abc9_box.insert(std::make_pair(cell->type, box_module && box_module->attributes.count(ID(abc9_box_id)))).first;
			if (jt->second) {
				if (box_module->get_bool_attribute("\\abc9_flop")) {
					if (dff_mode)
						boxes.emplace_back(cell);
					else
						box_module->set_bool_attribute("\\abc9_keep", false);
				}
				else
					boxes.emplace_back(cell);
			}
		}

		dict<SigBit, pool<IdString>> bit_drivers, bit_users;
		TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
		dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
		dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

		std::map<IdString, int> cell_stats;
		for (auto mapped_cell : mapped_mod->cells())
		{
			toposort.node(mapped_cell->name);

			RTLIL::Cell *cell = nullptr;
			if (mapped_cell->type == ID($_NOT_)) {
				RTLIL::SigBit a_bit = mapped_cell->getPort(ID::A);
				RTLIL::SigBit y_bit = mapped_cell->getPort(ID::Y);
				bit_users[a_bit].insert(mapped_cell->name);
				bit_drivers[y_bit].insert(mapped_cell->name);

				if (!a_bit.wire) {
					mapped_cell->setPort(ID::Y, module->addWire(NEW_ID));
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
						cell = module->addLut(remap_name(stringf("%s$lut", mapped_cell->name.c_str())),
								RTLIL::SigBit(module->wires_.at(remap_name(a_bit.wire->name)), a_bit.offset),
								RTLIL::SigBit(module->wires_.at(remap_name(y_bit.wire->name)), y_bit.offset),
								RTLIL::Const::from_string("01"));
						bit2sinks[cell->getPort(ID::A)].push_back(cell);
						cell_stats[ID($lut)]++;
					}
					else
						not2drivers[mapped_cell] = driver_lut;
					continue;
				}
				else
					log_abort();
				continue;
			}
			cell_stats[mapped_cell->type]++;

			RTLIL::Cell *existing_cell = nullptr;
			if (mapped_cell->type.in(ID($lut), ID($__ABC9_FF_))) {
				if (mapped_cell->type == ID($lut) &&
						GetSize(mapped_cell->getPort(ID::A)) == 1 &&
						mapped_cell->getParam(ID(LUT)) == RTLIL::Const::from_string("01")) {
					SigSpec my_a = module->wires_.at(remap_name(mapped_cell->getPort(ID::A).as_wire()->name));
					SigSpec my_y = module->wires_.at(remap_name(mapped_cell->getPort(ID::Y).as_wire()->name));
					module->connect(my_y, my_a);
					log_abort();
					continue;
				}
				cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			}
			else {
				existing_cell = module->cell(mapped_cell->name);
				log_assert(existing_cell);
				cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			}

			if (existing_cell) {
				cell->parameters = existing_cell->parameters;
				cell->attributes = existing_cell->attributes;
			}
			else {
				cell->parameters = mapped_cell->parameters;
				cell->attributes = mapped_cell->attributes;
			}

			RTLIL::Module* box_module = design->module(mapped_cell->type);
			auto abc9_flop = box_module && box_module->get_bool_attribute("\\abc9_flop");
			for (auto &conn : mapped_cell->connections()) {
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

				if (!abc9_flop) {
					if (cell->input(conn.first)) {
						for (auto i : newsig)
							bit2sinks[i].push_back(cell);
						for (auto i : conn.second)
							bit_users[i].insert(mapped_cell->name);
					}
					if (cell->output(conn.first))
						for (auto i : conn.second)
							bit_drivers[i].insert(mapped_cell->name);
				}
			}
		}

		for (auto existing_cell : boxes) {
			Cell *cell = module->cell(remap_name(existing_cell->name));
			if (cell) {
				for (auto &conn : existing_cell->connections()) {
					if (!conn.second.is_wire())
						continue;
					Wire *wire = conn.second.as_wire();
					if (!wire->get_bool_attribute(ID(abc9_padding)))
						continue;
					cell->unsetPort(conn.first);
					log_debug("Dropping padded port connection for %s (%s) .%s (%s )\n", log_id(cell), cell->type.c_str(), log_id(conn.first), log_signal(conn.second));
				}
				module->swap_names(cell, existing_cell);
			}
			module->remove(existing_cell);
		}

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

		// Now 'unexpose' those wires by undoing
		// the expose operation -- remove them from PO/PI
		// and re-connecting them back together
		for (auto wire : module->wires()) {
			auto it = wire->attributes.find(ID(abc9_scc_break));
			if (it != wire->attributes.end()) {
				wire->attributes.erase(it);
				log_assert(wire->port_output);
				wire->port_output = false;
				std::string name = wire->name.str();
				RTLIL::Wire *i_wire = module->wire(name.substr(0, GetSize(name) - 5));
				log_assert(i_wire);
				log_assert(i_wire->port_input);
				i_wire->port_input = false;
				module->connect(i_wire, wire);
			}
		}
		module->fixup_ports();

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
	void on_register() YS_OVERRIDE
	{
		RTLIL::constpad["abc9.script.default"] = "+&scorr; &sweep; &dc2; &dch -f; &ps; &if {C} {W} {D} {R} -v; &mfs";
		RTLIL::constpad["abc9.script.default.area"] = "+&scorr; &sweep; &dc2; &dch -f; &ps; &if {C} {W} {D} {R} -a -v; &mfs";
		RTLIL::constpad["abc9.script.default.fast"] = "+&if {C} {W} {D} {R} -v";
		// Based on ABC's &flow
		RTLIL::constpad["abc9.script.flow"] = "+&scorr; &sweep;" \
			"&dch -C 500;" \
			/* Round 1 */ \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			/* Round 2 */ \
			"&st; &sopb;" \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			/* Round 3 */ \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;";
		// Based on ABC's &flow2
		RTLIL::constpad["abc9.script.flow2"] = "+&scorr; &sweep;" \
			/* Comm1 */ "&synch2 -K 6 -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			/* Comm2 */ "&dch -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			"&load; &st; &sopb -R 10 -C 4; " \
			/* Comm3 */ "&synch2 -K 6 -C 500; &if -m "/*"-E 5"*/" {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			/* Comm2 */ "&dch -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save; "\
			"&load";
		// Based on ABC's &flow3
		RTLIL::constpad["abc9.script.flow3"] = "+&scorr; &sweep;" \
			"&if {C} {W} {D}; &save; &st; &syn2; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&st; &if {C} -g -K 6; &dch -f; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&st; &if {C} -g -K 6; &synch2; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&mfs";
	}
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9 [options] [selection]\n");
		log("\n");
		log("This pass uses the ABC tool [1] for technology mapping of yosys's internal gate\n");
		log("library to a target architecture. Only fully-selected modules are supported.\n");
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
		log("        for -lut/-luts:\n");
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default")).c_str()+1);
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("\n");
		log("        for -lut/-luts:\n");
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default.fast")).c_str()+1);
		log("\n");
		log("    -D <picoseconds>\n");
		log("        set delay target. the string {D} in the default scripts above is\n");
		log("        replaced by this option when used, and an empty string otherwise\n");
		log("        (indicating best possible delay).\n");
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
		log("    -dff\n");
		log("        also pass $_ABC9_FF_ cells through to ABC. modules with many clock\n");
		log("        domains are marked as such and automatically partitioned by ABC.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("    -showtmp\n");
		log("        print the temp dir name in log. usually this is suppressed so that the\n");
		log("        command output is identical across runs.\n");
		log("\n");
		log("    -box <file>\n");
		log("        pass this file with box library to ABC. Use with -lut.\n");
		log("\n");
		log("Note that this is a logic optimization pass within Yosys that is calling ABC\n");
		log("internally. This is not going to \"run ABC on your design\". It will instead run\n");
		log("ABC on logic snippets extracted from your design. You will not get any useful\n");
		log("output when passing an ABC script that writes a file. Instead write your full\n");
		log("design as an XAIGER file with `write_xaiger' and then load that into ABC\n");
		log("externally if you want to use ABC to convert your design into another format.\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9 pass (technology mapping using ABC9).\n");
		log_push();

#ifdef ABCEXTERNAL
		std::string exe_file = ABCEXTERNAL;
#else
		std::string exe_file = proc_self_dirname() + "yosys-abc";
#endif
		std::string script_file, clk_str, box_file, lut_file;
		std::string delay_target, lutin_shared = "-S 1", wire_delay;
		bool fast_mode = false, dff_mode = false, cleanup = true;
		bool show_tempdir = false;
		bool nomfs = false;
		vector<int> lut_costs;

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

		// get arguments from scratchpad first, then override by command arguments
		std::string lut_arg, luts_arg;
		exe_file = design->scratchpad_get_string("abc9.exe", exe_file /* inherit default value if not set */);
		script_file = design->scratchpad_get_string("abc9.script", script_file);
		if (design->scratchpad.count("abc9.D")) {
			delay_target = "-D " + design->scratchpad_get_string("abc9.D");
		}
		lut_arg = design->scratchpad_get_string("abc9.lut", lut_arg);
		luts_arg = design->scratchpad_get_string("abc9.luts", luts_arg);
		fast_mode = design->scratchpad_get_bool("abc9.fast", fast_mode);
		dff_mode = design->scratchpad_get_bool("abc9.dff", dff_mode);
		cleanup = !design->scratchpad_get_bool("abc9.nocleanup", !cleanup);
		show_tempdir = design->scratchpad_get_bool("abc9.showtmp", show_tempdir);
		box_file = design->scratchpad_get_string("abc9.box", box_file);
		if (design->scratchpad.count("abc9.W")) {
			wire_delay = "-W " + design->scratchpad_get_string("abc9.W");
		}
		nomfs = design->scratchpad_get_bool("abc9.nomfs", nomfs);

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
				lut_arg = args[++argidx];
				continue;
			}
			if (arg == "-luts" && argidx+1 < args.size()) {
				luts_arg = args[++argidx];
				continue;
			}
			if (arg == "-fast") {
				fast_mode = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			if (arg == "-showtmp") {
				show_tempdir = true;
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
			if (arg == "-nomfs") {
				nomfs = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		rewrite_filename(script_file);
		if (!script_file.empty() && !is_absolute_path(script_file) && script_file[0] != '+')
			script_file = std::string(pwd) + "/" + script_file;

		// handle -lut / -luts args
		if (!lut_arg.empty()) {
			string arg = lut_arg;
			if (arg.find_first_not_of("0123456789:") == std::string::npos) {
				size_t pos = arg.find_first_of(':');
				int lut_mode = 0, lut_mode2 = 0;
				if (pos != string::npos) {
					lut_mode = atoi(arg.substr(0, pos).c_str());
					lut_mode2 = atoi(arg.substr(pos+1).c_str());
				} else {
					lut_mode = atoi(arg.c_str());
					lut_mode2 = lut_mode;
				}
				lut_costs.clear();
				for (int i = 0; i < lut_mode; i++)
					lut_costs.push_back(1);
				for (int i = lut_mode; i < lut_mode2; i++)
					lut_costs.push_back(2 << (i - lut_mode));
			}
			else {
				lut_file = arg;
				rewrite_filename(lut_file);
				if (!lut_file.empty() && !is_absolute_path(lut_file) && lut_file[0] != '+')
					lut_file = std::string(pwd) + "/" + lut_file;
			}
		}
		if (!luts_arg.empty()) {
			lut_costs.clear();
			for (auto &tok : split_tokens(luts_arg, ",")) {
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
		}

		// ABC expects a box file for XAIG
		if (box_file.empty())
		    box_file = "+/dummy.box";

		rewrite_filename(box_file);
		if (!box_file.empty() && !is_absolute_path(box_file) && box_file[0] != '+')
		    box_file = std::string(pwd) + "/" + box_file;

		SigMap assign_map;
		CellTypes ct(design);
		for (auto module : design->selected_modules())
		{
			if (module->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(module));
				continue;
			}
			log_assert(!module->attributes.count(ID(abc9_box_id)));

			if (!design->selected_whole_module(module))
				log_error("Can't handle partially selected module %s!\n", log_id(module));

			assign_map.set(module);

			typedef SigSpec clkdomain_t;
			dict<clkdomain_t, int> clk_to_mergeability;

			if (dff_mode)
				for (auto cell : module->cells()) {
					if (cell->type != "$__ABC9_FF_")
						continue;

					Wire *abc9_clock_wire = module->wire(stringf("%s.clock", cell->name.c_str()));
					if (abc9_clock_wire == NULL)
						log_error("'%s.clock' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
					SigSpec abc9_clock = assign_map(abc9_clock_wire);

					clkdomain_t key(abc9_clock);

					auto r = clk_to_mergeability.insert(std::make_pair(abc9_clock, clk_to_mergeability.size() + 1));
					auto r2 YS_ATTRIBUTE(unused) = cell->attributes.insert(std::make_pair(ID(abc9_mergeability), r.first->second));
					log_assert(r2.second);

					Wire *abc9_init_wire = module->wire(stringf("%s.init", cell->name.c_str()));
					if (abc9_init_wire == NULL)
						log_error("'%s.init' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
					log_assert(GetSize(abc9_init_wire) == 1);
					SigSpec abc9_init = assign_map(abc9_init_wire);
					if (!abc9_init.is_fully_const())
						log_error("'%s.init' is not a constant wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
					r2 = cell->attributes.insert(std::make_pair(ID(abc9_init), abc9_init.as_const()));
					log_assert(r2.second);
				}
			else
				for (auto cell : module->cells()) {
					auto inst_module = design->module(cell->type);
					if (!inst_module || !inst_module->get_bool_attribute("\\abc9_flop"))
						continue;
					cell->set_bool_attribute("\\abc9_keep");
				}

			design->selected_active_module = module->name.str();
			abc9_module(design, module, script_file, exe_file, cleanup, lut_costs, dff_mode,
					delay_target, lutin_shared, fast_mode, show_tempdir,
					box_file, lut_file, wire_delay, nomfs);
			design->selected_active_module.clear();
		}

		log_pop();
	}
} Abc9Pass;

PRIVATE_NAMESPACE_END
