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

#include "blifparse.h"

YOSYS_NAMESPACE_BEGIN

static bool read_next_line(char *&buffer, size_t &buffer_size, int &line_count, std::istream &f)
{
	string strbuf;
	int buffer_len = 0;
	buffer[0] = 0;

	while (1)
	{
		buffer_len += strlen(buffer + buffer_len);
		while (buffer_len > 0 && (buffer[buffer_len-1] == ' ' || buffer[buffer_len-1] == '\t' ||
				buffer[buffer_len-1] == '\r' || buffer[buffer_len-1] == '\n'))
			buffer[--buffer_len] = 0;

		if (buffer_size-buffer_len < 4096) {
			buffer_size *= 2;
			buffer = (char*)realloc(buffer, buffer_size);
		}

		if (buffer_len == 0 || buffer[buffer_len-1] == '\\') {
			if (buffer_len > 0 && buffer[buffer_len-1] == '\\')
				buffer[--buffer_len] = 0;
			line_count++;
			if (!std::getline(f, strbuf))
				return false;
			while (buffer_size-buffer_len < strbuf.size()+1) {
				buffer_size *= 2;
				buffer = (char*)realloc(buffer, buffer_size);
			}
			strcpy(buffer+buffer_len, strbuf.c_str());
		} else
			return true;
	}
}

static std::pair<RTLIL::IdString, int> wideports_split(std::string name)
{
	int pos = -1;

	if (name.empty() || name.back() != ']')
		goto failed;

	for (int i = 0; i+1 < GetSize(name); i++) {
		if (name[i] == '[')
			pos = i;
		else if (name[i] < '0' || name[i] > '9')
			pos = -1;
		else if (i == pos+1 && name[i] == '0' && name[i+1] != ']')
			pos = -1;
	}

	if (pos >= 0)
		return std::pair<RTLIL::IdString, int>("\\" + name.substr(0, pos), atoi(name.c_str() + pos+1)+1);

failed:
	return std::pair<RTLIL::IdString, int>("\\" + name, 0);
}

void parse_blif(RTLIL::Design *design, std::istream &f, std::string dff_name, bool run_clean, bool sop_mode, bool wideports)
{
	RTLIL::Module *module = nullptr;
	RTLIL::Const *lutptr = NULL;
	RTLIL::Cell *sopcell = NULL;
	RTLIL::Cell *lastcell = nullptr;
	RTLIL::State lut_default_state = RTLIL::State::Sx;
	std::string err_reason;
	int blif_maxnum = 0, sopmode = -1;

	auto blif_wire = [&](const std::string &wire_name) -> Wire*
	{
		if (wire_name[0] == '$')
		{
			for (int i = 0; i+1 < GetSize(wire_name); i++)
			{
				if (wire_name[i] != '$')
					continue;

				int len = 0;
				while (i+len+1 < GetSize(wire_name) && '0' <= wire_name[i+len+1] && wire_name[i+len+1] <= '9')
					len++;

				if (len > 0) {
					string num_str = wire_name.substr(i+1, len);
					int num = atoi(num_str.c_str()) & 0x0fffffff;
					blif_maxnum = std::max(blif_maxnum, num);
				}
			}
		}

		IdString wire_id = RTLIL::escape_id(wire_name);
		Wire *wire = module->wire(wire_id);

		if (wire == nullptr)
			wire = module->addWire(wire_id);

		return wire;
	};

	dict<RTLIL::IdString, RTLIL::Const> *obj_attributes = nullptr;
	dict<RTLIL::IdString, RTLIL::Const> *obj_parameters = nullptr;

	dict<RTLIL::IdString, std::pair<int, bool>> wideports_cache;

	size_t buffer_size = 4096;
	char *buffer = (char*)malloc(buffer_size);
	int line_count = 0;

	while (1)
	{
		if (!read_next_line(buffer, buffer_size, line_count, f)) {
			if (module != nullptr)
				goto error;
			free(buffer);
			return;
		}

	continue_without_read:
		if (buffer[0] == '#')
			continue;

		if (buffer[0] == '.')
		{
			if (lutptr) {
				for (auto &bit : lutptr->bits)
					if (bit == RTLIL::State::Sx)
						bit = lut_default_state;
				lutptr = NULL;
				lut_default_state = RTLIL::State::Sx;
			}

			if (sopcell) {
				sopcell = NULL;
				sopmode = -1;
			}

			char *cmd = strtok(buffer, " \t\r\n");

			if (!strcmp(cmd, ".model")) {
				if (module != nullptr)
					goto error;
				module = new RTLIL::Module;
				lastcell = nullptr;
				module->name = RTLIL::escape_id(strtok(NULL, " \t\r\n"));
				obj_attributes = &module->attributes;
				obj_parameters = nullptr;
				if (design->module(module->name))
					log_error("Duplicate definition of module %s in line %d!\n", log_id(module->name), line_count);
				design->add(module);
				continue;
			}

			if (module == nullptr)
				goto error;

			if (!strcmp(cmd, ".end"))
			{
				for (auto &wp : wideports_cache)
				{
					auto name = wp.first;
					int width = wp.second.first;
					bool isinput = wp.second.second;

					RTLIL::Wire *wire = module->addWire(name, width);
					wire->port_input = isinput;
					wire->port_output = !isinput;

					for (int i = 0; i < width; i++) {
						RTLIL::IdString other_name = name.str() + stringf("[%d]", i);
						RTLIL::Wire *other_wire = module->wire(other_name);
						if (other_wire) {
							other_wire->port_input = false;
							other_wire->port_output = false;
							if (isinput)
								module->connect(other_wire, SigSpec(wire, i));
							else
								module->connect(SigSpec(wire, i), other_wire);
						}
					}
				}

				module->fixup_ports();
				wideports_cache.clear();

				if (run_clean)
				{
					Const buffer_lut(vector<RTLIL::State>({State::S0, State::S1}));
					vector<Cell*> remove_cells;

					for (auto cell : module->cells())
						if (cell->type == "$lut" && cell->getParam("\\LUT") == buffer_lut) {
							module->connect(cell->getPort("\\Y"), cell->getPort("\\A"));
							remove_cells.push_back(cell);
						}

					for (auto cell : remove_cells)
						module->remove(cell);

					Wire *true_wire = module->wire("$true");
					Wire *false_wire = module->wire("$false");
					Wire *undef_wire = module->wire("$undef");

					if (true_wire != nullptr)
						module->rename(true_wire, stringf("$true$%d", ++blif_maxnum));

					if (false_wire != nullptr)
						module->rename(false_wire, stringf("$false$%d", ++blif_maxnum));

					if (undef_wire != nullptr)
						module->rename(undef_wire, stringf("$undef$%d", ++blif_maxnum));

					autoidx = std::max(autoidx, blif_maxnum+1);
					blif_maxnum = 0;
				}

				module = nullptr;
				lastcell = nullptr;
				obj_attributes = nullptr;
				obj_parameters = nullptr;
				continue;
			}

			if (!strcmp(cmd, ".inputs") || !strcmp(cmd, ".outputs"))
			{
				char *p;
				while ((p = strtok(NULL, " \t\r\n")) != NULL)
				{
					RTLIL::IdString wire_name(stringf("\\%s", p));
					RTLIL::Wire *wire = module->wire(wire_name);
					if (wire == nullptr)
						wire = module->addWire(wire_name);
					if (!strcmp(cmd, ".inputs"))
						wire->port_input = true;
					else
						wire->port_output = true;

					if (wideports) {
						std::pair<RTLIL::IdString, int> wp = wideports_split(p);
						if (wp.second > 0) {
							wideports_cache[wp.first].first = std::max(wideports_cache[wp.first].first, wp.second);
							wideports_cache[wp.first].second = !strcmp(cmd, ".inputs");
						}
					}
				}
				obj_attributes = nullptr;
				obj_parameters = nullptr;
				continue;
			}

			if (!strcmp(cmd, ".cname"))
			{
				char *p = strtok(NULL, " \t\r\n");
				if (p == NULL)
					goto error;

				if(lastcell == nullptr || module == nullptr)
				{
					err_reason = stringf("No primitive object to attach .cname %s.", p);
					goto error_with_reason;
				}

				module->rename(lastcell, p);
				continue;
			}

			if (!strcmp(cmd, ".attr") || !strcmp(cmd, ".param")) {
				char *n = strtok(NULL, " \t\r\n");
				char *v = strtok(NULL, "\r\n");
				IdString id_n = RTLIL::escape_id(n);
				Const const_v;
				if (v[0] == '"') {
					std::string str(v+1);
					if (str.back() == '"')
						str.resize(str.size()-1);
					const_v = Const(str);
				} else {
					int n = strlen(v);
					const_v.bits.resize(n);
					for (int i = 0; i < n; i++)
						const_v.bits[i] = v[n-i-1] != '0' ? State::S1 : State::S0;
				}
				if (!strcmp(cmd, ".attr")) {
					if (obj_attributes == nullptr) {
						err_reason = stringf("No object to attach .attr too.");
						goto error_with_reason;
					}
					(*obj_attributes)[id_n] = const_v;
				} else {
					if (obj_parameters == nullptr) {
						err_reason = stringf("No object to attach .param too.");
						goto error_with_reason;
					}
					(*obj_parameters)[id_n] = const_v;
				}
				continue;
			}

			if (!strcmp(cmd, ".latch"))
			{
				char *d = strtok(NULL, " \t\r\n");
				char *q = strtok(NULL, " \t\r\n");
				char *edge = strtok(NULL, " \t\r\n");
				char *clock = strtok(NULL, " \t\r\n");
				char *init = strtok(NULL, " \t\r\n");
				RTLIL::Cell *cell = nullptr;

				if (clock == nullptr && edge != nullptr) {
					init = edge;
					edge = nullptr;
				}

				if (init != nullptr && (init[0] == '0' || init[0] == '1'))
					blif_wire(q)->attributes["\\init"] = Const(init[0] == '1' ? 1 : 0, 1);

				if (clock == nullptr)
					goto no_latch_clock;

				if (!strcmp(edge, "re"))
					cell = module->addDff(NEW_ID, blif_wire(clock), blif_wire(d), blif_wire(q));
				else if (!strcmp(edge, "fe"))
					cell = module->addDff(NEW_ID, blif_wire(clock), blif_wire(d), blif_wire(q), false);
				else if (!strcmp(edge, "ah"))
					cell = module->addDlatch(NEW_ID, blif_wire(clock), blif_wire(d), blif_wire(q));
				else if (!strcmp(edge, "al"))
					cell = module->addDlatch(NEW_ID, blif_wire(clock), blif_wire(d), blif_wire(q), false);
				else {
			no_latch_clock:
					if (dff_name.empty()) {
						cell = module->addFf(NEW_ID, blif_wire(d), blif_wire(q));
					} else {
						cell = module->addCell(NEW_ID, dff_name);
						cell->setPort("\\D", blif_wire(d));
						cell->setPort("\\Q", blif_wire(q));
					}
				}

				lastcell = cell;
				obj_attributes = &cell->attributes;
				obj_parameters = &cell->parameters;
				continue;
			}

			if (!strcmp(cmd, ".gate") || !strcmp(cmd, ".subckt"))
			{
				char *p = strtok(NULL, " \t\r\n");
				if (p == NULL)
					goto error;

				IdString celltype = RTLIL::escape_id(p);
				RTLIL::Cell *cell = module->addCell(NEW_ID, celltype);

				dict<RTLIL::IdString, dict<int, SigBit>> cell_wideports_cache;

				while ((p = strtok(NULL, " \t\r\n")) != NULL)
				{
					char *q = strchr(p, '=');
					if (q == NULL || !q[0])
						goto error;
					*(q++) = 0;

					if (wideports) {
						std::pair<RTLIL::IdString, int> wp = wideports_split(p);
						if (wp.second > 0)
							cell_wideports_cache[wp.first][wp.second-1] = blif_wire(q);
						else
							cell->setPort(RTLIL::escape_id(p), *q ? blif_wire(q) : SigSpec());
					} else {
						cell->setPort(RTLIL::escape_id(p), *q ? blif_wire(q) : SigSpec());
					}
				}

				for (auto &it : cell_wideports_cache)
				{
					int width = 0;
					for (auto &b : it.second)
						width = std::max(width, b.first + 1);

					SigSpec sig;

					for (int i = 0; i < width; i++) {
						if (it.second.count(i))
							sig.append(it.second.at(i));
						else
							sig.append(module->addWire(NEW_ID));
					}

					cell->setPort(it.first, sig);
				}

				lastcell = cell;
				obj_attributes = &cell->attributes;
				obj_parameters = &cell->parameters;
				continue;
			}

			obj_attributes = nullptr;
			obj_parameters = nullptr;

			if (!strcmp(cmd, ".barbuf") || !strcmp(cmd, ".conn"))
			{
				char *p = strtok(NULL, " \t\r\n");
				if (p == NULL)
					goto error;

				char *q = strtok(NULL, " \t\r\n");
				if (q == NULL)
					goto error;

				module->connect(blif_wire(q), blif_wire(p));
				continue;
			}

			if (!strcmp(cmd, ".names"))
			{
				char *p;
				RTLIL::SigSpec input_sig, output_sig;
				while ((p = strtok(NULL, " \t\r\n")) != NULL)
					input_sig.append(blif_wire(p));
				output_sig = input_sig.extract(input_sig.size()-1, 1);
				input_sig = input_sig.extract(0, input_sig.size()-1);

				if (input_sig.size() == 0)
				{
					RTLIL::State state = RTLIL::State::Sa;
					while (1) {
						if (!read_next_line(buffer, buffer_size, line_count, f))
							goto error;
						for (int i = 0; buffer[i]; i++) {
							if (buffer[i] == ' ' || buffer[i] == '\t')
								continue;
							if (i == 0 && buffer[i] == '.')
								goto finished_parsing_constval;
							if (buffer[i] == '0') {
								if (state == RTLIL::State::S1)
									goto error;
								state = RTLIL::State::S0;
								continue;
							}
							if (buffer[i] == '1') {
								if (state == RTLIL::State::S0)
									goto error;
								state = RTLIL::State::S1;
								continue;
							}
							goto error;
						}
					}

				finished_parsing_constval:
					if (state == RTLIL::State::Sa)
						state = RTLIL::State::S0;
					if (output_sig.as_wire()->name == "$undef")
						state = RTLIL::State::Sx;
					module->connect(RTLIL::SigSig(output_sig, state));
					goto continue_without_read;
				}

				if (sop_mode)
				{
					sopcell = module->addCell(NEW_ID, "$sop");
					sopcell->parameters["\\WIDTH"] = RTLIL::Const(input_sig.size());
					sopcell->parameters["\\DEPTH"] = 0;
					sopcell->parameters["\\TABLE"] = RTLIL::Const();
					sopcell->setPort("\\A", input_sig);
					sopcell->setPort("\\Y", output_sig);
					sopmode = -1;
					lastcell = sopcell;
				}
				else
				{
					RTLIL::Cell *cell = module->addCell(NEW_ID, "$lut");
					cell->parameters["\\WIDTH"] = RTLIL::Const(input_sig.size());
					cell->parameters["\\LUT"] = RTLIL::Const(RTLIL::State::Sx, 1 << input_sig.size());
					cell->setPort("\\A", input_sig);
					cell->setPort("\\Y", output_sig);
					lutptr = &cell->parameters.at("\\LUT");
					lut_default_state = RTLIL::State::Sx;
					lastcell = cell;
				}
				continue;
			}

			goto error;
		}

		if (lutptr == NULL && sopcell == NULL)
			goto error;

		char *input = strtok(buffer, " \t\r\n");
		char *output = strtok(NULL, " \t\r\n");

		if (input == NULL || output == NULL || (strcmp(output, "0") && strcmp(output, "1")))
			goto error;

		int input_len = strlen(input);

		if (sopcell)
		{
			log_assert(sopcell->parameters["\\WIDTH"].as_int() == input_len);
			sopcell->parameters["\\DEPTH"] = sopcell->parameters["\\DEPTH"].as_int() + 1;

			for (int i = 0; i < input_len; i++)
				switch (input[i]) {
					case '0':
						sopcell->parameters["\\TABLE"].bits.push_back(State::S1);
						sopcell->parameters["\\TABLE"].bits.push_back(State::S0);
						break;
					case '1':
						sopcell->parameters["\\TABLE"].bits.push_back(State::S0);
						sopcell->parameters["\\TABLE"].bits.push_back(State::S1);
						break;
					default:
						sopcell->parameters["\\TABLE"].bits.push_back(State::S0);
						sopcell->parameters["\\TABLE"].bits.push_back(State::S0);
						break;
				}

			if (sopmode == -1) {
				sopmode = (*output == '1');
				if (!sopmode) {
					SigSpec outnet = sopcell->getPort("\\Y");
					SigSpec tempnet = module->addWire(NEW_ID);
					module->addNotGate(NEW_ID, tempnet, outnet);
					sopcell->setPort("\\Y", tempnet);
				}
			} else
				log_assert(sopmode == (*output == '1'));
		}

		if (lutptr)
		{
			if (input_len > 12)
				goto error;

			for (int i = 0; i < (1 << input_len); i++) {
				for (int j = 0; j < input_len; j++) {
					char c1 = input[j];
					if (c1 != '-') {
						char c2 = (i & (1 << j)) != 0 ? '1' : '0';
						if (c1 != c2)
							goto try_next_value;
					}
				}
				lutptr->bits.at(i) = !strcmp(output, "0") ? RTLIL::State::S0 : RTLIL::State::S1;
			try_next_value:;
			}

			lut_default_state = !strcmp(output, "0") ? RTLIL::State::S1 : RTLIL::State::S0;
		}
	}

	return;

error:
	log_error("Syntax error in line %d!\n", line_count);
error_with_reason:
	log_error("Syntax error in line %d: %s\n", line_count, err_reason.c_str());
}

struct BlifFrontend : public Frontend {
	BlifFrontend() : Frontend("blif", "read BLIF file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_blif [filename]\n");
		log("\n");
		log("Load modules from a BLIF file into the current design.\n");
		log("\n");
		log("    -sop\n");
		log("        Create $sop cells instead of $lut cells\n");
		log("\n");
		log("    -wideports\n");
		log("        Merge ports that match the pattern 'name[int]' into a single\n");
		log("        multi-bit port 'name'.\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool sop_mode = false;
		bool wideports = false;

		log_header(design, "Executing BLIF frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-sop") {
				sop_mode = true;
				continue;
			}
			if (arg == "-wideports") {
				wideports = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		parse_blif(design, *f, "", true, sop_mode, wideports);
	}
} BlifFrontend;

YOSYS_NAMESPACE_END

