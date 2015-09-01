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
			if (!f.getline(buffer+buffer_len, buffer_size-buffer_len))
				return false;
		} else
			return true;
	}
}

void parse_blif(RTLIL::Design *design, std::istream &f, std::string dff_name)
{
	RTLIL::Module *module = nullptr;
	RTLIL::Const *lutptr = NULL;
	RTLIL::State lut_default_state = RTLIL::State::Sx;

	dict<RTLIL::IdString, RTLIL::Const> *obj_attributes = nullptr;
	dict<RTLIL::IdString, RTLIL::Const> *obj_parameters = nullptr;

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

			char *cmd = strtok(buffer, " \t\r\n");

			if (!strcmp(cmd, ".model")) {
				if (module != nullptr)
					goto error;
				module = new RTLIL::Module;
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

			if (!strcmp(cmd, ".end")) {
				module->fixup_ports();
				module = nullptr;
				obj_attributes = nullptr;
				obj_parameters = nullptr;
				continue;
			}

			if (!strcmp(cmd, ".inputs") || !strcmp(cmd, ".outputs")) {
				char *p;
				while ((p = strtok(NULL, " \t\r\n")) != NULL) {
					RTLIL::Wire *wire = module->addWire(stringf("\\%s", p));
					if (!strcmp(cmd, ".inputs"))
						wire->port_input = true;
					else
						wire->port_output = true;
				}
				obj_attributes = nullptr;
				obj_parameters = nullptr;
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
					if (obj_attributes == nullptr)
						goto error;
					(*obj_attributes)[id_n] = const_v;
				} else {
					if (obj_parameters == nullptr)
						goto error;
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

				if (module->wires_.count(RTLIL::escape_id(d)) == 0)
					module->addWire(RTLIL::escape_id(d));

				if (module->wires_.count(RTLIL::escape_id(q)) == 0)
					module->addWire(RTLIL::escape_id(q));

				if (clock == nullptr && edge != nullptr) {
					init = edge;
					edge = nullptr;
				}

				if (init != nullptr && (init[0] == '0' || init[0] == '1'))
					module->wire(RTLIL::escape_id(d))->attributes["\\init"] = Const(init[0] == '1' ? 1 : 0, 1);

				if (clock == nullptr)
					goto no_latch_clock;

				if (module->wires_.count(RTLIL::escape_id(clock)) == 0)
					module->addWire(RTLIL::escape_id(clock));

				if (!strcmp(edge, "re"))
					cell = module->addDff(NEW_ID, module->wire(RTLIL::escape_id(clock)),
							module->wire(RTLIL::escape_id(d)), module->wire(RTLIL::escape_id(q)));
				else if (!strcmp(edge, "fe"))
					cell = module->addDff(NEW_ID, module->wire(RTLIL::escape_id(clock)),
							module->wire(RTLIL::escape_id(d)), module->wire(RTLIL::escape_id(q)), false);
				else {
			no_latch_clock:
					cell = module->addCell(NEW_ID, dff_name);
					cell->setPort("\\D", module->wires_.at(RTLIL::escape_id(d)));
					cell->setPort("\\Q", module->wires_.at(RTLIL::escape_id(q)));
				}

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

				while ((p = strtok(NULL, " \t\r\n")) != NULL) {
					char *q = strchr(p, '=');
					if (q == NULL || !q[0] || !q[1])
						goto error;
					*(q++) = 0;
					if (module->wires_.count(RTLIL::escape_id(q)) == 0)
						module->addWire(RTLIL::escape_id(q));
					cell->setPort(RTLIL::escape_id(p), module->wires_.at(RTLIL::escape_id(q)));
				}

				obj_attributes = &cell->attributes;
				obj_parameters = &cell->parameters;
				continue;
			}

			obj_attributes = nullptr;
			obj_parameters = nullptr;

			if (!strcmp(cmd, ".barbuf"))
			{
				char *p = strtok(NULL, " \t\r\n");
				if (p == NULL)
					goto error;

				char *q = strtok(NULL, " \t\r\n");
				if (q == NULL)
					goto error;

				if (module->wires_.count(RTLIL::escape_id(p)) == 0)
					module->addWire(RTLIL::escape_id(p));

				if (module->wires_.count(RTLIL::escape_id(q)) == 0)
					module->addWire(RTLIL::escape_id(q));

				module->connect(module->wires_.at(RTLIL::escape_id(q)), module->wires_.at(RTLIL::escape_id(p)));
				continue;
			}

			if (!strcmp(cmd, ".names"))
			{
				char *p;
				RTLIL::SigSpec input_sig, output_sig;
				while ((p = strtok(NULL, " \t\r\n")) != NULL) {
					RTLIL::Wire *wire;
					if (module->wires_.count(RTLIL::escape_id(p)) > 0) {
						wire = module->wires_.at(RTLIL::escape_id(p));
					} else {
						wire = module->addWire(RTLIL::escape_id(p));
					}
					input_sig.append(wire);
				}
				output_sig = input_sig.extract(input_sig.size()-1, 1);
				input_sig = input_sig.extract(0, input_sig.size()-1);

				if (input_sig.size() == 0) {
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
					module->connect(RTLIL::SigSig(output_sig, state));
					goto continue_without_read;
				}

				RTLIL::Cell *cell = module->addCell(NEW_ID, "$lut");
				cell->parameters["\\WIDTH"] = RTLIL::Const(input_sig.size());
				cell->parameters["\\LUT"] = RTLIL::Const(RTLIL::State::Sx, 1 << input_sig.size());
				cell->setPort("\\A", input_sig);
				cell->setPort("\\Y", output_sig);
				lutptr = &cell->parameters.at("\\LUT");
				lut_default_state = RTLIL::State::Sx;
				continue;
			}

			goto error;
		}

		if (lutptr == NULL)
			goto error;

		char *input = strtok(buffer, " \t\r\n");
		char *output = strtok(NULL, " \t\r\n");

		if (input == NULL || output == NULL || (strcmp(output, "0") && strcmp(output, "1")))
			goto error;

		int input_len = strlen(input);
		if (input_len > 8)
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

error:
	log_error("Syntax error in line %d!\n", line_count);
}

struct BlifFrontend : public Frontend {
	BlifFrontend() : Frontend("blif", "read BLIF file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_blif [filename]\n");
		log("\n");
		log("Load modules from a BLIF file into the current design.\n");
		log("\n");
	}
	virtual void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing BLIF frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			// if (arg == "-lib") {
			// 	flag_lib = true;
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		parse_blif(design, *f, "\\DFF");
	}
} BlifFrontend;

YOSYS_NAMESPACE_END

