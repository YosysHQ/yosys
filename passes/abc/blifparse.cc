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

static bool read_next_line(char *&buffer, size_t &buffer_size, int &line_count, FILE *f)
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
			if (fgets(buffer+buffer_len, buffer_size-buffer_len, f) == NULL)
				return false;
		} else
			return true;
	}
}

RTLIL::Design *abc_parse_blif(FILE *f, std::string dff_name)
{
	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module = new RTLIL::Module;

	RTLIL::Const *lutptr = NULL;
	RTLIL::State lut_default_state = RTLIL::State::Sx;

	module->name = "\\netlist";
	design->add(module);

	size_t buffer_size = 4096;
	char *buffer = (char*)malloc(buffer_size);
	int line_count = 0;

	while (1)
	{
		if (!read_next_line(buffer, buffer_size, line_count, f))
			goto error;

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

			if (!strcmp(cmd, ".model"))
				continue;

			if (!strcmp(cmd, ".end")) {
				module->fixup_ports();
				free(buffer);
				return design;
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
				continue;
			}

			if (!strcmp(cmd, ".latch"))
			{
				char *d = strtok(NULL, " \t\r\n");
				char *q = strtok(NULL, " \t\r\n");

				if (module->wires_.count(RTLIL::escape_id(d)) == 0)
					module->addWire(RTLIL::escape_id(d));

				if (module->wires_.count(RTLIL::escape_id(q)) == 0)
					module->addWire(RTLIL::escape_id(q));

				RTLIL::Cell *cell = module->addCell(NEW_ID, dff_name);
				cell->setPort("\\D", module->wires_.at(RTLIL::escape_id(d)));
				cell->setPort("\\Q", module->wires_.at(RTLIL::escape_id(q)));
				continue;
			}

			if (!strcmp(cmd, ".gate"))
			{
				char *p = strtok(NULL, " \t\r\n");
				if (p == NULL)
					goto error;

				RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(p));

				while ((p = strtok(NULL, " \t\r\n")) != NULL) {
					char *q = strchr(p, '=');
					if (q == NULL || !q[0] || !q[1])
						goto error;
					*(q++) = 0;
					if (module->wires_.count(RTLIL::escape_id(q)) == 0)
						module->addWire(RTLIL::escape_id(q));
					cell->setPort(RTLIL::escape_id(p), module->wires_.at(RTLIL::escape_id(q)));
				}
				continue;
			}

			if (!strcmp(cmd, ".names"))
			{
				char *p;
				RTLIL::SigSpec input_sig, output_sig;
				while ((p = strtok(NULL, " \t\r\n")) != NULL) {
					RTLIL::Wire *wire;
					if (module->wires_.count(stringf("\\%s", p)) > 0) {
						wire = module->wires_.at(stringf("\\%s", p));
					} else {
						wire = module->addWire(stringf("\\%s", p));
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
						state = RTLIL::State::S1;
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
	// delete design;
	// return NULL;
}

YOSYS_NAMESPACE_END

