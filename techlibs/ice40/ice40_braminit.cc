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
#include "kernel/sigtools.h"
#include <stdlib.h>
#include <stdio.h>
#include <bitset>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void run_ice40_braminit(Module *module)
{
	for (auto cell : module->selected_cells())
	{
		uint16_t mem[256];

		/* Only consider cells we're interested in */
		if (cell->type != "\\SB_RAM40_4K" &&
		    cell->type != "\\SB_RAM40_4KNR" &&
		    cell->type != "\\SB_RAM40_4KNW" &&
		    cell->type != "\\SB_RAM40_4KNRNW")
			continue;
		if (!cell->hasParam("\\INIT_FILE"))
			continue;
		std::string init_file = cell->getParam("\\INIT_FILE").decode_string();
		cell->unsetParam("\\INIT_FILE");
		if (init_file == "")
			continue;

		/* Open file */
		log("Processing %s : %s\n", RTLIL::id2cstr(cell->name), init_file.c_str());

		std::ifstream f;
		f.open(init_file.c_str());
		if (f.fail()) {
			log("Can not open file `%s`.\n", init_file.c_str());
			continue;
		}

		/* Defaults to 0 */
		memset(mem, 0x00, sizeof(mem));

		/* Process each line */
		bool in_comment = false;
		int cursor = 0;

		while (!f.eof())
		{
			std::string line, token;
			std::getline(f, line);

			for (int i = 0; i < GetSize(line); i++)
			{
				if (in_comment && line.compare(i, 2, "*/") == 0) {
					line[i] = ' ';
					line[i+1] = ' ';
					in_comment = false;
					continue;
				}
				if (!in_comment && line.compare(i, 2, "/*") == 0)
					in_comment = true;
				if (in_comment)
					line[i] = ' ';
			}

			while (1)
			{
				bool set_cursor = false;
				long value;

				token = next_token(line, " \t\r\n");
				if (token.empty() || token.compare(0, 2, "//") == 0)
					break;

				if (token[0] == '@') {
					token = token.substr(1);
					set_cursor = true;
				}

				const char *nptr = token.c_str();
				char *endptr;
				value = strtol(nptr, &endptr, 16);
				if (!*nptr || *endptr) {
					log("Can not parse %s `%s` for %s.\n",
						set_cursor ? "address" : "value",
						nptr, token.c_str()
					);
					continue;
				}

				if (set_cursor)
					cursor = value;
				else if (cursor >= 0 && cursor < 256)
					mem[cursor++] = value;
				else
					log("Attempt to initialize non existent address %d\n", cursor);
			}
		}

		/* Set attributes */
		const char *hex = "0123456789ABCDEF";
		for (int i=0; i<16; i++) {
			std::string val = "";
			for (int j=15; j>=0; j--)
				val += std::bitset<16>(mem[i*16+j]).to_string();
			cell->setParam("\\INIT_" + std::string(1, hex[i]), RTLIL::Const::from_string(val));
		}
	}
}

struct Ice40BRAMInitPass : public Pass {
	Ice40BRAMInitPass() : Pass("ice40_braminit", "iCE40: perform SB_RAM40_4K initialization from file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_braminit\n");
		log("\n");
		log("This command processes all SB_RAM40_4K blocks with a non-empty INIT_FILE\n");
		log("parameter and converts it into the required INIT_x attributes\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_BRAMINIT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-???") {
			//  continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			run_ice40_braminit(module);
	}
} Ice40BRAMInitPass;

PRIVATE_NAMESPACE_END
