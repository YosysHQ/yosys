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

static void run_pp3_braminit(Module *module)
{
	for (auto cell : module->selected_cells())
	{
		uint32_t mem[2048];
                int32_t ramDataWidth = 32;
                int32_t ramDataDepth = 512;
                

                log("cell type %s\n", RTLIL::id2cstr(cell->name));
		/* Only consider cells we're interested in */
		if (cell->type != ID(RAM_16K_BLK) &&
		    cell->type != ID(RAM_8K_BLK))
			continue;
                log("found ram block\n");
		if (!cell->hasParam(ID(INIT_FILE)))
			continue;
		std::string init_file = cell->getParam(ID(INIT_FILE)).decode_string();
		cell->unsetParam(ID(INIT_FILE));
		if (init_file == "")
			continue;

		/* Open file */
		log("Processing %s : %s\n", RTLIL::id2cstr(cell->name), init_file.c_str());
                ramDataWidth = cell->getParam(ID(data_width_int)).as_int();
                ramDataDepth = cell->getParam(ID(data_depth_int)).as_int();

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
				else if (cursor >= 0 && cursor < ramDataDepth)
					mem[cursor++] = value;
				else
					log("Attempt to initialize non existent address %d\n", cursor);
			}
		}

		/* Set attributes */
		std::string val = "";
		for (int i=ramDataDepth-1; i>=0; i--) {
			//std::string val = "";
			if (ramDataWidth == 8)
	                     val += std::bitset<8>(mem[i]).to_string();
			else if (ramDataWidth == 16)
	                     val += std::bitset<16>(mem[i]).to_string();
			else if (ramDataWidth == 32)
	                     val += std::bitset<32>(mem[i]).to_string();
		}
		cell->setParam("\\INIT", RTLIL::Const::from_string(val));
	}
}

struct PP3BRAMInitPass : public Pass {
	PP3BRAMInitPass() : Pass("pp3_braminit", "PP3: perform RAM Block initialization from file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    pp3_braminit\n");
		log("\n");
		log("This command processes all PP3 RAM blocks with a non-empty INIT_FILE\n");
		log("parameter and converts it into the required INIT attributes\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing PP3_BRAMINIT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-???") {
			//  continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			run_pp3_braminit(module);
	}
} PP3BRAMInitPass;

PRIVATE_NAMESPACE_END
