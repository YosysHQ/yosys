/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 - 2020  Claire Wolf <claire@symbioticeda.com>
 *  Copyright (C) 2012 - 2020  Diego H     <diego@symbioticeda.com>
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
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <iomanip>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void create_mif (std::string file_name, std::string contents, int depth, int width)
{
	std::ofstream f;
	f.open(file_name+".mif");

	if (f.fail()) {
		log_error("File %s cannot be opened. Check W/R permissions/quota in CWD.\n", file_name.c_str());
	}

	f << stringf("-- Yosys generated MIF file.\n");
	f << stringf("-- The generation of MIF files is still experimental.\n");
	f << stringf("DEPTH = %d;\n", depth);
	f << stringf("WIDTH = %d;\n", width);
	f << stringf("ADDRESS_RADIX=UNS;\n");
	f << stringf("DATA_RADIX=BIN;\n");
	f << stringf("CONTENT BEGIN\n");
	
	// Formatting the data in 0 to depth size -1 fashion as location, and with chunks of width size.
	for (unsigned long iline = 0; iline < contents.length(); iline += width) {
		int didx = depth-1;
		f << "\t" << std::setw(4) << didx << " : " << contents.substr(iline, width) << std::internal << ";" << std::endl;
		depth--;
	}

	f << "END;" << std::endl;
	f.close();
}

static void mifgen(Module *module)
{
	for (auto cell : module->selected_cells()) {
		// Skip non-intel memory cells
		if (!(cell->type.in(ID(altsyncram))))
			continue;

		// Get the values from init parameter. 
		// If contents are don't care, means that memory is not initialized, 
		// so init_type is removed, and init_file needs to be set as UNUSED.
		if (cell->getParam(ID(init_file)).is_fully_undef()) {
			cell->setParam(ID(init_file), RTLIL::Const("UNUSED"));
			cell->unsetParam(ID(init_type));
			log("Skipping memory %s: Memory content is left as don't care or is not initialised.\n", RTLIL::id2cstr(cell->name)); 
			continue;
		}
		
		log("Processing memory %s: The MIF files will be saved in CWD.\n", RTLIL::id2cstr(cell->name));
	
		// Name of the cell is used to save the MIF file using same name.
		std::string mem_name = RTLIL::escape_id(RTLIL::id2cstr(cell->name));
		std::string mif_param = RTLIL::id2cstr(mem_name+".mif");
		// TODO: Check for when A and B ports are different size? (init_file layout).
		int width_a = cell->getParam(ID(width_a)).as_int();
		int depth_a = cell->getParam(ID(numwords_a)).as_int();
		// INIT parameter as a single line string
		Const init = cell->getParam(ID(init_file));
		std::string init_content = init.as_string();

		// Create the mif file
		create_mif (RTLIL::id2cstr(mem_name), init_content, depth_a, width_a);
		// Set the MIF file as a parameter for the current memory cell.
		cell->setParam(ID(init_file), RTLIL::Const(mif_param));
		cell->setParam(ID(init_type), RTLIL::Const("mif"));
	}
}

struct IntelMifGen : public Pass {
	IntelMifGen() : Pass("intel_genmif", "Generate Intel memory contents in MIF format") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    intel_genmif\n");
		log("\n");
		log("Convert the Yosys INIT parameter, to a MIF file that Quartus can process.\n");
		log("This pass also set the parameters \"init_file\" and \"init_type\" depending on\n");
		log("whether the memory is not initialised (init_file=UNUSED) or if\n");
		log("the memory is initialised by user contents (init_file=mif file generated).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing INTEL_GENMIF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			mifgen(module);
	}
} IntelMifGen;

PRIVATE_NAMESPACE_END
