/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  Miodrag Milanovic <miodrag@symbioticeda.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AnlogicEqnPass : public Pass {
	AnlogicEqnPass() : Pass("anlogic_eqn", "Anlogic: Calculate equations for luts") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    anlogic_eqn [selection]\n");
		log("\n");
		log("Calculate equations for luts since bitstream generator depends on it.\n");
		log("\n");
	}

	Const init2eqn(Const init, int inputs)
	{
		std::string init_bits = init.as_string();
		const char* names[] = { "A" , "B", "C", "D", "E", "F" };

		std::string eqn;
		int width = (int)pow(2,inputs);
		for(int i=0;i<width;i++)
		{
			if (init_bits[width-1-i]=='1')
			{
				eqn += "(";
				for(int j=0;j<inputs;j++)
				{
					if (i & (1<<j))
						eqn += names[j];
					else
						eqn += std::string("~") + names[j];

					if (j!=(inputs-1)) eqn += "*";
				}
				eqn += ")+";
			}
		}
		if (eqn.empty()) return Const("0");
		eqn = eqn.substr(0, eqn.length()-1);
		return Const(eqn);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ANLOGIC_EQN pass (calculate equations for luts).\n");

		extra_args(args, args.size(), design);

		int cnt = 0;
		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\AL_MAP_LUT1")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),1));
					cnt++;
				}
				if (cell->type == "\\AL_MAP_LUT2")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),2));
					cnt++;
				}
				if (cell->type == "\\AL_MAP_LUT3")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),3));
					cnt++;
				}
				if (cell->type == "\\AL_MAP_LUT4")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),4));
					cnt++;
				}
				if (cell->type == "\\AL_MAP_LUT5")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),5));
					cnt++;
				}
				if (cell->type == "\\AL_MAP_LUT6")
				{
					cell->setParam("\\EQN", init2eqn(cell->getParam("\\INIT"),6));
					cnt++;
				}
			}
		}
		log_header(design, "Updated %d of AL_MAP_LUT* elements with equation.\n", cnt);
	}
} AnlogicEqnPass;

PRIVATE_NAMESPACE_END
