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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FsmInfoPass : public Pass {
	FsmInfoPass() : Pass("fsm_info", "print information on finite state machines") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_info [selection]\n");
		log("\n");
		log("This pass dumps all internal information on FSM cells. It can be useful for\n");
		log("analyzing the synthesis process and is called automatically by the 'fsm'\n");
		log("pass so that this information is included in the synthesis log file.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing FSM_INFO pass (dumping all available information on FSM cells).\n");
		extra_args(args, 1, design);

		for (auto mod : design->selected_modules())
			for (auto cell : mod->selected_cells())
				if (cell->type == ID($fsm)) {
					log("\n");
					log("FSM `%s' from module `%s':\n", log_id(cell), log_id(mod));
					FsmData fsm_data;
					fsm_data.copy_from_cell(cell);
					fsm_data.log_info(cell);
				}
	}
} FsmInfoPass;

PRIVATE_NAMESPACE_END
