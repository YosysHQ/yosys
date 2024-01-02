/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  N. Engelhardt <nak@yosyshq.com>
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
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// ============================================================================



struct QlBramMergeWorker {

	// can be used to record parameter values that have to match on both sides
	typedef dict<RTLIL::IdString, RTLIL::Const> MergeableGroupKeyType;

	RTLIL::Module *module;
	dict<MergeableGroupKeyType, pool<RTLIL::Cell*>> mergeable_groups;

	QlBramMergeWorker(RTLIL::Module* module) : module(module)
	{
		const RTLIL::IdString split_cell_type = ID($__QLF_TDP36K);

		for (RTLIL::Cell* cell : module->selected_cells())
		{
			if(cell->type != split_cell_type) continue;
			if(!cell->hasParam(ID(OPTION_SPLIT))) continue;
			if(cell->getParam(ID(OPTION_SPLIT)) != RTLIL::Const(1, 32)) continue;
			mergeable_groups[get_key(cell)].insert(cell);
		}
	}

	static MergeableGroupKeyType get_key(RTLIL::Cell* cell)
	{
		MergeableGroupKeyType key;
		// For now, there are no restrictions on which cells can be merged
		(void) cell;
		return key;
	}

	const dict<RTLIL::IdString, RTLIL::IdString>& param_map(bool second)
	{
		static const dict<RTLIL::IdString, RTLIL::IdString> bram1_map = {
			{ ID(INIT),                     ID(INIT1) },
			{ ID(PORT_A_WIDTH),             ID(PORT_A1_WIDTH) },
			{ ID(PORT_B_WIDTH),             ID(PORT_B1_WIDTH) },
			{ ID(PORT_A_WR_BE_WIDTH),       ID(PORT_A1_WR_BE_WIDTH) },
			{ ID(PORT_B_WR_BE_WIDTH),       ID(PORT_B1_WR_BE_WIDTH) }
		};
		static const dict<RTLIL::IdString, RTLIL::IdString> bram2_map = {
			{ ID(INIT),                     ID(INIT2) },
			{ ID(PORT_A_WIDTH),             ID(PORT_A2_WIDTH) },
			{ ID(PORT_B_WIDTH),             ID(PORT_B2_WIDTH) },
			{ ID(PORT_A_WR_BE_WIDTH),       ID(PORT_A2_WR_BE_WIDTH) },
			{ ID(PORT_B_WR_BE_WIDTH),       ID(PORT_B2_WR_BE_WIDTH) }
		};

		if(second)
			return bram2_map;
		else
			return bram1_map;
	}

	const dict<RTLIL::IdString, RTLIL::IdString>& port_map(bool second)
	{
		static const dict<RTLIL::IdString, RTLIL::IdString> bram1_map = {
			{ ID(PORT_A_CLK),       ID(PORT_A1_CLK) },
			{ ID(PORT_B_CLK),       ID(PORT_B1_CLK) },
			{ ID(PORT_A_CLK_EN),    ID(PORT_A1_CLK_EN) },
			{ ID(PORT_B_CLK_EN),    ID(PORT_B1_CLK_EN) },
			{ ID(PORT_A_ADDR),      ID(PORT_A1_ADDR) },
			{ ID(PORT_B_ADDR),      ID(PORT_B1_ADDR) },
			{ ID(PORT_A_WR_DATA),   ID(PORT_A1_WR_DATA) },
			{ ID(PORT_B_WR_DATA),   ID(PORT_B1_WR_DATA) },
			{ ID(PORT_A_WR_EN),     ID(PORT_A1_WR_EN) },
			{ ID(PORT_B_WR_EN),     ID(PORT_B1_WR_EN) },
			{ ID(PORT_A_WR_BE),     ID(PORT_A1_WR_BE) },
			{ ID(PORT_B_WR_BE),     ID(PORT_B1_WR_BE) },
			{ ID(PORT_A_RD_DATA),   ID(PORT_A1_RD_DATA) },
			{ ID(PORT_B_RD_DATA),   ID(PORT_B1_RD_DATA) }
		};
		static const dict<RTLIL::IdString, RTLIL::IdString> bram2_map = {
			{ ID(PORT_A_CLK),       ID(PORT_A2_CLK) },
			{ ID(PORT_B_CLK),       ID(PORT_B2_CLK) },
			{ ID(PORT_A_CLK_EN),    ID(PORT_A2_CLK_EN) },
			{ ID(PORT_B_CLK_EN),    ID(PORT_B2_CLK_EN) },
			{ ID(PORT_A_ADDR),      ID(PORT_A2_ADDR) },
			{ ID(PORT_B_ADDR),      ID(PORT_B2_ADDR) },
			{ ID(PORT_A_WR_DATA),   ID(PORT_A2_WR_DATA) },
			{ ID(PORT_B_WR_DATA),   ID(PORT_B2_WR_DATA) },
			{ ID(PORT_A_WR_EN),     ID(PORT_A2_WR_EN) },
			{ ID(PORT_B_WR_EN),     ID(PORT_B2_WR_EN) },
			{ ID(PORT_A_WR_BE),     ID(PORT_A2_WR_BE) },
			{ ID(PORT_B_WR_BE),     ID(PORT_B2_WR_BE) },
			{ ID(PORT_A_RD_DATA),   ID(PORT_A2_RD_DATA) },
			{ ID(PORT_B_RD_DATA),   ID(PORT_B2_RD_DATA) }
		};

		if(second)
			return bram2_map;
		else
			return bram1_map;
	}

	void merge_brams(RTLIL::Cell* bram1, RTLIL::Cell* bram2)
	{
		const RTLIL::IdString merged_cell_type = ID($__QLF_TDP36K_MERGED);

		// Create the new cell
		RTLIL::Cell* merged = module->addCell(NEW_ID, merged_cell_type);
		log_debug("Merging split BRAM cells %s and %s -> %s\n", log_id(bram1->name), log_id(bram2->name), log_id(merged->name));

		for (auto &it : param_map(false))
		{
			if(bram1->hasParam(it.first))
				merged->setParam(it.second, bram1->getParam(it.first));
		}
		for (auto &it : param_map(true))
		{
			if(bram2->hasParam(it.first))
				merged->setParam(it.second, bram2->getParam(it.first));
		}

		for (auto &it : port_map(false))
		{
			if (bram1->hasPort(it.first))
				merged->setPort(it.second, bram1->getPort(it.first));
			else
				log_error("Can't find port %s on cell %s!\n", log_id(it.first), log_id(bram1->name));
		}
		for (auto &it : port_map(true))
		{
			if (bram2->hasPort(it.first))
				merged->setPort(it.second, bram2->getPort(it.first));
			else
				log_error("Can't find port %s on cell %s!\n", log_id(it.first), log_id(bram2->name));
		}
		merged->attributes = bram1->attributes;
		for (auto attr: bram2->attributes)
			if (!merged->has_attribute(attr.first))
				merged->attributes.insert(attr);

		// Remove the old cells
		module->remove(bram1);
		module->remove(bram2);

	}

	void merge_bram_groups()
	{
		for (auto &it : mergeable_groups)
		{
			while (it.second.size() > 1)
			{
				merge_brams(it.second.pop(), it.second.pop());
			}
		}
	}

};

struct QlBramMergePass : public Pass {
	
	QlBramMergePass() : Pass("ql_bram_merge", "Infers QuickLogic k6n10f BRAM pairs that can operate independently") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_bram_merge [selection]\n");
		log("\n");
		log("    This pass identifies k6n10f 18K BRAM cells and packs pairs of them together\n");
		log("    into a TDP36K cell operating in split mode\n");
		log("\n");
	}



	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing QL_BRAM_MERGE pass.\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (RTLIL::Module* module : design->selected_modules())
		{
			QlBramMergeWorker worker(module);
			worker.merge_bram_groups();
		}
	}


} QlBramMergePass;

PRIVATE_NAMESPACE_END
