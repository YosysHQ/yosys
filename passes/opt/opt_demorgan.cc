/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017  Clifford Wolf <clifford@clifford.at>
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
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void demorgan_worker(
	ModIndex& index,
	Cell *cell,
	unsigned int& cells_changed)
{
	SigMap& sigmap = index.sigmap;
	auto m = cell->module;

	//TODO: Add support for reduce_xor
	//DeMorgan of XOR is either XOR (if even number of inputs) or XNOR (if odd number)

	if( (cell->type != ID($reduce_and)) && (cell->type != ID($reduce_or)) )
		return;

	auto insig = sigmap(cell->getPort(ID::A));
	log("Inspecting %s cell %s (%d inputs)\n", log_id(cell->type), log_id(cell->name), GetSize(insig));
	int num_inverted = 0;
	for(int i=0; i<GetSize(insig); i++)
	{
		auto b = insig[i];

		//See if this bit is driven by a $not cell
		//TODO: do other stuff like nor/nand?
		pool<ModIndex::PortInfo> ports = index.query_ports(b);
		bool inverted = false;
		for(auto x : ports)
		{
			if(x.port == ID::Y && x.cell->type == ID($_NOT_))
			{
				inverted = true;
				break;
			}
		}

		if(inverted)
			num_inverted ++;
	}

	//Stop if less than half of the inputs are inverted
	if(num_inverted*2 < GetSize(insig))
	{
		log("  %d / %d inputs are inverted, not pushing\n", num_inverted, GetSize(insig));
		return;
	}

	//More than half of the inputs are inverted! Push through
	cells_changed ++;
	log("  %d / %d inputs are inverted, pushing inverter through reduction\n", num_inverted, GetSize(insig));

	//For each input, either add or remove the inverter as needed
	//TODO: this duplicates the loop up above, can we refactor it?
	for(int i=0; i<GetSize(insig); i++)
	{
		auto b = insig[i];

		//See if this bit is driven by a $not cell
		//TODO: do other stuff like nor/nand?
		pool<ModIndex::PortInfo> ports = index.query_ports(b);
		RTLIL::Cell* srcinv = NULL;
		for(auto x : ports)
		{
			if(x.port == ID::Y && x.cell->type == ID($_NOT_))
			{
				srcinv = x.cell;
				break;
			}
		}

		//We are NOT inverted! Add an inverter
		if(!srcinv)
		{
			auto inverted_b = m->addWire(NEW_ID);
			m->addNot(NEW_ID, RTLIL::SigSpec(b), RTLIL::SigSpec(inverted_b));
			insig[i] = inverted_b;
		}

		//We ARE inverted - bypass it
		//Don't automatically delete the inverter since other stuff might still use it
		else
			insig[i] = srcinv->getPort(ID::A);
	}

	//Cosmetic fixup: If our input is just a scrambled version of one bus, rearrange it
	//Reductions are all commutative, so there's no point in having them in a weird order
	bool same_signal = true;
	RTLIL::Wire* srcwire = insig[0].wire;
	dict<int, int> seen_bits;
	for(int i=0; i<GetSize(insig); i++)
		seen_bits[i] = 0;
	for(int i=0; i<GetSize(insig); i++)
	{
		seen_bits[insig[i].offset] ++;
		if(insig[i].wire != srcwire)
		{
			same_signal = false;
			break;
		}
	}
	if(same_signal)
	{
		//Make sure we've seen every bit exactly once
		bool every_bit_once = true;
		for(int i=0; i<GetSize(insig); i++)
		{
			if(seen_bits[i] != 1)
			{
				every_bit_once = false;
				break;
			}
		}

		//All good? Just use the whole wire as-is without any reordering
		//We do have to swap MSB to LSB b/c that's the way the reduction cells seem to work?
		//Unclear on why this isn't sorting properly
		//TODO: can we do SigChunks instead of single bits if we have subsets of a bus?
		if(every_bit_once && (GetSize(insig) == srcwire->width) )
		{
			log("Rearranging bits\n");
			RTLIL::SigSpec newsig;
			for(int i=0; i<GetSize(insig); i++)
				newsig.append(RTLIL::SigBit(srcwire, GetSize(insig) - i - 1));
			insig = newsig;
			insig.sort();
		}
	}

	//Push the new input signal back to the reduction (after bypassing/adding inverters)
	cell->setPort(ID::A, insig);

	//Change the cell type
	if(cell->type == ID($reduce_and))
		cell->type = ID($reduce_or);
	else if(cell->type == ID($reduce_or))
		cell->type = ID($reduce_and);
	//don't change XOR

	//Add an inverter to the output
	auto inverted_output = cell->getPort(ID::Y);
	auto uninverted_output = m->addWire(NEW_ID);
	m->addNot(NEW_ID, RTLIL::SigSpec(uninverted_output), inverted_output);
	cell->setPort(ID::Y, uninverted_output);
}

struct OptDemorganPass : public Pass {
	OptDemorganPass() : Pass("opt_demorgan", "Optimize reductions with DeMorgan equivalents") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_demorgan [selection]\n");
		log("\n");
		log("This pass pushes inverters through $reduce_* cells if this will reduce the\n");
		log("overall gate count of the circuit\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_DEMORGAN pass (push inverters through $reduce_* cells).\n");

		int argidx = 0;
		extra_args(args, argidx, design);

		unsigned int cells_changed = 0;
		for (auto module : design->selected_modules())
		{
			ModIndex index(module);
			for (auto cell : module->selected_cells())
				demorgan_worker(index, cell, cells_changed);
		}

		if(cells_changed)
			log("Pushed inverters through %u reductions\n", cells_changed);
	}
} OptDemorganPass;

PRIVATE_NAMESPACE_END
