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
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

//get the list of cells hooked up to at least one bit of a given net
std::set<Cell*> get_other_cells(const RTLIL::SigSpec& port, ModIndex& index, Cell* src)
{
	std::set<Cell*> rval;
	for(auto b : port)
	{
		pool<ModIndex::PortInfo> ports = index.query_ports(b);
		for(auto x : ports)
		{
			if(x.cell == src)
				continue;
			rval.insert(x.cell);
		}
	}
	return rval;
}

//return true if there is a full-width bus connection between the two named module/port combos
bool is_full_bus(const RTLIL::SigSpec& sig, ModIndex& index, Cell* a, RTLIL::IdString ap, Cell* b, RTLIL::IdString bp)
{
	for(auto s : sig)
	{
		pool<ModIndex::PortInfo> ports = index.query_ports(s);
		bool found_a = false;
		bool found_b = false;
		for(auto x : ports)
		{
			if( (x.cell == a) && (x.port == ap) )
				found_a = true;
			else if( (x.cell == b) && (x.port == bp) )
				found_b = true;
			else
				return false;
		}
		
		if( (!found_a) || (!found_b) )
			return false;
	}
	
	return true;
}

//return true if the signal connects to one port only (nothing on the other end)
bool is_unconnected(const RTLIL::SigSpec& port, ModIndex& index)
{
	for(auto b : port)
	{
		pool<ModIndex::PortInfo> ports = index.query_ports(b);
		if(ports.size() > 1)
			return false;
	}
	
	return true;
}

void counters_worker(SigMap &sigmap, Module *module, Cell *cell)
{
	if (cell->type == "$alu")
	{	
		//GreenPak does not support counters larger than 14 bits so immediately skip anything bigger
		int a_width = cell->getParam("\\A_WIDTH").as_int();
		if(a_width > 14)
			return;
			
		//Second input must be a single bit
		int b_width = cell->getParam("\\B_WIDTH").as_int();
		if(b_width != 1)
			return;
			
		//Both inputs must be unsigned, so don't extract anything with a signed input
		bool a_sign = cell->getParam("\\A_SIGNED").as_bool();
		bool b_sign = cell->getParam("\\B_SIGNED").as_bool();
		if(a_sign || b_sign)
			return;

		//To be a counter, one input of the ALU must be a constant 1
		//TODO: can A or B be swapped in synthesized RTL or is B always the 1?
		const RTLIL::SigSpec b_port = sigmap(cell->getPort("\\B"));
		if(!b_port.is_fully_const() || (b_port.as_int() != 1) )
			return;
			
		//BI and CI must be constant 1 as well
		const RTLIL::SigSpec bi_port = sigmap(cell->getPort("\\BI"));
		if(!bi_port.is_fully_const() || (bi_port.as_int() != 1) )
			return;
		const RTLIL::SigSpec ci_port = sigmap(cell->getPort("\\CI"));
		if(!ci_port.is_fully_const() || (ci_port.as_int() != 1) )
			return;
		
		//Index the module
		ModIndex index(module);
		
		//We found a decrementer. Not sure if it's a counter yet but log for debugging
		log("    Found candidate counter %s (width %d)\n", cell->name.c_str(), a_width);
			
		//CO and X must be unconnected (exactly one connection to each port)
		if(!is_unconnected(sigmap(cell->getPort("\\CO")), index))
			return;
		if(!is_unconnected(sigmap(cell->getPort("\\X")), index))
			return;
			
		//Y must have exactly one connection, and it has to be a $mux cell.
		//We must have a direct bus connection from our Y to their A.
		const RTLIL::SigSpec aluy = sigmap(cell->getPort("\\Y"));
		std::set<Cell*> y_loads = get_other_cells(aluy, index, cell);
		if(y_loads.size() != 1)
			return;
		Cell* count_mux = *y_loads.begin();
		if(count_mux->type != "$mux")
			return;
		if(!is_full_bus(aluy, index, cell, "\\Y", count_mux, "\\A"))
			return;
		
		//B connection of the mux is our overflow value
		const RTLIL::SigSpec overflow = sigmap(count_mux->getPort("\\B"));
		if(!overflow.is_fully_const())
			return;
		int count_value = overflow.as_int();
		
		//TODO: S connection of the mux must come from an inverter
		
		//Y connection of the mux must have exactly one load, the counter's internal register
		const RTLIL::SigSpec muxy = sigmap(count_mux->getPort("\\Y"));
		std::set<Cell*> muxy_loads = get_other_cells(muxy, index, count_mux);
		if(muxy_loads.size() != 1)
			return;
		Cell* count_reg = *muxy_loads.begin();
		if(count_reg->type != "$dff")			//TODO: support dffr/dffs?
			return;
		if(!is_full_bus(muxy, index, count_mux, "\\Y", count_reg, "\\D"))
			return;
		
		log("        Looks like a counter so far (count value = %d, count_reg = %s)\n",
			count_value, count_reg->name.c_str());
		
		
		/*
		log("Converting %s cell %s.%s to $adff.\n", log_id(cell->type), log_id(module), log_id(cell));

		if (GetSize(setctrl) == 1) {
			cell->setPort("\\ARST", setctrl);
			cell->setParam("\\ARST_POLARITY", setpol);
		} else {
			cell->setPort("\\ARST", clrctrl);
			cell->setParam("\\ARST_POLARITY", clrpol);
		}

		cell->type = "$adff";
		cell->unsetPort("\\SET");
		cell->unsetPort("\\CLR");
		cell->setParam("\\ARST_VALUE", reset_val);
		cell->unsetParam("\\SET_POLARITY");
		cell->unsetParam("\\CLR_POLARITY");

		return;
		*/
	}
}

struct CountersPass : public Pass {
	CountersPass() : Pass("counters", "Extract counter cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    counters [options] [selection]\n");
		log("\n");
		log("This pass converts resettable down counters to GreenPak counter cells\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing COUNTERS pass (mapping counters to GP_COUNTx cells).\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-v") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);
		
		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);
			for (auto cell : module->selected_cells())
				counters_worker(sigmap, module, cell);
		}
		
	}
} CountersPass;

PRIVATE_NAMESPACE_END
