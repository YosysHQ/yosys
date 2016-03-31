/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2016  Clifford Wolf <clifford@clifford.at>
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
pool<Cell*> get_other_cells(const RTLIL::SigSpec& port, ModIndex& index, Cell* src)
{
	pool<Cell*> rval;
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

//return true if there is a full-width bus connection from cell a port ap to cell b port bp
//if other_conns_allowed is false, then we require a strict point to point connection (no other links)
bool is_full_bus(
	const RTLIL::SigSpec& sig,
	ModIndex& index,
	Cell* a,
	RTLIL::IdString ap,
	Cell* b,
	RTLIL::IdString bp,
	bool other_conns_allowed = false)
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
			else if(!other_conns_allowed)
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

void greenpak4_counters_worker(ModIndex& index, Module *module, Cell *cell, unsigned int& total_counters)
{
	SigMap& sigmap = index.sigmap;
	
	//Core of the counter must be an ALU
	if (cell->type != "$alu")
		return;
	
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
				
	//CO and X must be unconnected (exactly one connection to each port)
	if(!is_unconnected(sigmap(cell->getPort("\\CO")), index))
		return;
	if(!is_unconnected(sigmap(cell->getPort("\\X")), index))
		return;
		
	//Y must have exactly one connection, and it has to be a $mux cell.
	//We must have a direct bus connection from our Y to their A.
	const RTLIL::SigSpec aluy = sigmap(cell->getPort("\\Y"));
	pool<Cell*> y_loads = get_other_cells(aluy, index, cell);
	if(y_loads.size() != 1)
		return;
	Cell* count_mux = *y_loads.begin();
	if(count_mux->type != "$mux")
		return;
	if(!is_full_bus(aluy, index, cell, "\\Y", count_mux, "\\A"))
		return;

	//B connection of the mux is our underflow value
	const RTLIL::SigSpec underflow = sigmap(count_mux->getPort("\\B"));
	if(!underflow.is_fully_const())
		return;
	int count_value = underflow.as_int();
	
	//S connection of the mux must come from an inverter (need not be the only load)
	const RTLIL::SigSpec muxsel = sigmap(count_mux->getPort("\\S"));
	pool<Cell*> muxsel_conns = get_other_cells(muxsel, index, count_mux);
	Cell* underflow_inv = NULL;
	for(auto c : muxsel_conns)
	{		
		if(c->type != "$logic_not")
			continue;
		if(!is_full_bus(muxsel, index, c, "\\Y", count_mux, "\\S", true))
			continue;
	
		underflow_inv = c;
		break;
	}
	if(underflow_inv == NULL)
		return;
	
	//Y connection of the mux must have exactly one load, the counter's internal register
	const RTLIL::SigSpec muxy = sigmap(count_mux->getPort("\\Y"));
	pool<Cell*> muxy_loads = get_other_cells(muxy, index, count_mux);
	if(muxy_loads.size() != 1)
		return;
	Cell* count_reg = *muxy_loads.begin();
	if(count_reg->type != "$dff")			//TODO: support dffr/dffs?
		return;
	if(!is_full_bus(muxy, index, count_mux, "\\Y", count_reg, "\\D"))
		return;
		
	//Register output must have exactly two loads, the inverter and ALU
	const RTLIL::SigSpec cnout = sigmap(count_reg->getPort("\\Q"));
	pool<Cell*> cnout_loads = get_other_cells(cnout, index, count_reg);
	if(cnout_loads.size() != 2)
		return;
	if(!is_full_bus(cnout, index, count_reg, "\\Q", underflow_inv, "\\A", true))
		return;
	if(!is_full_bus(cnout, index, count_reg, "\\Q", cell, "\\A", true))
		return;
		
	//Look up the clock from the register
	const RTLIL::SigSpec clk = sigmap(count_reg->getPort("\\CLK"));
	
	//Register output net must have an INIT attribute equal to the count value
	auto rwire = cnout.as_wire();
	if(rwire->attributes.find("\\init") == rwire->attributes.end())
		return;
	int rinit = rwire->attributes["\\init"].as_int();
	if(rinit != count_value)
		return;
	
	//Figure out the final cell type based on the counter size
	string celltype = "\\GP_COUNT8";
	if(a_width > 8)
		celltype = "\\GP_COUNT14";
	
	//Log it
	total_counters ++;
	string count_reg_src = rwire->attributes["\\src"].decode_string().c_str();
	log("  Found %d-bit non-resettable down counter (from %d) for register %s declared at %s\n",
		a_width,
		count_value,
		log_id(rwire->name),
		count_reg_src.c_str());
		
	//Wipe all of the old connections to the ALU
	cell->unsetPort("\\A");
	cell->unsetPort("\\B");
	cell->unsetPort("\\BI");
	cell->unsetPort("\\CI");
	cell->unsetPort("\\CO");
	cell->unsetPort("\\X");
	cell->unsetPort("\\Y");
	cell->unsetParam("\\A_SIGNED");
	cell->unsetParam("\\A_WIDTH");
	cell->unsetParam("\\B_SIGNED");
	cell->unsetParam("\\B_WIDTH");
	cell->unsetParam("\\Y_WIDTH");
	
	//Change the cell type
	cell->type = celltype;
	
	//Hook it up to everything
	cell->setParam("\\RESET_MODE", RTLIL::Const("RISING"));
	cell->setParam("\\CLKIN_DIVIDE", RTLIL::Const(1));
	cell->setParam("\\COUNT_TO", RTLIL::Const(count_value));
	cell->setPort("\\CLK", clk);
	cell->setPort("\\RST", RTLIL::SigSpec(false));
	cell->setPort("\\OUT", muxsel);
	
	//Delete the cells we've replaced (let opt_clean handle deleting the now-redundant wires)
	module->remove(count_mux);
	module->remove(count_reg);
	module->remove(underflow_inv);
}

struct Greenpak4CountersPass : public Pass {
	Greenpak4CountersPass() : Pass("greenpak4_counters", "Extract GreenPak4 counter cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    greenpak4_counters [options] [selection]\n");
		log("\n");
		log("This pass converts non-resettable down counters to GreenPak4 counter cells\n");
		log("(All other GreenPak4 counter modes must be instantiated manually for now.)\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing GREENPAK4_COUNTERS pass (mapping counters to hard IP blocks).\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-v") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);
		
		unsigned int total_counters = 0;
		for (auto module : design->selected_modules())
		{
			ModIndex index(module);
			for (auto cell : module->selected_cells())
				greenpak4_counters_worker(index, module, cell, total_counters);
		}
		
		if(total_counters)
			log("Extracted %u counters\n", total_counters);
		
	}
} Greenpak4CountersPass;

PRIVATE_NAMESPACE_END
