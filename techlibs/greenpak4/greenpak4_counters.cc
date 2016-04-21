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

struct CounterExtraction
{
	int width;					//counter width
	RTLIL::Wire* rwire;			//the register output
	bool has_reset;				//true if we have a reset
	RTLIL::SigSpec rst;			//reset pin
	int count_value;			//value we count from
	RTLIL::SigSpec clk;			//clock signal
	RTLIL::SigSpec outsig;		//counter output signal
	RTLIL::Cell* count_mux;		//counter mux
	RTLIL::Cell* count_reg;		//counter register
	RTLIL::Cell* underflow_inv;	//inverter reduction for output-underflow detect
};

//attempt to extract a counter centered on the given cell
int greenpak4_counters_tryextract(ModIndex& index, Cell *cell, CounterExtraction& extract)
{
	SigMap& sigmap = index.sigmap;
	
	//GreenPak does not support counters larger than 14 bits so immediately skip anything bigger
	int a_width = cell->getParam("\\A_WIDTH").as_int();
	extract.width = a_width;
	if(a_width > 14)
		return 1;
		
	//Second input must be a single bit
	int b_width = cell->getParam("\\B_WIDTH").as_int();
	if(b_width != 1)
		return 2;
		
	//Both inputs must be unsigned, so don't extract anything with a signed input
	bool a_sign = cell->getParam("\\A_SIGNED").as_bool();
	bool b_sign = cell->getParam("\\B_SIGNED").as_bool();
	if(a_sign || b_sign)
		return 3;

	//To be a counter, one input of the ALU must be a constant 1
	//TODO: can A or B be swapped in synthesized RTL or is B always the 1?
	const RTLIL::SigSpec b_port = sigmap(cell->getPort("\\B"));
	if(!b_port.is_fully_const() || (b_port.as_int() != 1) )
		return 4;
		
	//BI and CI must be constant 1 as well
	const RTLIL::SigSpec bi_port = sigmap(cell->getPort("\\BI"));
	if(!bi_port.is_fully_const() || (bi_port.as_int() != 1) )
		return 5;
	const RTLIL::SigSpec ci_port = sigmap(cell->getPort("\\CI"));
	if(!ci_port.is_fully_const() || (ci_port.as_int() != 1) )
		return 6;
				
	//CO and X must be unconnected (exactly one connection to each port)
	if(!is_unconnected(sigmap(cell->getPort("\\CO")), index))
		return 7;
	if(!is_unconnected(sigmap(cell->getPort("\\X")), index))
		return 8;
		
	//Y must have exactly one connection, and it has to be a $mux cell.
	//We must have a direct bus connection from our Y to their A.
	const RTLIL::SigSpec aluy = sigmap(cell->getPort("\\Y"));
	pool<Cell*> y_loads = get_other_cells(aluy, index, cell);
	if(y_loads.size() != 1)
		return 9;
	Cell* count_mux = *y_loads.begin();
	extract.count_mux = count_mux;
	if(count_mux->type != "$mux")
		return 10;
	if(!is_full_bus(aluy, index, cell, "\\Y", count_mux, "\\A"))
		return 11;

	//B connection of the mux is our underflow value
	const RTLIL::SigSpec underflow = sigmap(count_mux->getPort("\\B"));
	if(!underflow.is_fully_const())
		return 12;
	extract.count_value = underflow.as_int();
	
	//S connection of the mux must come from an inverter (need not be the only load)
	const RTLIL::SigSpec muxsel = sigmap(count_mux->getPort("\\S"));
	extract.outsig = muxsel;
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
		return 13;
	extract.underflow_inv = underflow_inv;
	
	//Y connection of the mux must have exactly one load, the counter's internal register
	const RTLIL::SigSpec muxy = sigmap(count_mux->getPort("\\Y"));
	pool<Cell*> muxy_loads = get_other_cells(muxy, index, count_mux);
	if(muxy_loads.size() != 1)
		return 14;
	Cell* count_reg = *muxy_loads.begin();
	extract.count_reg = count_reg;
	if(count_reg->type == "$dff")
		extract.has_reset = false;
	else if(count_reg->type == "$adff")
	{
		extract.has_reset = true;
		
		//Verify ARST_VALUE is zero and ARST_POLARITY is 1
		//TODO: infer an inverter to make it 1 if necessary, so we can support negative level resets?
		if(count_reg->getParam("\\ARST_POLARITY").as_int() != 1)
			return 22;
		if(count_reg->getParam("\\ARST_VALUE").as_int() != 0)
			return 23;
			
		//Save the reset
		extract.rst = sigmap(count_reg->getPort("\\ARST"));
	}
	//TODO: support synchronous reset
	else
		return 15;
	if(!is_full_bus(muxy, index, count_mux, "\\Y", count_reg, "\\D"))
		return 16;
		
	//TODO: Verify count_reg CLK_POLARITY is 1
		
	//Register output must have exactly two loads, the inverter and ALU
	const RTLIL::SigSpec cnout = sigmap(count_reg->getPort("\\Q"));
	pool<Cell*> cnout_loads = get_other_cells(cnout, index, count_reg);
	if(cnout_loads.size() != 2)
		return 17;
	if(!is_full_bus(cnout, index, count_reg, "\\Q", underflow_inv, "\\A", true))
		return 18;
	if(!is_full_bus(cnout, index, count_reg, "\\Q", cell, "\\A", true))
		return 19;
		
	//Look up the clock from the register
	extract.clk = sigmap(count_reg->getPort("\\CLK"));
	
	//Register output net must have an INIT attribute equal to the count value
	extract.rwire = cnout.as_wire();
	if(extract.rwire->attributes.find("\\init") == extract.rwire->attributes.end())
		return 20;
	int rinit = extract.rwire->attributes["\\init"].as_int();
	if(rinit != extract.count_value)
		return 21;
		
	return 0;
}

void greenpak4_counters_worker(
	ModIndex& index,
	Cell *cell,
	unsigned int& total_counters,
	pool<Cell*>& cells_to_remove)
{
	SigMap& sigmap = index.sigmap;
	
	//Core of the counter must be an ALU
	if (cell->type != "$alu")
		return;
	
	//A input is the count value. Check if it has COUNT_EXTRACT set.
	//If it's not a wire, don't even try
	auto port = sigmap(cell->getPort("\\A"));
	if(!port.is_wire())
		return;
	RTLIL::Wire* a_wire = port.as_wire();
	bool force_extract = false;
	bool never_extract = false;
	string count_reg_src = a_wire->attributes["\\src"].decode_string().c_str();
	if(a_wire->attributes.find("\\COUNT_EXTRACT") != a_wire->attributes.end())
	{
		pool<string> sa = a_wire->get_strpool_attribute("\\COUNT_EXTRACT");
		string extract_value;
		if(sa.size() >= 1)
		{
			extract_value = *sa.begin();
			log("  Signal %s declared at %s has COUNT_EXTRACT = %s\n",
				log_id(a_wire),
				count_reg_src.c_str(),
				extract_value.c_str());
				
			if(extract_value == "FORCE")
				force_extract = true;
			else if(extract_value == "NO")
				never_extract = true;
			else if(extract_value == "AUTO")
			{}	//default
			else
				log_error("  Illegal COUNT_EXTRACT value %s (must be one of FORCE, NO, AUTO)\n",
					extract_value.c_str());
		}
	}
	
	//If we're explicitly told not to extract, don't infer a counter
	if(never_extract)
		return;
	
	//Attempt to extract a counter
	CounterExtraction extract;
	int reason = greenpak4_counters_tryextract(index, cell, extract);
	
	//Nonzero code - we could not find a matchable counter.
	//Do nothing, unless extraction was forced in which case give an error
	if(reason != 0)
	{
		static const char* reasons[24]=
		{
			"no problem",									//0
			"counter is larger than 14 bits",				//1
			"counter does not count by one",				//2
			"counter uses signed math",						//3
			"counter does not count by one",				//4
			"ALU is not a subtractor",						//5
			"ALU is not a subtractor",						//6
			"ALU ports used outside counter",				//7
			"ALU ports used outside counter",				//8
			"ALU output used outside counter",				//9
			"ALU output is not a mux",						//10
			"ALU output is not full bus",					//11
			"Underflow value is not constant",				//12
			"No underflow detector found",					//13
			"Mux output is used outside counter",			//14
			"Counter reg is not DFF/ADFF",					//15
			"Counter input is not full bus",				//16
			"Count register is used outside counter",		//17
			"Register output is not full bus",				//18
			"Register output is not full bus",				//19
			"No init value found",							//20
			"Underflow value is not equal to init value",	//21
			"Reset polarity is not positive",				//22
			"Reset is not to zero"							//23
		};
		
		if(force_extract)
		{
			log_error(
			"Counter extraction is set to FORCE on register %s, but a counter could not be inferred (%s)\n",
			log_id(a_wire),
			reasons[reason]);
		}
		return;
	}
	
	//Figure out the final cell type based on the counter size
	string celltype = "\\GP_COUNT8";
	if(extract.width > 8)
		celltype = "\\GP_COUNT14";
	
	//Log it
	total_counters ++;
	string reset_type = "non-resettable";
	if(extract.has_reset)
	{
		//TODO: support other kind of reset
		reset_type = "async resettable";
	}
	log("  Found %d-bit %s down counter (from %d) for register %s declared at %s\n",
		extract.width,
		reset_type.c_str(),
		extract.count_value,
		log_id(extract.rwire->name),
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
	
	//Hook up resets
	if(extract.has_reset)
	{
		//TODO: support other kinds of reset
		cell->setParam("\\RESET_MODE", RTLIL::Const("LEVEL"));
		cell->setPort("\\RST", extract.rst);
	}
	else
	{
		cell->setParam("\\RESET_MODE", RTLIL::Const("RISING"));
		cell->setPort("\\RST", RTLIL::SigSpec(false));
	}
	
	//Hook up other stuff
	cell->setParam("\\CLKIN_DIVIDE", RTLIL::Const(1));
	cell->setParam("\\COUNT_TO", RTLIL::Const(extract.count_value));
	
	cell->setPort("\\CLK", extract.clk);
	cell->setPort("\\OUT", extract.outsig);
	
	//Delete the cells we've replaced (let opt_clean handle deleting the now-redundant wires)
	cells_to_remove.insert(extract.count_mux);
	cells_to_remove.insert(extract.count_reg);
	cells_to_remove.insert(extract.underflow_inv);
}

struct Greenpak4CountersPass : public Pass {
	Greenpak4CountersPass() : Pass("greenpak4_counters", "Extract GreenPak4 counter cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    greenpak4_counters [options] [selection]\n");
		log("\n");
		log("This pass converts non-resettable or async resettable down counters to GreenPak4\n");
		log("counter cells (All other GreenPak4 counter modes must be instantiated manually.)\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing GREENPAK4_COUNTERS pass (mapping counters to hard IP blocks).\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-v") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);
		
		//Extract all of the counters we could find
		unsigned int total_counters = 0;
		for (auto module : design->selected_modules())
		{
			pool<Cell*> cells_to_remove;
			
			ModIndex index(module);
			for (auto cell : module->selected_cells())
				greenpak4_counters_worker(index, cell, total_counters, cells_to_remove);
				
			for(auto cell : cells_to_remove)
				module->remove(cell);
		}
		
		if(total_counters)
			log("Extracted %u counters\n", total_counters);
	}
} Greenpak4CountersPass;

PRIVATE_NAMESPACE_END
