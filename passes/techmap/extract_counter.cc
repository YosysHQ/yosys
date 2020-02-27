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
	int width;						//counter width
	bool count_is_up;				//count up (else down)
	RTLIL::Wire* rwire;				//the register output
	bool has_reset;					//true if we have a reset
	bool has_ce;					//true if we have a clock enable
	bool ce_inverted;				//true if clock enable is active low
	RTLIL::SigSpec rst;				//reset pin
	bool rst_inverted;				//true if reset is active low
	bool rst_to_max;				//true if we reset to max instead of 0
	int count_value;				//value we count from
	RTLIL::SigSpec ce;				//clock signal
	RTLIL::SigSpec clk;				//clock enable, if any
	RTLIL::SigSpec outsig;			//counter overflow output signal
	RTLIL::SigSpec poutsig;			//counter parallel output signal
	bool has_pout;					//whether parallel output is used
	RTLIL::Cell* count_mux;			//counter mux
	RTLIL::Cell* count_reg;			//counter register
	RTLIL::Cell* overflow_cell;		//cell for counter overflow (either inverter reduction or $eq)
	pool<ModIndex::PortInfo> pouts;	//Ports that take a parallel output from us
};

struct CounterExtractionSettings
{
	pool<RTLIL::IdString>& parallel_cells;
	int maxwidth;
	int minwidth;
	bool allow_arst;
	int allowed_dirs;	//0 = down, 1 = up, 2 = both
};

//attempt to extract a counter centered on the given adder cell
//For now we only support DOWN counters.
//TODO: up/down support
int counter_tryextract(
	ModIndex& index,
	Cell *cell,
	CounterExtraction& extract,
	CounterExtractionSettings settings)
{
	SigMap& sigmap = index.sigmap;

	//Both inputs must be unsigned, so don't extract anything with a signed input
	bool a_sign = cell->getParam(ID(A_SIGNED)).as_bool();
	bool b_sign = cell->getParam(ID(B_SIGNED)).as_bool();
	if(a_sign || b_sign)
		return 3;

	//CO and X must be unconnected (exactly one connection to each port)
	if(!is_unconnected(sigmap(cell->getPort(ID(CO))), index))
		return 7;
	if(!is_unconnected(sigmap(cell->getPort(ID(X))), index))
		return 8;

	//true if $alu is performing A - B, else A + B
	bool alu_is_subtract;

	//BI and CI must be both constant 0 or both constant 1 as well
	const RTLIL::SigSpec bi_port = sigmap(cell->getPort(ID(BI)));
	const RTLIL::SigSpec ci_port = sigmap(cell->getPort(ID(CI)));
	if(bi_port.is_fully_const() && bi_port.as_int() == 1 &&
		ci_port.is_fully_const() && ci_port.as_int() == 1)
	{
		alu_is_subtract = true;
	}
	else if(bi_port.is_fully_const() && bi_port.as_int() == 0 &&
		ci_port.is_fully_const() && ci_port.as_int() == 0)
	{
		alu_is_subtract = false;
	}
	else
	{
		return 5;
	}

	//false -> port B connects to value
	//true -> port A connects to value
	bool alu_port_use_a = false;

	if(alu_is_subtract)
	{
		const int a_width = cell->getParam(ID(A_WIDTH)).as_int();
		const int b_width = cell->getParam(ID(B_WIDTH)).as_int();
		const RTLIL::SigSpec b_port = sigmap(cell->getPort(ID::B));

		// down, cnt <= cnt - 1
		if (b_width == 1 && b_port.is_fully_const() && b_port.as_int() == 1)
		{
			// OK
			alu_port_use_a = true;
			extract.count_is_up = false;
		}

		// up, cnt <= cnt - -1
		else if (b_width == a_width && b_port.is_fully_const() && b_port.is_fully_ones())
		{
			// OK
			alu_port_use_a = true;
			extract.count_is_up = true;
		}

		// ???
		else
		{
			return 2;
		}
	}
	else
	{
		const int a_width = cell->getParam(ID(A_WIDTH)).as_int();
		const int b_width = cell->getParam(ID(B_WIDTH)).as_int();
		const RTLIL::SigSpec a_port = sigmap(cell->getPort(ID::A));
		const RTLIL::SigSpec b_port = sigmap(cell->getPort(ID::B));

		// down, cnt <= cnt + -1
		if (b_width == a_width && b_port.is_fully_const() && b_port.is_fully_ones())
		{
			// OK
			alu_port_use_a = true;
			extract.count_is_up = false;
		}
		else if (a_width == b_width && a_port.is_fully_const() && a_port.is_fully_ones())
		{
			// OK
			alu_port_use_a = false;
			extract.count_is_up = false;
		}

		// up, cnt <= cnt + 1
		else if (b_width == 1 && b_port.is_fully_const() && b_port.as_int() == 1)
		{
			// OK
			alu_port_use_a = true;
			extract.count_is_up = true;
		}
		else if (a_width == 1 && a_port.is_fully_const() && a_port.as_int() == 1)
		{
			// OK
			alu_port_use_a = false;
			extract.count_is_up = true;
		}

		// ???
		else
		{
			return 2;
		}
	}

	if (extract.count_is_up && settings.allowed_dirs == 0)
		return 26;
	if (!extract.count_is_up && settings.allowed_dirs == 1)
		return 26;

	//Check if counter is an appropriate size
	int count_width;
	if (alu_port_use_a)
		count_width = cell->getParam(ID(A_WIDTH)).as_int();
	else
		count_width = cell->getParam(ID(B_WIDTH)).as_int();
	extract.width = count_width;
	if( (count_width < settings.minwidth) || (count_width > settings.maxwidth) )
		return 1;

	//Y must have exactly one connection, and it has to be a $mux cell.
	//We must have a direct bus connection from our Y to their A.
	const RTLIL::SigSpec aluy = sigmap(cell->getPort(ID::Y));
	pool<Cell*> y_loads = get_other_cells(aluy, index, cell);
	if(y_loads.size() != 1)
		return 9;
	Cell* count_mux = *y_loads.begin();
	extract.count_mux = count_mux;
	if(count_mux->type != ID($mux))
		return 10;
	if(!is_full_bus(aluy, index, cell, ID::Y, count_mux, ID::A))
		return 11;

	if (extract.count_is_up)
	{
		//B connection of the mux must be 0
		const RTLIL::SigSpec underflow = sigmap(count_mux->getPort(ID::B));
		if(!(underflow.is_fully_const() && underflow.is_fully_zero()))
			return 12;
	}
	else
	{
		//B connection of the mux is our underflow value
		const RTLIL::SigSpec underflow = sigmap(count_mux->getPort(ID::B));
		if(!underflow.is_fully_const())
			return 12;
		extract.count_value = underflow.as_int();
	}

	//S connection of the mux must come from an inverter if down, eq if up
	//(need not be the only load)
	const RTLIL::SigSpec muxsel = sigmap(count_mux->getPort(ID(S)));
	extract.outsig = muxsel;
	pool<Cell*> muxsel_conns = get_other_cells(muxsel, index, count_mux);
	Cell* overflow_cell = NULL;
	for(auto c : muxsel_conns)
	{
		if(extract.count_is_up && c->type != ID($eq))
			continue;
		if(!extract.count_is_up && c->type != ID($logic_not))
			continue;
		if(!is_full_bus(muxsel, index, c, ID::Y, count_mux, ID(S), true))
			continue;

		overflow_cell = c;
		break;
	}
	if(overflow_cell == NULL)
		return 13;
	extract.overflow_cell = overflow_cell;

	//Y connection of the mux must have exactly one load, the counter's internal register, if there's no clock enable
	//If we have a clock enable, Y drives the B input of a mux. A of that mux must come from our register
	const RTLIL::SigSpec muxy = sigmap(count_mux->getPort(ID::Y));
	pool<Cell*> muxy_loads = get_other_cells(muxy, index, count_mux);
	if(muxy_loads.size() != 1)
		return 14;
	Cell* muxload = *muxy_loads.begin();
	Cell* count_reg = muxload;
	Cell* cemux = NULL;
	RTLIL::SigSpec cey;
	if(muxload->type == ID($mux))
	{
		//This mux is probably a clock enable mux.
		//Find our count register (should be our only load)
		cemux = muxload;
		cey = sigmap(cemux->getPort(ID::Y));
		pool<Cell*> cey_loads = get_other_cells(cey, index, cemux);
		if(cey_loads.size() != 1)
			return 24;
		count_reg = *cey_loads.begin();

		if(sigmap(cemux->getPort(ID::Y)) != sigmap(count_reg->getPort(ID(D))))
			return 24;
		//Mux should have A driven by count Q, and B by muxy
		//if A and B are swapped, CE polarity is inverted
		if(sigmap(cemux->getPort(ID::B)) == muxy && 
			sigmap(cemux->getPort(ID::A)) == sigmap(count_reg->getPort(ID(Q))))
		{
			extract.ce_inverted = false;
		}
		else if(sigmap(cemux->getPort(ID::A)) == muxy && 
				sigmap(cemux->getPort(ID::B)) == sigmap(count_reg->getPort(ID(Q))))
		{
			extract.ce_inverted = true;
		}
		else
		{
			return 24;
		}

		//Select of the mux is our clock enable
		extract.has_ce = true;
		extract.ce = sigmap(cemux->getPort(ID(S)));
	}
	else
		extract.has_ce = false;

	extract.count_reg = count_reg;
	if(count_reg->type == ID($dff))
		extract.has_reset = false;
	else if(count_reg->type == ID($adff))
	{
		if (!settings.allow_arst)
			return 25;

		extract.has_reset = true;

		//Check polarity of reset - we may have to add an inverter later on!
		extract.rst_inverted = (count_reg->getParam(ID(ARST_POLARITY)).as_int() != 1);

		//Verify ARST_VALUE is zero or full scale
		int rst_value = count_reg->getParam(ID(ARST_VALUE)).as_int();
		if(rst_value == 0)
			extract.rst_to_max = false;
		else if(rst_value == extract.count_value)
			extract.rst_to_max = true;
		else
			return 23;

		//Save the reset
		extract.rst = sigmap(count_reg->getPort(ID(ARST)));
	}
	//TODO: support synchronous reset
	else
		return 15;

	//Sanity check that we use the ALU output properly
	if(extract.has_ce)
	{
		if(!extract.ce_inverted && !is_full_bus(muxy, index, count_mux, ID::Y, cemux, ID::B))
			return 16;
		if(extract.ce_inverted && !is_full_bus(muxy, index, count_mux, ID::Y, cemux, ID::A))
			return 16;
		if(!is_full_bus(cey, index, cemux, ID::Y, count_reg, ID(D)))
			return 16;
	}
	else if(!is_full_bus(muxy, index, count_mux, ID::Y, count_reg, ID(D)))
		return 16;

	//TODO: Verify count_reg CLK_POLARITY is 1

	//Register output must have exactly two loads, the inverter and ALU
	//(unless we have a parallel output!)
	//If we have a clock enable, 3 is OK
	const RTLIL::SigSpec qport = count_reg->getPort(ID(Q));
	extract.poutsig = qport;
	extract.has_pout = false;
	const RTLIL::SigSpec cnout = sigmap(qport);
	pool<Cell*> cnout_loads = get_other_cells(cnout, index, count_reg);
	unsigned int max_loads = 2;
	if(extract.has_ce)
		max_loads = 3;
	if(cnout_loads.size() > max_loads)
	{
		for(auto c : cnout_loads)
		{
			if(c == overflow_cell)
				continue;
			if(c == cell)
				continue;
			if(c == muxload)
				continue;

			//If we specified a limited set of cells for parallel output, check that we only drive them
			if(!settings.parallel_cells.empty())
			{
				//Make sure we're in the whitelist
				if( settings.parallel_cells.find(c->type) == settings.parallel_cells.end())
					return 17;
			}

			//Figure out what port(s) are driven by it
			//TODO: this can probably be done more efficiently w/o multiple iterations over our whole net?
			//TODO: For what purpose do we actually need extract.pouts?
			for(auto b : qport)
			{
				pool<ModIndex::PortInfo> ports = index.query_ports(b);
				for(auto x : ports)
				{
					if(x.cell != c)
						continue;
					extract.pouts.insert(ModIndex::PortInfo(c, x.port, 0));
					extract.has_pout = true;
				}
			}
		}
	}
	for (auto b : qport)
	{
		if(index.query_is_output(b))
		{
			// Parallel out goes out of module
			extract.has_pout = true;
		}
	}
	if(!extract.count_is_up)
	{
		if(!is_full_bus(cnout, index, count_reg, ID(Q), overflow_cell, ID::A, true))
			return 18;
	}
	else
	{
		if(is_full_bus(cnout, index, count_reg, ID(Q), overflow_cell, ID::A, true))
		{
			// B must be the overflow value
			const RTLIL::SigSpec overflow = sigmap(overflow_cell->getPort(ID::B));
			if(!overflow.is_fully_const())
				return 12;
			extract.count_value = overflow.as_int();
		}
		else if(is_full_bus(cnout, index, count_reg, ID(Q), overflow_cell, ID::B, true))
		{
			// A must be the overflow value
			const RTLIL::SigSpec overflow = sigmap(overflow_cell->getPort(ID::A));
			if(!overflow.is_fully_const())
				return 12;
			extract.count_value = overflow.as_int();
		}
		else
		{
			return 18;
		}
	}
	if(alu_port_use_a && !is_full_bus(cnout, index, count_reg, ID(Q), cell, ID::A, true))
		return 19;
	if(!alu_port_use_a && !is_full_bus(cnout, index, count_reg, ID(Q), cell, ID::B, true))
		return 19;

	//Look up the clock from the register
	extract.clk = sigmap(count_reg->getPort(ID(CLK)));

	if(!extract.count_is_up)
	{
		//Register output net must have an INIT attribute equal to the count value
		extract.rwire = cnout.as_wire();
		if(extract.rwire->attributes.find(ID(init)) == extract.rwire->attributes.end())
			return 20;
		int rinit = extract.rwire->attributes[ID(init)].as_int();
		if(rinit != extract.count_value)
			return 21;
	}
	else
	{
		//Register output net must not have an INIT attribute or it must be zero
		extract.rwire = cnout.as_wire();
		if(extract.rwire->attributes.find(ID(init)) == extract.rwire->attributes.end())
			return 0;
		int rinit = extract.rwire->attributes[ID(init)].as_int();
		if(rinit != 0)
			return 21;
	}

	return 0;
}

void counter_worker(
	ModIndex& index,
	Cell *cell,
	unsigned int& total_counters,
	pool<Cell*>& cells_to_remove,
	pool<pair<Cell*, string>>& cells_to_rename,
	CounterExtractionSettings settings)
{
	SigMap& sigmap = index.sigmap;

	//Core of the counter must be an ALU
	if (cell->type != ID($alu))
		return;

	//A input is the count value. Check if it has COUNT_EXTRACT set.
	//If it's not a wire, don't even try
	auto port = sigmap(cell->getPort(ID::A));
	if(!port.is_wire())
	{
		port = sigmap(cell->getPort(ID::B));
		if(!port.is_wire())
			return;
	}
	RTLIL::Wire* port_wire = port.as_wire();
	bool force_extract = false;
	bool never_extract = false;
	string count_reg_src = port_wire->attributes[ID(src)].decode_string().c_str();
	if(port_wire->attributes.find(ID(COUNT_EXTRACT)) != port_wire->attributes.end())
	{
		pool<string> sa = port_wire->get_strpool_attribute(ID(COUNT_EXTRACT));
		string extract_value;
		if(sa.size() >= 1)
		{
			extract_value = *sa.begin();
			log("  Signal %s declared at %s has COUNT_EXTRACT = %s\n",
				log_id(port_wire),
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
	int reason = counter_tryextract(index, cell, extract, settings);

	//Nonzero code - we could not find a matchable counter.
	//Do nothing, unless extraction was forced in which case give an error
	if(reason != 0)
	{
		static const char* reasons[]=
		{
			"no problem",									//0
			"counter is too large/small",					//1
			"counter does not count by one",				//2
			"counter uses signed math",						//3
			"RESERVED, not implemented",					//4
			"ALU is not an adder/subtractor",				//5
			"RESERVED, not implemented",					//6
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
			"Count register is used outside counter, but not by an allowed cell",		//17
			"Register output is not full bus",				//18
			"Register output is not full bus",				//19
			"No init value found",							//20
			"Underflow value is not equal to init value",	//21
			"RESERVED, not implemented",					//22, kept for compatibility but not used anymore
			"Reset is not to zero or COUNT_TO",				//23
			"Clock enable configuration is unsupported",	//24
			"Async reset used but not permitted",			//25
			"Count direction is not allowed"				//26
		};

		if(force_extract)
		{
			log_error(
			"Counter extraction is set to FORCE on register %s, but a counter could not be inferred (%s)\n",
			log_id(port_wire),
			reasons[reason]);
		}
		return;
	}

	//Get new cell name
	string countname = string("$COUNTx$") + log_id(extract.rwire->name.str());

	//Wipe all of the old connections to the ALU
	cell->unsetPort(ID::A);
	cell->unsetPort(ID::B);
	cell->unsetPort(ID(BI));
	cell->unsetPort(ID(CI));
	cell->unsetPort(ID(CO));
	cell->unsetPort(ID(X));
	cell->unsetPort(ID::Y);
	cell->unsetParam(ID(A_SIGNED));
	cell->unsetParam(ID(A_WIDTH));
	cell->unsetParam(ID(B_SIGNED));
	cell->unsetParam(ID(B_WIDTH));
	cell->unsetParam(ID(Y_WIDTH));

	//Change the cell type
	cell->type = ID($__COUNT_);

	//Hook up resets
	if(extract.has_reset)
	{
		//TODO: support other kinds of reset
		cell->setParam(ID(RESET_MODE), RTLIL::Const("LEVEL"));

		//If the reset is active low, infer an inverter ($__COUNT_ cells always have active high reset)
		if(extract.rst_inverted)
		{
			auto realreset = cell->module->addWire(NEW_ID);
			cell->module->addNot(NEW_ID, extract.rst, RTLIL::SigSpec(realreset));
			cell->setPort(ID(RST), realreset);
		}
		else
			cell->setPort(ID(RST), extract.rst);
	}
	else
	{
		cell->setParam(ID(RESET_MODE), RTLIL::Const("RISING"));
		cell->setPort(ID(RST), RTLIL::SigSpec(false));
	}

	//Hook up other stuff
	//cell->setParam(ID(CLKIN_DIVIDE), RTLIL::Const(1));
	cell->setParam(ID(COUNT_TO), RTLIL::Const(extract.count_value));
	cell->setParam(ID(WIDTH), RTLIL::Const(extract.width));
	cell->setPort(ID(CLK), extract.clk);
	cell->setPort(ID(OUT), extract.outsig);

	//Hook up clock enable
	if(extract.has_ce)
	{
		cell->setParam(ID(HAS_CE), RTLIL::Const(1));
		if(extract.ce_inverted)
		{
			auto realce = cell->module->addWire(NEW_ID);
			cell->module->addNot(NEW_ID, extract.ce, RTLIL::SigSpec(realce));
			cell->setPort(ID(CE), realce);
		}
		else
			cell->setPort(ID(CE), extract.ce);
	}
	else
	{
		cell->setParam(ID(HAS_CE), RTLIL::Const(0));
		cell->setPort(ID(CE), RTLIL::Const(1));
	}

	if(extract.count_is_up)
	{
		cell->setParam(ID(DIRECTION), RTLIL::Const("UP"));
		//XXX: What is this supposed to do?
		cell->setPort(ID(UP), RTLIL::Const(1));
	}
	else
	{
		cell->setParam(ID(DIRECTION), RTLIL::Const("DOWN"));
		cell->setPort(ID(UP), RTLIL::Const(0));
	}

	//Hook up hard-wired ports, default to no parallel output
	cell->setParam(ID(HAS_POUT), RTLIL::Const(0));
	cell->setParam(ID(RESET_TO_MAX), RTLIL::Const(0));

	//Hook up any parallel outputs
	for(auto load : extract.pouts)
	{
		log("    Counter has parallel output to cell %s port %s\n", log_id(load.cell->name), log_id(load.port));
	}
	if(extract.has_pout)
	{
		//Connect it to our parallel output
		cell->setPort(ID(POUT), extract.poutsig);
		cell->setParam(ID(HAS_POUT), RTLIL::Const(1));
	}

	//Delete the cells we've replaced (let opt_clean handle deleting the now-redundant wires)
	cells_to_remove.insert(extract.count_mux);
	cells_to_remove.insert(extract.count_reg);
	cells_to_remove.insert(extract.overflow_cell);

	//Log it
	total_counters ++;
	string reset_type = "non-resettable";
	if(extract.has_reset)
	{
		if(extract.rst_inverted)
			reset_type = "negative";
		else
			reset_type = "positive";

		//TODO: support other kind of reset
		reset_type += " async resettable";
	}
	log("  Found %d-bit (%s) %s counter %s (counting %s %d) for register %s, declared at %s\n",
		extract.width,
		reset_type.c_str(),
		extract.count_is_up ? "up" : "down",
		countname.c_str(),
		extract.count_is_up ? "to" : "from",
		extract.count_value,
		log_id(extract.rwire->name),
		count_reg_src.c_str());

	//Optimize the counter
	//If we have no parallel output, and we have redundant bits, shrink us
	if(!extract.has_pout)
	{
		//TODO: Need to update this when we add support for counters with nonzero reset values
		//to make sure the reset value fits in our bit space too

		//Optimize it
		int newbits = ceil(log2(extract.count_value));
		if(extract.width != newbits)
		{
			cell->setParam(ID(WIDTH), RTLIL::Const(newbits));
			log("    Optimizing out %d unused high-order bits (new width is %d)\n",
				extract.width - newbits,
				newbits);
		}
	}

	//Finally, rename the cell
	cells_to_rename.insert(pair<Cell*, string>(cell, countname));
}

struct ExtractCounterPass : public Pass {
	ExtractCounterPass() : Pass("extract_counter", "Extract GreenPak4 counter cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    extract_counter [options] [selection]\n");
		log("\n");
		log("This pass converts non-resettable or async resettable down counters to\n");
		log("counter cells. Use a target-specific 'techmap' map file to convert those cells\n");
		log("to the actual target cells.\n");
		log("\n");
		log("    -maxwidth N\n");
		log("        Only extract counters up to N bits wide (default 64)\n");
		log("\n");
		log("    -minwidth N\n");
		log("        Only extract counters at least N bits wide (default 2)\n");
		log("\n");
		log("    -allow_arst yes|no\n");
		log("        Allow counters to have async reset (default yes)\n");
		log("\n");
		log("    -dir up|down|both\n");
		log("        Look for up-counters, down-counters, or both (default down)\n");
		log("\n");
		log("    -pout X,Y,...\n");
		log("        Only allow parallel output from the counter to the listed cell types\n");
		log("        (if not specified, parallel outputs are not restricted)\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing EXTRACT_COUNTER pass (find counters in netlist).\n");

		pool<RTLIL::IdString> _parallel_cells;
		CounterExtractionSettings settings
		{
			.parallel_cells = _parallel_cells,
			.maxwidth = 64,
			.minwidth = 2,
			.allow_arst = true,
			.allowed_dirs = 0,
		};

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-pout")
			{
				if(argidx + 1 >= args.size())
				{
					log_error("extract_counter -pout requires an argument\n");
					return;
				}

				std::string pouts = args[++argidx];
				std::string tmp;
				for(size_t i=0; i<pouts.length(); i++)
				{
					if(pouts[i] == ',')
					{
						settings.parallel_cells.insert(RTLIL::escape_id(tmp));
						tmp = "";
					}
					else
						tmp += pouts[i];
				}
				settings.parallel_cells.insert(RTLIL::escape_id(tmp));
				continue;
			}

			if (args[argidx] == "-maxwidth" && argidx+1 < args.size())
			{
				settings.maxwidth = atoi(args[++argidx].c_str());
				continue;
			}

			if (args[argidx] == "-minwidth" && argidx+1 < args.size())
			{
				settings.minwidth = atoi(args[++argidx].c_str());
				continue;
			}

			if (args[argidx] == "-allow_arst" && argidx+1 < args.size())
			{
				auto arg = args[++argidx];
				if (arg == "yes")
					settings.allow_arst = true;
				else if (arg == "no")
					settings.allow_arst = false;
				else
					log_error("Invalid -allow_arst value \"%s\"\n", arg.c_str());
				continue;
			}

			if (args[argidx] == "-dir" && argidx+1 < args.size())
			{
				auto arg = args[++argidx];
				if (arg == "up")
					settings.allowed_dirs = 1;
				else if (arg == "down")
					settings.allowed_dirs = 0;
				else if (arg == "both")
					settings.allowed_dirs = 2;
				else
					log_error("Invalid -dir value \"%s\"\n", arg.c_str());
				continue;
			}
		}
		extra_args(args, argidx, design);

		if (settings.minwidth < 2)
		{
			//A counter with less than 2 bits makes no sense
			log_warning("Minimum counter width is 2 bits wide\n");
			settings.minwidth = 2;
		}

		//Extract all of the counters we could find
		unsigned int total_counters = 0;
		for (auto module : design->selected_modules())
		{
			pool<Cell*> cells_to_remove;
			pool<pair<Cell*, string>> cells_to_rename;

			ModIndex index(module);
			for (auto cell : module->selected_cells())
				counter_worker(index, cell, total_counters, cells_to_remove, cells_to_rename, settings);

			for(auto cell : cells_to_remove)
			{
				//log("Removing cell %s\n", log_id(cell->name));
				module->remove(cell);
			}

			for(auto cpair : cells_to_rename)
			{
				//log("Renaming cell %s to %s\n", log_id(cpair.first->name), cpair.second.c_str());
				module->rename(cpair.first, cpair.second);
			}
		}

		if(total_counters)
			log("Extracted %u counters\n", total_counters);
	}
} ExtractCounterPass;

PRIVATE_NAMESPACE_END
