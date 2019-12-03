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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/cellaigs.h"
#include "kernel/log.h"
#include <algorithm>
#include <string>
#include <regex>
#include <vector>
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

pool<string> used_names;
dict<IdString, string> namecache;
int autoid_counter;

typedef unsigned FDirection;
static const FDirection FD_NODIRECTION = 0x0;
static const FDirection FD_IN = 0x1;
static const FDirection FD_OUT = 0x2;
static const FDirection FD_INOUT = 0x3;
static const int FIRRTL_MAX_DSH_WIDTH_ERROR = 20; // For historic reasons, this is actually one greater than the maximum allowed shift width

// Get a port direction with respect to a specific module.
FDirection getPortFDirection(IdString id, Module *module)
{
	Wire *wire = module->wires_.at(id);
	FDirection direction = FD_NODIRECTION;
	if (wire && wire->port_id)
	{
		if (wire->port_input)
			direction |= FD_IN;
		if (wire->port_output)
			direction |= FD_OUT;
	}
	return direction;
}

string next_id()
{
	string new_id;

	while (1) {
		new_id = stringf("_%d", autoid_counter++);
		if (used_names.count(new_id) == 0) break;
	}

	used_names.insert(new_id);
	return new_id;
}

const char *make_id(IdString id)
{
	if (namecache.count(id) != 0)
		return namecache.at(id).c_str();

	string new_id = log_id(id);

	for (int i = 0; i < GetSize(new_id); i++)
	{
		char &ch = new_id[i];
		if ('a' <= ch && ch <= 'z') continue;
		if ('A' <= ch && ch <= 'Z') continue;
		if ('0' <= ch && ch <= '9' && i != 0) continue;
		if ('_' == ch) continue;
		ch = '_';
	}

	while (used_names.count(new_id) != 0)
		new_id += '_';

	namecache[id] = new_id;
	used_names.insert(new_id);
	return namecache.at(id).c_str();
}

struct FirrtlWorker
{
	Module *module;
	std::ostream &f;

	dict<SigBit, pair<string, int>> reverse_wire_map;
	string unconn_id;
	RTLIL::Design *design;
	std::string indent;

	// Define read/write ports and memories.
	// We'll collect their definitions and emit the corresponding FIRRTL definitions at the appropriate point in module construction.
	// For the moment, we don't handle $readmemh or $readmemb.
	// These will be part of a subsequent PR.
	struct read_port {
		string name;
		bool clk_enable;
		bool clk_parity;
		bool transparent;
		RTLIL::SigSpec clk;
		RTLIL::SigSpec ena;
		RTLIL::SigSpec addr;
		read_port(string name, bool clk_enable, bool clk_parity, bool transparent, RTLIL::SigSpec clk, RTLIL::SigSpec ena, RTLIL::SigSpec addr) : name(name), clk_enable(clk_enable), clk_parity(clk_parity), transparent(transparent), clk(clk), ena(ena), addr(addr) {
			// Current (3/13/2019) conventions:
			//  generate a constant 0 for clock and a constant 1 for enable if they are undefined.
			if (!clk.is_fully_def())
				this->clk = SigSpec(State::S0);
			if (!ena.is_fully_def())
				this->ena = SigSpec(State::S1);
		}
		string gen_read(const char * indent) {
			string addr_expr = make_expr(addr);
			string ena_expr = make_expr(ena);
			string clk_expr = make_expr(clk);
			string addr_str = stringf("%s%s.addr <= %s\n", indent, name.c_str(), addr_expr.c_str());
			string ena_str = stringf("%s%s.en <= %s\n", indent, name.c_str(), ena_expr.c_str());
			string clk_str = stringf("%s%s.clk <= asClock(%s)\n", indent, name.c_str(), clk_expr.c_str());
			return addr_str + ena_str + clk_str;
		}
	};
	struct write_port : read_port {
		RTLIL::SigSpec mask;
		write_port(string name, bool clk_enable, bool clk_parity, bool transparent, RTLIL::SigSpec clk, RTLIL::SigSpec ena, RTLIL::SigSpec addr, RTLIL::SigSpec mask) : read_port(name, clk_enable, clk_parity, transparent, clk, ena, addr), mask(mask) {
			if (!clk.is_fully_def())
				this->clk = SigSpec(RTLIL::Const(0));
			if (!ena.is_fully_def())
				this->ena = SigSpec(RTLIL::Const(0));
			if (!mask.is_fully_def())
				this->ena = SigSpec(RTLIL::Const(1));
		}
		string gen_read(const char * /* indent */) {
			log_error("gen_read called on write_port: %s\n", name.c_str());
			return stringf("gen_read called on write_port: %s\n", name.c_str());
		}
		string gen_write(const char * indent) {
			string addr_expr = make_expr(addr);
			string ena_expr = make_expr(ena);
			string clk_expr = make_expr(clk);
			string mask_expr = make_expr(mask);
			string mask_str = stringf("%s%s.mask <= %s\n", indent, name.c_str(), mask_expr.c_str());
			string addr_str = stringf("%s%s.addr <= %s\n", indent, name.c_str(), addr_expr.c_str());
			string ena_str = stringf("%s%s.en <= %s\n", indent, name.c_str(), ena_expr.c_str());
			string clk_str = stringf("%s%s.clk <= asClock(%s)\n", indent, name.c_str(), clk_expr.c_str());
			return addr_str + ena_str + clk_str + mask_str;
		}
	};
	/* Memories defined within this module. */
	struct memory {
		Cell *pCell;					// for error reporting
		string name;					// memory name
		int abits;						// number of address bits
		int size;						// size (in units) of the memory
		int width;						// size (in bits) of each element
		int read_latency;
		int write_latency;
		vector<read_port> read_ports;
		vector<write_port> write_ports;
		std::string init_file;
		std::string init_file_srcFileSpec;
		string srcLine;
		memory(Cell *pCell, string name, int abits, int size, int width) : pCell(pCell), name(name), abits(abits), size(size), width(width), read_latency(0), write_latency(1), init_file(""), init_file_srcFileSpec("") {
			// Provide defaults for abits or size if one (but not the other) is specified.
			if (this->abits == 0 && this->size != 0) {
				this->abits = ceil_log2(this->size);
			} else if (this->abits != 0 && this->size == 0) {
				this->size = 1 << this->abits;
			}
			// Sanity-check this construction.
			if (this->name == "") {
				log_error("Nameless memory%s\n", this->atLine());
			}
			if (this->abits == 0 && this->size == 0) {
				log_error("Memory %s has zero address bits and size%s\n", this->name.c_str(), this->atLine());
			}
			if (this->width == 0) {
				log_error("Memory %s has zero width%s\n", this->name.c_str(), this->atLine());
			}
		 }
		// We need a default constructor for the dict insert.
	   memory() : pCell(0), read_latency(0), write_latency(1), init_file(""), init_file_srcFileSpec(""){}

		const char *atLine() {
			if (srcLine == "") {
				if (pCell) {
					auto p = pCell->attributes.find("\\src");
					srcLine = " at " + p->second.decode_string();
				}
			}
			return srcLine.c_str();
		}
		void add_memory_read_port(read_port &rp) {
			read_ports.push_back(rp);
		}
		void add_memory_write_port(write_port &wp) {
			write_ports.push_back(wp);
		}
		void add_memory_file(std::string init_file, std::string init_file_srcFileSpec) {
			this->init_file = init_file;
			this->init_file_srcFileSpec = init_file_srcFileSpec;
		}

	};
	dict<string, memory> memories;

	void register_memory(memory &m)
	{
		memories[m.name] = m;
	}

	void register_reverse_wire_map(string id, SigSpec sig)
	{
		for (int i = 0; i < GetSize(sig); i++)
			reverse_wire_map[sig[i]] = make_pair(id, i);
	}

	FirrtlWorker(Module *module, std::ostream &f, RTLIL::Design *theDesign) : module(module), f(f), design(theDesign), indent("    ")
	{
	}

	static string make_expr(const SigSpec &sig)
	{
		string expr;

		for (auto chunk : sig.chunks())
		{
			string new_expr;

			if (chunk.wire == nullptr)
			{
				std::vector<RTLIL::State> bits = chunk.data;
				new_expr = stringf("UInt<%d>(\"h", GetSize(bits));

				while (GetSize(bits) % 4 != 0)
					bits.push_back(State::S0);

				for (int i = GetSize(bits)-4; i >= 0; i -= 4)
				{
					int val = 0;
					if (bits[i+0] == State::S1) val += 1;
					if (bits[i+1] == State::S1) val += 2;
					if (bits[i+2] == State::S1) val += 4;
					if (bits[i+3] == State::S1) val += 8;
					new_expr.push_back(val < 10 ? '0' + val : 'a' + val - 10);
				}

				new_expr += "\")";
			}
			else if (chunk.offset == 0 && chunk.width == chunk.wire->width)
			{
				new_expr = make_id(chunk.wire->name);
			}
			else
			{
				string wire_id = make_id(chunk.wire->name);
				new_expr = stringf("bits(%s, %d, %d)", wire_id.c_str(), chunk.offset + chunk.width - 1, chunk.offset);
			}

			if (expr.empty())
				expr = new_expr;
			else
				expr = "cat(" + new_expr + ", " + expr + ")";
		}

		return expr;
	}

	std::string fid(RTLIL::IdString internal_id)
	{
		return make_id(internal_id);
	}

	std::string cellname(RTLIL::Cell *cell)
	{
		return fid(cell->name).c_str();
	}

	void process_instance(RTLIL::Cell *cell, vector<string> &wire_exprs)
	{
		std::string cell_type = fid(cell->type);
		std::string instanceOf;
		// If this is a parameterized module, its parent module is encoded in the cell type
		if (cell->type.begins_with("$paramod"))
		{
			std::string::iterator it;
			for (it = cell_type.begin(); it < cell_type.end(); it++)
			{
				switch (*it) {
					case '\\': /* FALL_THROUGH */
					case '=': /* FALL_THROUGH */
					case '\'': /* FALL_THROUGH */
					case '$': instanceOf.append("_"); break;
					default: instanceOf.append(1, *it); break;
				}
			}
		}
		else
		{
			instanceOf = cell_type;
		}

		std::string cell_name = cellname(cell);
		std::string cell_name_comment;
		if (cell_name != fid(cell->name))
			cell_name_comment = " /* " + fid(cell->name) + " */ ";
		else
			cell_name_comment = "";
		// Find the module corresponding to this instance.
		auto instModule = design->module(cell->type);
		// If there is no instance for this, just return.
		if (instModule == NULL)
		{
			log_warning("No instance for %s.%s\n", cell_type.c_str(), cell_name.c_str());
			return;
		}
		wire_exprs.push_back(stringf("%s" "inst %s%s of %s", indent.c_str(), cell_name.c_str(), cell_name_comment.c_str(), instanceOf.c_str()));

		for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
			if (it->second.size() > 0) {
				const SigSpec &secondSig = it->second;
				const std::string firstName = cell_name + "." + make_id(it->first);
				const std::string secondExpr = make_expr(secondSig);
				// Find the direction for this port.
				FDirection dir = getPortFDirection(it->first, instModule);
				std::string sourceExpr, sinkExpr;
				const SigSpec *sinkSig = nullptr;
				switch (dir) {
					case FD_INOUT:
						log_warning("Instance port connection %s.%s is INOUT; treating as OUT\n", cell_type.c_str(), log_signal(it->second));
						/* FALLTHRU */
					case FD_OUT:
						sourceExpr = firstName;
						sinkExpr = secondExpr;
						sinkSig = &secondSig;
						break;
					case FD_NODIRECTION:
						log_warning("Instance port connection %s.%s is NODIRECTION; treating as IN\n", cell_type.c_str(), log_signal(it->second));
						/* FALLTHRU */
					case FD_IN:
						sourceExpr = secondExpr;
						sinkExpr = firstName;
						break;
					default:
						log_error("Instance port %s.%s unrecognized connection direction 0x%x !\n", cell_type.c_str(), log_signal(it->second), dir);
						break;
				}
				// Check for subfield assignment.
				std::string bitsString = "bits(";
				if (sinkExpr.compare(0, bitsString.length(), bitsString) == 0) {
					if (sinkSig == nullptr)
						log_error("Unknown subfield %s.%s\n", cell_type.c_str(), sinkExpr.c_str());
					// Don't generate the assignment here.
					// Add the source and sink to the "reverse_wire_map" and we'll output the assignment
					//  as part of the coalesced subfield assignments for this wire.
					register_reverse_wire_map(sourceExpr, *sinkSig);
				} else {
					wire_exprs.push_back(stringf("\n%s%s <= %s", indent.c_str(), sinkExpr.c_str(), sourceExpr.c_str()));
				}
			}
		}
		wire_exprs.push_back(stringf("\n"));

	}

	// Given an expression for a shift amount, and a maximum width,
	//  generate the FIRRTL expression for equivalent dynamic shift taking into account FIRRTL shift semantics.
	std::string gen_dshl(const string b_expr, const int b_width)
	{
		string result = b_expr;
		if (b_width >= FIRRTL_MAX_DSH_WIDTH_ERROR) {
			int max_shift_width_bits = FIRRTL_MAX_DSH_WIDTH_ERROR - 1;
			string max_shift_string = stringf("UInt<%d>(%d)", max_shift_width_bits, (1<<max_shift_width_bits) - 1);
			// Deal with the difference in semantics between FIRRTL and verilog
			result = stringf("mux(gt(%s, %s), %s, bits(%s, %d, 0))", b_expr.c_str(), max_shift_string.c_str(), max_shift_string.c_str(), b_expr.c_str(), max_shift_width_bits - 1);
		}
		return result;
	}

	void run()
	{
		f << stringf("  module %s:\n", make_id(module->name));
		vector<string> port_decls, wire_decls, cell_exprs, wire_exprs;

		for (auto wire : module->wires())
		{
			const auto wireName = make_id(wire->name);
			// If a wire has initial data, issue a warning since FIRRTL doesn't currently support it.
			if (wire->attributes.count("\\init")) {
				log_warning("Initial value (%s) for (%s.%s) not supported\n",
							wire->attributes.at("\\init").as_string().c_str(),
							log_id(module), log_id(wire));
			}
			if (wire->port_id)
			{
				if (wire->port_input && wire->port_output)
					log_error("Module port %s.%s is inout!\n", log_id(module), log_id(wire));
				port_decls.push_back(stringf("    %s %s: UInt<%d>\n", wire->port_input ? "input" : "output",
						wireName, wire->width));
			}
			else
			{
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", wireName, wire->width));
			}
		}

		for (auto cell : module->cells())
		{
			static Const ndef(0, 0);

		    // Is this cell is a module instance?
			if (cell->type[0] != '$')
			{
				process_instance(cell, wire_exprs);
				continue;
			}
			// Not a module instance. Set up cell properties
			bool extract_y_bits = false;		// Assume no extraction of final bits will be required.
			int a_width = cell->parameters.at("\\A_WIDTH", ndef).as_int();	// The width of "A"
			int b_width = cell->parameters.at("\\B_WIDTH", ndef).as_int();	// The width of "A"
			const int y_width = cell->parameters.at("\\Y_WIDTH", ndef).as_int();	// The width of the result
			const bool a_signed = cell->parameters.at("\\A_SIGNED", ndef).as_bool();
			const bool b_signed = cell->parameters.at("\\B_SIGNED", ndef).as_bool();
			bool firrtl_is_signed = a_signed;	// The result is signed (subsequent code may change this).
			int firrtl_width = 0;
			string primop;
			bool always_uint = false;
			string y_id = make_id(cell->name);

			if (cell->type.in("$not", "$logic_not", "$neg", "$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_bool", "$reduce_xnor"))
			{
				string a_expr = make_expr(cell->getPort("\\A"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (a_signed) {
					a_expr = "asSInt(" + a_expr + ")";
				}

				// Don't use the results of logical operations (a single bit) to control padding
				if (!(cell->type.in("$eq", "$eqx", "$gt", "$ge", "$lt", "$le", "$ne", "$nex", "$reduce_bool", "$logic_not") && y_width == 1) ) {
					a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
				}

				// Assume the FIRRTL width is a single bit.
				firrtl_width = 1;
				if (cell->type == "$not") primop = "not";
				else if (cell->type == "$neg") {
					primop = "neg";
					firrtl_is_signed = true;	// Result of "neg" is signed (an SInt).
					firrtl_width = a_width;
				} else if (cell->type == "$logic_not") {
                                        primop = "eq";
                                        a_expr = stringf("%s, UInt(0)", a_expr.c_str());
                                }
				else if (cell->type == "$reduce_and") primop = "andr";
				else if (cell->type == "$reduce_or") primop = "orr";
				else if (cell->type == "$reduce_xor") primop = "xorr";
				else if (cell->type == "$reduce_xnor") {
                                        primop = "not";
                                        a_expr = stringf("xorr(%s)", a_expr.c_str());
                                }
				else if (cell->type == "$reduce_bool") {
					primop = "neq";
					// Use the sign of the a_expr and its width as the type (UInt/SInt) and width of the comparand.
					a_expr = stringf("%s, %cInt<%d>(0)", a_expr.c_str(), a_signed ? 'S' : 'U', a_width);
				}

				string expr = stringf("%s(%s)", primop.c_str(), a_expr.c_str());

				if ((firrtl_is_signed && !always_uint))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}
			if (cell->type.in("$add", "$sub", "$mul", "$div", "$mod", "$xor", "$xnor", "$and", "$or", "$eq", "$eqx",
							  "$gt", "$ge", "$lt", "$le", "$ne", "$nex", "$shr", "$sshr", "$sshl", "$shl",
							  "$logic_and", "$logic_or", "$pow"))
			{
				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (a_signed) {
					a_expr = "asSInt(" + a_expr + ")";
					// Expand the "A" operand to the result width
					if (a_width < y_width) {
						a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
						a_width = y_width;
					}
				}
				// Shift amount is always unsigned, and needn't be padded to result width,
				//  otherwise, we need to cast the b_expr appropriately
				if (b_signed && !cell->type.in("$shr", "$sshr", "$shl", "$sshl", "$pow")) {
					b_expr = "asSInt(" + b_expr + ")";
					// Expand the "B" operand to the result width
					if (b_width < y_width) {
						b_expr = stringf("pad(%s, %d)", b_expr.c_str(), y_width);
						b_width = y_width;
					}
				}

				// For the arithmetic ops, expand operand widths to result widths befor performing the operation.
				// This corresponds (according to iverilog) to what verilog compilers implement.
				if (cell->type.in("$add", "$sub", "$mul", "$div", "$mod", "$xor", "$xnor", "$and", "$or"))
				{
					if (a_width < y_width) {
						a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
						a_width = y_width;
					}
					if (b_width < y_width) {
						b_expr = stringf("pad(%s, %d)", b_expr.c_str(), y_width);
						b_width = y_width;
					}
				}
				// Assume the FIRRTL width is the width of "A"
				firrtl_width = a_width;
				auto a_sig = cell->getPort("\\A");

				if (cell->type == "$add") {
					primop = "add";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = max(a_width, b_width);
				} else if (cell->type == "$sub") {
					primop = "sub";
					firrtl_is_signed = true;
					int a_widthInc = (!a_signed && b_signed) ? 2 : (a_signed && !b_signed) ? 1 : 0;
					int b_widthInc = (a_signed && !b_signed) ? 2 : (!a_signed && b_signed) ? 1 : 0;
					firrtl_width = max(a_width + a_widthInc, b_width + b_widthInc);
				} else if (cell->type == "$mul") {
					primop = "mul";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = a_width + b_width;
				} else if (cell->type == "$div") {
					primop = "div";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = a_width;
				} else if (cell->type == "$mod") {
					primop = "rem";
					firrtl_width = min(a_width, b_width);
				} else if (cell->type == "$and") {
					primop = "and";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type == "$or" ) {
					primop =  "or";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type == "$xor") {
					primop = "xor";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type == "$xnor") {
					primop = "xnor";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if ((cell->type == "$eq") | (cell->type == "$eqx")) {
					primop = "eq";
					always_uint = true;
					firrtl_width = 1;
			    }
				else if ((cell->type == "$ne") | (cell->type == "$nex")) {
					primop = "neq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == "$gt") {
					primop = "gt";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == "$ge") {
					primop = "geq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == "$lt") {
					primop = "lt";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == "$le") {
					primop = "leq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == "$shl") | (cell->type == "$sshl")) {
					// FIRRTL will widen the result (y) by the amount of the shift.
					// We'll need to offset this by extracting the un-widened portion as Verilog would do.
					extract_y_bits = true;
					// Is the shift amount constant?
					auto b_sig = cell->getPort("\\B");
					if (b_sig.is_fully_const()) {
						primop = "shl";
						int shift_amount = b_sig.as_int();
						b_expr = std::to_string(shift_amount);
						firrtl_width = a_width + shift_amount;
					} else {
						primop = "dshl";
						// Convert from FIRRTL left shift semantics.
						b_expr = gen_dshl(b_expr, b_width);
						firrtl_width = a_width + (1 << b_width) - 1;
					}
				}
				else if ((cell->type == "$shr") | (cell->type == "$sshr")) {
					// We don't need to extract a specific range of bits.
					extract_y_bits = false;
					// Is the shift amount constant?
					auto b_sig = cell->getPort("\\B");
					if (b_sig.is_fully_const()) {
						primop = "shr";
						int shift_amount = b_sig.as_int();
						b_expr = std::to_string(shift_amount);
						firrtl_width = max(1, a_width - shift_amount);
					} else {
						primop = "dshr";
						firrtl_width = a_width;
					}
					// We'll need to do some special fixups if the source (and thus result) is signed.
					if (firrtl_is_signed) {
						// If this is a "logical" shift right, pretend the source is unsigned.
						if (cell->type == "$shr") {
							a_expr = "asUInt(" + a_expr + ")";
						}
					}
				}
				else if ((cell->type == "$logic_and")) {
					primop = "and";
					a_expr = "neq(" + a_expr + ", UInt(0))";
					b_expr = "neq(" + b_expr + ", UInt(0))";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == "$logic_or")) {
					primop = "or";
					a_expr = "neq(" + a_expr + ", UInt(0))";
					b_expr = "neq(" + b_expr + ", UInt(0))";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == "$pow")) {
					if (a_sig.is_fully_const() && a_sig.as_int() == 2) {
						// We'll convert this to a shift. To simplify things, change the a_expr to "1"
						//	so we can use b_expr directly as a shift amount.
						// Only support 2 ** N (i.e., shift left)
						// FIRRTL will widen the result (y) by the amount of the shift.
						// We'll need to offset this by extracting the un-widened portion as Verilog would do.
						a_expr = firrtl_is_signed ? "SInt(1)" : "UInt(1)";
						extract_y_bits = true;
						// Is the shift amount constant?
						auto b_sig = cell->getPort("\\B");
						if (b_sig.is_fully_const()) {
							primop = "shl";
							int shiftAmount = b_sig.as_int();
							if (shiftAmount < 0) {
								log_error("Negative power exponent - %d: %s.%s\n", shiftAmount, log_id(module), log_id(cell));
							}
							b_expr = std::to_string(shiftAmount);
							firrtl_width = a_width + shiftAmount;
						} else {
							primop = "dshl";
							// Convert from FIRRTL left shift semantics.
							b_expr = gen_dshl(b_expr, b_width);
							firrtl_width = a_width + (1 << b_width) - 1;
						}
					} else {
						log_error("Non power 2: %s.%s\n", log_id(module), log_id(cell));
					}
				}

				if (!cell->parameters.at("\\B_SIGNED").as_bool()) {
					b_expr = "asUInt(" + b_expr + ")";
				}

				string expr;
				// Deal with $xnor == ~^ (not xor)
				if (primop == "xnor") {
					expr = stringf("not(xor(%s, %s))", a_expr.c_str(), b_expr.c_str());
				} else {
					expr = stringf("%s(%s, %s)", primop.c_str(), a_expr.c_str(), b_expr.c_str());
				}

				// Deal with FIRRTL's "shift widens" semantics, or the need to widen the FIRRTL result.
				// If the operation is signed, the FIRRTL width will be 1 one bit larger.
				if (extract_y_bits) {
					expr = stringf("bits(%s, %d, 0)", expr.c_str(), y_width - 1);
				} else if (firrtl_is_signed && (firrtl_width + 1) < y_width) {
					expr = stringf("pad(%s, %d)", expr.c_str(), y_width);
				}

				if ((firrtl_is_signed && !always_uint))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}

			if (cell->type.in("$mux"))
			{
				int width = cell->parameters.at("\\WIDTH").as_int();
				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				string s_expr = make_expr(cell->getPort("\\S"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), width));

				string expr = stringf("mux(%s, %s, %s)", s_expr.c_str(), b_expr.c_str(), a_expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}

			if (cell->type.in("$mem"))
			{
				string mem_id = make_id(cell->name);
				int abits = cell->parameters.at("\\ABITS").as_int();
				int width = cell->parameters.at("\\WIDTH").as_int();
				int size = cell->parameters.at("\\SIZE").as_int();
				memory m(cell, mem_id, abits, size, width);
				int rd_ports = cell->parameters.at("\\RD_PORTS").as_int();
				int wr_ports = cell->parameters.at("\\WR_PORTS").as_int();

				Const initdata = cell->parameters.at("\\INIT");
				for (State bit : initdata.bits)
					if (bit != State::Sx)
						log_error("Memory with initialization data: %s.%s\n", log_id(module), log_id(cell));

				Const rd_clk_enable = cell->parameters.at("\\RD_CLK_ENABLE");
				Const wr_clk_enable = cell->parameters.at("\\WR_CLK_ENABLE");
				Const wr_clk_polarity = cell->parameters.at("\\WR_CLK_POLARITY");

				int offset = cell->parameters.at("\\OFFSET").as_int();
				if (offset != 0)
					log_error("Memory with nonzero offset: %s.%s\n", log_id(module), log_id(cell));

				for (int i = 0; i < rd_ports; i++)
				{
					if (rd_clk_enable[i] != State::S0)
						log_error("Clocked read port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					SigSpec addr_sig = cell->getPort("\\RD_ADDR").extract(i*abits, abits);
					SigSpec data_sig = cell->getPort("\\RD_DATA").extract(i*width, width);
					string addr_expr = make_expr(addr_sig);
					string name(stringf("%s.r%d", m.name.c_str(), i));
					bool clk_enable = false;
					bool clk_parity = true;
					bool transparency = false;
					SigSpec ena_sig = RTLIL::SigSpec(RTLIL::State::S1, 1);
					SigSpec clk_sig = RTLIL::SigSpec(RTLIL::State::S0, 1);
					read_port rp(name, clk_enable, clk_parity, transparency, clk_sig, ena_sig, addr_sig);
					m.add_memory_read_port(rp);
					cell_exprs.push_back(rp.gen_read(indent.c_str()));
					register_reverse_wire_map(stringf("%s.data", name.c_str()), data_sig);
				}

				for (int i = 0; i < wr_ports; i++)
				{
					if (wr_clk_enable[i] != State::S1)
						log_error("Unclocked write port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					if (wr_clk_polarity[i] != State::S1)
						log_error("Negedge write port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					string name(stringf("%s.w%d", m.name.c_str(), i));
					bool clk_enable = true;
					bool clk_parity = true;
					bool transparency = false;
					SigSpec addr_sig =cell->getPort("\\WR_ADDR").extract(i*abits, abits);
					string addr_expr = make_expr(addr_sig);
					SigSpec data_sig =cell->getPort("\\WR_DATA").extract(i*width, width);
					string data_expr = make_expr(data_sig);
					SigSpec clk_sig = cell->getPort("\\WR_CLK").extract(i);
					string clk_expr = make_expr(clk_sig);

					SigSpec wen_sig = cell->getPort("\\WR_EN").extract(i*width, width);
					string wen_expr = make_expr(wen_sig[0]);

					for (int i = 1; i < GetSize(wen_sig); i++)
						if (wen_sig[0] != wen_sig[i])
							log_error("Complex write enable on port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					SigSpec mask_sig = RTLIL::SigSpec(RTLIL::State::S1, 1);
					write_port wp(name, clk_enable, clk_parity, transparency, clk_sig, wen_sig[0], addr_sig, mask_sig);
					m.add_memory_write_port(wp);
					cell_exprs.push_back(stringf("%s%s.data <= %s\n", indent.c_str(), name.c_str(), data_expr.c_str()));
					cell_exprs.push_back(wp.gen_write(indent.c_str()));
				}
				register_memory(m);
				continue;
			}

			if (cell->type.in("$memwr", "$memrd", "$meminit"))
			{
				std::string cell_type = fid(cell->type);
				std::string mem_id = make_id(cell->parameters["\\MEMID"].decode_string());
				int abits = cell->parameters.at("\\ABITS").as_int();
				int width = cell->parameters.at("\\WIDTH").as_int();
				memory *mp = nullptr;
				if (cell->type == "$meminit" ) {
					log_error("$meminit (%s.%s.%s) currently unsupported\n", log_id(module), log_id(cell), mem_id.c_str());
				} else {
					// It's a $memwr or $memrd. Remember the read/write port parameters for the eventual FIRRTL memory definition.
					auto addrSig = cell->getPort("\\ADDR");
					auto dataSig = cell->getPort("\\DATA");
					auto enableSig = cell->getPort("\\EN");
					auto clockSig = cell->getPort("\\CLK");
					Const clk_enable = cell->parameters.at("\\CLK_ENABLE");
					Const clk_polarity = cell->parameters.at("\\CLK_POLARITY");

					// Do we already have an entry for this memory?
					if (memories.count(mem_id) == 0) {
						memory m(cell, mem_id, abits, 0, width);
						register_memory(m);
					}
					mp = &memories.at(mem_id);
					int portNum = 0;
					bool transparency = false;
					string data_expr = make_expr(dataSig);
					if (cell->type.in("$memwr")) {
						portNum = (int) mp->write_ports.size();
						write_port wp(stringf("%s.w%d", mem_id.c_str(), portNum), clk_enable.as_bool(), clk_polarity.as_bool(),  transparency, clockSig, enableSig, addrSig, dataSig);
						mp->add_memory_write_port(wp);
						cell_exprs.push_back(stringf("%s%s.data <= %s\n", indent.c_str(), wp.name.c_str(), data_expr.c_str()));
						cell_exprs.push_back(wp.gen_write(indent.c_str()));
					} else if (cell->type.in("$memrd")) {
						portNum = (int) mp->read_ports.size();
						read_port rp(stringf("%s.r%d", mem_id.c_str(), portNum), clk_enable.as_bool(), clk_polarity.as_bool(),  transparency, clockSig, enableSig, addrSig);
						mp->add_memory_read_port(rp);
						cell_exprs.push_back(rp.gen_read(indent.c_str()));
						register_reverse_wire_map(stringf("%s.data", rp.name.c_str()), dataSig);
					}
				}
				continue;
			}

			if (cell->type.in("$dff"))
			{
				bool clkpol = cell->parameters.at("\\CLK_POLARITY").as_bool();
				if (clkpol == false)
					log_error("Negative edge clock on FF %s.%s.\n", log_id(module), log_id(cell));

				int width = cell->parameters.at("\\WIDTH").as_int();
				string expr = make_expr(cell->getPort("\\D"));
				string clk_expr = "asClock(" + make_expr(cell->getPort("\\CLK")) + ")";

				wire_decls.push_back(stringf("    reg %s: UInt<%d>, %s\n", y_id.c_str(), width, clk_expr.c_str()));

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Q"));

				continue;
			}

			// This may be a parameterized module - paramod.
			if (cell->type.begins_with("$paramod"))
			{
				process_instance(cell, wire_exprs);
				continue;
			}
			if (cell->type == "$shiftx") {
				// assign y = a[b +: y_width];
				// We'll extract the correct bits as part of the primop.

				string a_expr = make_expr(cell->getPort("\\A"));
				// Get the initial bit selector
				string b_expr = make_expr(cell->getPort("\\B"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (cell->getParam("\\B_SIGNED").as_bool()) {
					// Use validif to constrain the selection (test the sign bit)
					auto b_string = b_expr.c_str();
					int b_sign = cell->parameters.at("\\B_WIDTH").as_int() - 1;
					b_expr = stringf("validif(not(bits(%s, %d, %d)), %s)", b_string, b_sign, b_sign, b_string);
				}
				string expr = stringf("dshr(%s, %s)", a_expr.c_str(), b_expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));
				continue;
			}
			if (cell->type == "$shift") {
				// assign y = a >> b;
				//  where b may be negative

				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				auto b_string = b_expr.c_str();
				string expr;
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (cell->getParam("\\B_SIGNED").as_bool()) {
					// We generate a left or right shift based on the sign of b.
					std::string dshl = stringf("bits(dshl(%s, %s), 0, %d)", a_expr.c_str(), gen_dshl(b_expr, b_width).c_str(), y_width);
					std::string dshr = stringf("dshr(%s, %s)", a_expr.c_str(), b_string);
					expr = stringf("mux(%s < 0, %s, %s)",
									 b_string,
									 dshl.c_str(),
									 dshr.c_str()
									 );
				} else {
					expr = stringf("dshr(%s, %s)", a_expr.c_str(), b_string);
				}
				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));
				continue;
			}
			if (cell->type == "$pos") {
				// assign y = a;
//				printCell(cell);
				string a_expr = make_expr(cell->getPort("\\A"));
				// Verilog appears to treat the result as signed, so if the result is wider than "A",
				//  we need to pad.
				if (a_width < y_width) {
					a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
				}
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));
				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), a_expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));
				continue;
			}
			log_error("Cell type not supported: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
		}

		for (auto conn : module->connections())
		{
			string y_id = next_id();
			int y_width =  GetSize(conn.first);
			string expr = make_expr(conn.second);

			wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));
			cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
			register_reverse_wire_map(y_id, conn.first);
		}

		for (auto wire : module->wires())
		{
			string expr;

			if (wire->port_input)
				continue;

			int cursor = 0;
			bool is_valid = false;
			bool make_unconn_id = false;

			while (cursor < wire->width)
			{
				int chunk_width = 1;
				string new_expr;

				SigBit start_bit(wire, cursor);

				if (reverse_wire_map.count(start_bit))
				{
					pair<string, int> start_map = reverse_wire_map.at(start_bit);

					while (cursor+chunk_width < wire->width)
					{
						SigBit stop_bit(wire, cursor+chunk_width);

						if (reverse_wire_map.count(stop_bit) == 0)
							break;

						pair<string, int> stop_map = reverse_wire_map.at(stop_bit);
						stop_map.second -= chunk_width;

						if (start_map != stop_map)
							break;

						chunk_width++;
					}

					new_expr = stringf("bits(%s, %d, %d)", start_map.first.c_str(),
							start_map.second + chunk_width - 1, start_map.second);
					is_valid = true;
				}
				else
				{
					if (unconn_id.empty()) {
						unconn_id = next_id();
						make_unconn_id = true;
					}
					new_expr = unconn_id;
				}

				if (expr.empty())
					expr = new_expr;
				else
					expr = "cat(" + new_expr + ", " + expr + ")";

				cursor += chunk_width;
			}

			if (is_valid) {
				if (make_unconn_id) {
					wire_decls.push_back(stringf("    wire %s: UInt<1>\n", unconn_id.c_str()));
					wire_decls.push_back(stringf("    %s is invalid\n", unconn_id.c_str()));
				}
				wire_exprs.push_back(stringf("    %s <= %s\n", make_id(wire->name), expr.c_str()));
			} else {
				if (make_unconn_id) {
					unconn_id.clear();
				}
				wire_decls.push_back(stringf("    %s is invalid\n", make_id(wire->name)));
			}
		}

		for (auto str : port_decls)
			f << str;

		f << stringf("\n");

		for (auto str : wire_decls)
			f << str;

		f << stringf("\n");

		// If we have any memory definitions, output them.
		for (auto kv : memories) {
			memory &m = kv.second;
			f << stringf("    mem %s:\n", m.name.c_str());
			f << stringf("      data-type => UInt<%d>\n", m.width);
			f << stringf("      depth => %d\n", m.size);
			for (int i = 0; i < (int) m.read_ports.size(); i += 1) {
				f << stringf("      reader => r%d\n", i);
			}
			for (int i = 0; i < (int) m.write_ports.size(); i += 1) {
				f << stringf("      writer => w%d\n", i);
			}
			f << stringf("      read-latency => %d\n", m.read_latency);
			f << stringf("      write-latency => %d\n", m.write_latency);
			f << stringf("      read-under-write => undefined\n");
		}
		f << stringf("\n");

		for (auto str : cell_exprs)
			f << str;

		f << stringf("\n");

		for (auto str : wire_exprs)
			f << str;
	}
};

struct FirrtlBackend : public Backend {
	FirrtlBackend() : Backend("firrtl", "write design to a FIRRTL file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_firrtl [options] [filename]\n");
		log("\n");
		log("Write a FIRRTL netlist of the current design.\n");
		log("The following commands are executed by this command:\n");
		log("        pmuxtree\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx = args.size();	// We aren't expecting any arguments.

		// If we weren't explicitly passed a filename, use the last argument (if it isn't a flag).
		if (filename == "") {
			if (argidx > 0 && args[argidx - 1][0] != '-') {
				// extra_args and friends need to see this argument.
				argidx -= 1;
				filename = args[argidx];
			}
		}
		extra_args(f, filename, args, argidx);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing FIRRTL backend.\n");
		log_push();

		Pass::call(design, stringf("pmuxtree"));

		namecache.clear();
		autoid_counter = 0;

		// Get the top module, or a reasonable facsimile - we need something for the circuit name.
		Module *top = design->top_module();
		Module *last = nullptr;
		// Generate module and wire names.
		for (auto module : design->modules()) {
			make_id(module->name);
			last = module;
			if (top == nullptr && module->get_bool_attribute("\\top")) {
				top = module;
			}
			for (auto wire : module->wires())
				if (wire->port_id)
					make_id(wire->name);
		}

		if (top == nullptr)
			top = last;

		*f << stringf("circuit %s:\n", make_id(top->name));

		for (auto module : design->modules())
		{
			FirrtlWorker worker(module, *f, design);
			worker.run();
		}

		namecache.clear();
		autoid_counter = 0;
	}
} FirrtlBackend;

PRIVATE_NAMESPACE_END
