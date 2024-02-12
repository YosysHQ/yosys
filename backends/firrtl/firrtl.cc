/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/log.h"
#include "kernel/mem.h"
#include <algorithm>
#include <string>
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

std::string getFileinfo(const RTLIL::AttrObject *design_entity)
{
	std::string src(design_entity->get_src_attribute());
	std::string fileinfo_str = src.empty() ? "" : "@[" + src + "]";
	return fileinfo_str;
}

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

std::string dump_const_string(const RTLIL::Const &data)
{
	std::string res_str;

	std::string str = data.decode_string();
	for (size_t i = 0; i < str.size(); i++)
	{
		if (str[i] == '\n')
			res_str += "\\n";
		else if (str[i] == '\t')
			res_str += "\\t";
		else if (str[i] < 32)
			res_str += stringf("\\%03o", str[i]);
		else if (str[i] == '"')
			res_str += "\\\"";
		else if (str[i] == '\\')
			res_str += "\\\\";
		else
			res_str += str[i];
	}

	return res_str;
}

std::string dump_const(const RTLIL::Const &data)
{
	std::string res_str;

	// // For debugging purposes to find out how Yosys encodes flags.
	// res_str += stringf("flags_%x --> ", data.flags);

	// Real-valued parameter.
	if (data.flags & RTLIL::CONST_FLAG_REAL)
	{
		// Yosys stores real values as strings, so we call the string dumping code.
		res_str += dump_const_string(data);
	}
	// String parameter.
	else if (data.flags & RTLIL::CONST_FLAG_STRING)
	{
		res_str += "\"";
		res_str += dump_const_string(data);
		res_str += "\"";
	}
	// Numeric (non-real) parameter.
	else
	{
		int width = data.bits.size();

		// If a standard 32-bit int, then emit standard int value like "56" or
		// "-56". Firrtl supports negative-valued int literals.
		//
		//    SignedInt
		//      : ( '+' | '-' ) PosInt
		//      ;
		if (width <= 32)
		{
			int32_t int_val = 0;

			for (int i = 0; i < width; i++)
			{
				switch (data.bits[i])
				{
					case State::S0:                      break;
					case State::S1: int_val |= (1 << i); break;
					default:
						log_error("Unexpected int value\n");
						break;
				}
			}

			res_str += stringf("%d", int_val);
		}
		else
		{
			// If value is larger than 32 bits, then emit a binary representation of
			// the number as integers are not large enough to contain the result.
			// There is a caveat to this approach though:
			//
			// Note that parameter may be defined as having a fixed width as follows:
			//
			//     parameter signed [26:0] test_signed;
			//     parameter        [26:0] test_unsigned;
			//     parameter signed [40:0] test_signed_large;
			//
			// However, if you assign a value on the RHS without specifying the
			// precision, then yosys considers the value you used as an int and
			// assigns it a width of 32 bits regardless of the type of the parameter.
			//
			//     defparam <inst_name> .test_signed = 49;           (width = 32, though should be 27 based on definition)
			//     defparam <inst_name> .test_unsigned = 40'd35;     (width = 40, though should be 27 based on definition)
			//     defparam <inst_name> .test_signed_large = 40'd12; (width = 40)
			//
			// We therefore may lose the precision of the original verilog literal if
			// it was written without its bitwidth specifier.

			// Emit binary prefix for string.
			res_str += "\"b";

			// Emit bits.
			for (int i = width - 1; i >= 0; i--)
			{
				log_assert(i < width);
				switch (data.bits[i])
				{
					case State::S0: res_str += "0"; break;
					case State::S1: res_str += "1"; break;
					case State::Sx: res_str += "x"; break;
					case State::Sz: res_str += "z"; break;
					case State::Sa: res_str += "-"; break;
					case State::Sm: res_str += "m"; break;
				}
			}

			res_str += "\"";
		}
	}

	return res_str;
}

std::string extmodule_name(RTLIL::Cell *cell, RTLIL::Module *mod_instance)
{
	// Since we are creating a custom extmodule for every cell that instantiates
	// this blackbox, we need to create a custom name for it. We just use the
	// name of the blackbox itself followed by the name of the cell.
	const std::string cell_name = std::string(make_id(cell->name));
	const std::string blackbox_name = std::string(make_id(mod_instance->name));
	const std::string extmodule_name = blackbox_name + "_" + cell_name;
	return extmodule_name;
}

/**
 * Emits a parameterized extmodule. Instance parameters are obtained from
 * ''cell'' as it represents the instantiation of the blackbox defined by
 * ''mod_instance'' and therefore contains all its instance parameters.
 */
void emit_extmodule(RTLIL::Cell *cell, RTLIL::Module *mod_instance, std::ostream &f)
{
	const std::string indent = "    ";

	const std::string blackbox_name = std::string(make_id(mod_instance->name));
	const std::string exported_name = extmodule_name(cell, mod_instance);

	// We use the cell's fileinfo for this extmodule as its parameters come from
	// the cell and not from the module itself (the module contains default
	// parameters, not the instance-specific ones we're using to emit the
	// extmodule).
	const std::string extmoduleFileinfo = getFileinfo(cell);

	// Emit extmodule header.
	f << stringf("  extmodule %s: %s\n", exported_name.c_str(), extmoduleFileinfo.c_str());

	// Emit extmodule ports.
	for (auto wire : mod_instance->wires())
	{
		const auto wireName = make_id(wire->name);
		const std::string wireFileinfo = getFileinfo(wire);

		if (wire->port_input && wire->port_output)
		{
			log_error("Module port %s.%s is inout!\n", log_id(mod_instance), log_id(wire));
		}

		const std::string portDecl = stringf("%s%s %s: UInt<%d> %s\n",
			indent.c_str(),
			wire->port_input ? "input" : "output",
			wireName,
			wire->width,
			wireFileinfo.c_str()
		);

		f << portDecl;
	}

	// Emit extmodule "defname" field. This is the name of the verilog blackbox
	// that is used when verilog is emitted, so we use the name of mod_instance
	// here.
	f << stringf("%sdefname = %s\n", indent.c_str(), blackbox_name.c_str());

	// Emit extmodule generic parameters.
	for (const auto &p : cell->parameters)
	{
		const RTLIL::IdString p_id = p.first;
		const RTLIL::Const p_value = p.second;

		std::string param_name(p_id.c_str());
		const std::string param_value = dump_const(p_value);

		// Remove backslashes from parameters as these come from the internal RTLIL
		// naming scheme, but should not exist in the emitted firrtl blackboxes.
		// When firrtl is converted to verilog and given to downstream synthesis
		// tools, these tools expect to find blackbox names and parameters as they
		// were originally defined, i.e. without the extra RTLIL naming conventions.
		param_name.erase(
			std::remove(param_name.begin(), param_name.end(), '\\'),
			param_name.end()
		);

		f << stringf("%sparameter %s = %s\n", indent.c_str(), param_name.c_str(), param_value.c_str());
	}

	f << "\n";
}

/**
 * Emits extmodules for every instantiated blackbox in the design.
 *
 * RTLIL stores instance parameters at the cell's instantiation location.
 * However, firrtl does not support module parameterization (everything is
 * already elaborated). Firrtl instead supports external modules (extmodule),
 * i.e. blackboxes that are defined by verilog and which have no body in
 * firrtl itself other than the declaration of the blackboxes ports and
 * parameters.
 *
 * Furthermore, firrtl does not support parameterization (even of extmodules)
 * at a module's instantiation location and users must instead declare
 * different extmodules with different instance parameters in the extmodule
 * definition itself.
 *
 * This function goes through the design to identify all RTLIL blackboxes
 * and emit parameterized extmodules with a unique name for each of them. The
 * name that's given to the extmodule is
 *
 *     <blackbox_name>_<instance_name>
 *
 * Beware that it is therefore necessary for users to replace "parameterized"
 * instances in the RTLIL sense with these custom extmodules for the firrtl to
 * be valid.
 */
void emit_elaborated_extmodules(RTLIL::Design *design, std::ostream &f)
{
	for (auto module : design->modules())
	{
		for (auto cell : module->cells())
		{
			// Is this cell a module instance?
			bool cellIsModuleInstance = cell->type[0] != '$';

			if (cellIsModuleInstance)
			{
				// Find the module corresponding to this instance.
				auto modInstance = design->module(cell->type);
				// Ensure that we actually have a module instance
				if (modInstance == nullptr) {
					log_error("Unknown cell type %s\n", cell->type.c_str());
					return;
				}

				bool modIsBlackbox = modInstance->get_blackbox_attribute();

				if (modIsBlackbox)
				{
					emit_extmodule(cell, modInstance, f);
				}
			}
		}
	}
}

struct FirrtlWorker
{
	Module *module;
	std::ostream &f;

	dict<SigBit, pair<string, int>> reverse_wire_map;
	string unconn_id;
	RTLIL::Design *design;
	std::string indent;

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
			log_assert(cell->has_attribute(ID::hdlname));
			instanceOf = cell->get_string_attribute(ID::hdlname);
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

		// If the instance is that of a blackbox, use the modified extmodule name
		// that contains per-instance parameterizations. These instances were
		// emitted earlier in the firrtl backend.
		const std::string instanceName = instModule->get_blackbox_attribute() ?
			extmodule_name(cell, instModule) :
			instanceOf;

		std::string cellFileinfo = getFileinfo(cell);
		wire_exprs.push_back(stringf("%s" "inst %s%s of %s %s", indent.c_str(), cell_name.c_str(), cell_name_comment.c_str(), instanceName.c_str(), cellFileinfo.c_str()));

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
						YS_FALLTHROUGH
					case FD_OUT:
						sourceExpr = firstName;
						sinkExpr = secondExpr;
						sinkSig = &secondSig;
						break;
					case FD_NODIRECTION:
						log_warning("Instance port connection %s.%s is NODIRECTION; treating as IN\n", cell_type.c_str(), log_signal(it->second));
						YS_FALLTHROUGH
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
					wire_exprs.push_back(stringf("\n%s%s <= %s %s", indent.c_str(), sinkExpr.c_str(), sourceExpr.c_str(), cellFileinfo.c_str()));
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

	void emit_module()
	{
		std::string moduleFileinfo = getFileinfo(module);
		f << stringf("  module %s: %s\n", make_id(module->name), moduleFileinfo.c_str());
		vector<string> port_decls, wire_decls, mem_exprs, cell_exprs, wire_exprs;

		std::vector<Mem> memories = Mem::get_all_memories(module);
		for (auto &mem : memories)
			mem.narrow();

		for (auto wire : module->wires())
		{
			const auto wireName = make_id(wire->name);
			std::string wireFileinfo = getFileinfo(wire);

			// If a wire has initial data, issue a warning since FIRRTL doesn't currently support it.
			if (wire->attributes.count(ID::init)) {
				log_warning("Initial value (%s) for (%s.%s) not supported\n",
							wire->attributes.at(ID::init).as_string().c_str(),
							log_id(module), log_id(wire));
			}
			if (wire->port_id)
			{
				if (wire->port_input && wire->port_output)
					log_error("Module port %s.%s is inout!\n", log_id(module), log_id(wire));
				port_decls.push_back(stringf("%s%s %s: UInt<%d> %s\n", indent.c_str(), wire->port_input ? "input" : "output",
						wireName, wire->width, wireFileinfo.c_str()));
			}
			else
			{
				wire_decls.push_back(stringf("%swire %s: UInt<%d> %s\n", indent.c_str(), wireName, wire->width, wireFileinfo.c_str()));
			}
		}

		for (auto cell : module->cells())
		{
			Const ndef(0, 0);

			// Is this cell is a module instance?
			if (module->design->module(cell->type))
			{
				process_instance(cell, wire_exprs);
				continue;
			}

			// Not a module instance. Set up cell properties
			bool extract_y_bits = false;		// Assume no extraction of final bits will be required.
			int a_width = cell->parameters.at(ID::A_WIDTH, ndef).as_int();	// The width of "A"
			int b_width = cell->parameters.at(ID::B_WIDTH, ndef).as_int();	// The width of "A"
			const int y_width = cell->parameters.at(ID::Y_WIDTH, ndef).as_int();	// The width of the result
			const bool a_signed = cell->parameters.at(ID::A_SIGNED, ndef).as_bool();
			const bool b_signed = cell->parameters.at(ID::B_SIGNED, ndef).as_bool();
			bool firrtl_is_signed = a_signed;	// The result is signed (subsequent code may change this).
			int firrtl_width = 0;
			string primop;
			bool always_uint = false;
			string y_id = make_id(cell->name);
			std::string cellFileinfo = getFileinfo(cell);

			if (cell->type.in(ID($not), ID($logic_not), ID($_NOT_), ID($neg), ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_bool), ID($reduce_xnor)))
			{
				string a_expr = make_expr(cell->getPort(ID::A));
				wire_decls.push_back(stringf("%swire %s: UInt<%d> %s\n", indent.c_str(), y_id.c_str(), y_width, cellFileinfo.c_str()));

				if (a_signed) {
					a_expr = "asSInt(" + a_expr + ")";
				}

				// Don't use the results of logical operations (a single bit) to control padding
				if (!(cell->type.in(ID($eq), ID($eqx), ID($gt), ID($ge), ID($lt), ID($le), ID($ne), ID($nex), ID($reduce_bool), ID($logic_not)) && y_width == 1) ) {
					a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
				}

				// Assume the FIRRTL width is a single bit.
				firrtl_width = 1;
				if (cell->type.in(ID($not), ID($_NOT_))) primop = "not";
				else if (cell->type == ID($neg)) {
					primop = "neg";
					firrtl_is_signed = true;	// Result of "neg" is signed (an SInt).
					firrtl_width = a_width;
				} else if (cell->type == ID($logic_not)) {
					primop = "eq";
					a_expr = stringf("%s, UInt(0)", a_expr.c_str());
				}
				else if (cell->type == ID($reduce_and)) primop = "andr";
				else if (cell->type == ID($reduce_or)) primop = "orr";
				else if (cell->type == ID($reduce_xor)) primop = "xorr";
				else if (cell->type == ID($reduce_xnor)) {
					primop = "not";
					a_expr = stringf("xorr(%s)", a_expr.c_str());
				}
				else if (cell->type == ID($reduce_bool)) {
					primop = "neq";
					// Use the sign of the a_expr and its width as the type (UInt/SInt) and width of the comparand.
					a_expr = stringf("%s, %cInt<%d>(0)", a_expr.c_str(), a_signed ? 'S' : 'U', a_width);
				}

				string expr = stringf("%s(%s)", primop.c_str(), a_expr.c_str());

				if ((firrtl_is_signed && !always_uint))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("%s%s <= %s %s\n", indent.c_str(), y_id.c_str(), expr.c_str(), cellFileinfo.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));

				continue;
			}
			if (cell->type.in(ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($xor), ID($_XOR_), ID($xnor), ID($and), ID($_AND_), ID($or), ID($_OR_), ID($eq), ID($eqx),
                                        ID($gt), ID($ge), ID($lt), ID($le), ID($ne), ID($nex), ID($shr), ID($sshr), ID($sshl), ID($shl),
                                        ID($logic_and), ID($logic_or), ID($pow)))
			{
				string a_expr = make_expr(cell->getPort(ID::A));
				string b_expr = make_expr(cell->getPort(ID::B));
				std::string cellFileinfo = getFileinfo(cell);
				wire_decls.push_back(stringf("%swire %s: UInt<%d> %s\n", indent.c_str(), y_id.c_str(), y_width, cellFileinfo.c_str()));

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
				if (b_signed && !cell->type.in(ID($shr), ID($sshr), ID($shl), ID($sshl), ID($pow))) {
					b_expr = "asSInt(" + b_expr + ")";
					// Expand the "B" operand to the result width
					if (b_width < y_width) {
						b_expr = stringf("pad(%s, %d)", b_expr.c_str(), y_width);
						b_width = y_width;
					}
				}

				// For the arithmetic ops, expand operand widths to result widths befor performing the operation.
				// This corresponds (according to iverilog) to what verilog compilers implement.
				if (cell->type.in(ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($xor), ID($_XOR_), ID($xnor), ID($and), ID($_AND_), ID($or), ID($_OR_)))
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
				auto a_sig = cell->getPort(ID::A);

				if (cell->type == ID($add)) {
					primop = "add";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = max(a_width, b_width);
				} else if (cell->type == ID($sub)) {
					primop = "sub";
					firrtl_is_signed = true;
					int a_widthInc = (!a_signed && b_signed) ? 2 : (a_signed && !b_signed) ? 1 : 0;
					int b_widthInc = (a_signed && !b_signed) ? 2 : (!a_signed && b_signed) ? 1 : 0;
					firrtl_width = max(a_width + a_widthInc, b_width + b_widthInc);
				} else if (cell->type == ID($mul)) {
					primop = "mul";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = a_width + b_width;
				} else if (cell->type == ID($div)) {
					primop = "div";
					firrtl_is_signed = a_signed | b_signed;
					firrtl_width = a_width;
				} else if (cell->type == ID($mod)) {
					// "rem" = truncating modulo
					primop = "rem";
					firrtl_width = min(a_width, b_width);
				} else if (cell->type.in(ID($and), ID($_AND_))) {
					primop = "and";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type.in(ID($or), ID($_OR_))) {
					primop =  "or";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type.in(ID($xor), ID($_XOR_))) {
					primop = "xor";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if (cell->type == ID($xnor)) {
					primop = "xnor";
					always_uint = true;
					firrtl_width = max(a_width, b_width);
				}
				else if ((cell->type == ID($eq)) || (cell->type == ID($eqx))) {
					primop = "eq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == ID($ne)) || (cell->type == ID($nex))) {
					primop = "neq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == ID($gt)) {
					primop = "gt";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == ID($ge)) {
					primop = "geq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == ID($lt)) {
					primop = "lt";
					always_uint = true;
					firrtl_width = 1;
				}
				else if (cell->type == ID($le)) {
					primop = "leq";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == ID($shl)) || (cell->type == ID($sshl))) {
					// FIRRTL will widen the result (y) by the amount of the shift.
					// We'll need to offset this by extracting the un-widened portion as Verilog would do.
					extract_y_bits = true;
					// Is the shift amount constant?
					auto b_sig = cell->getPort(ID::B);
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
				else if ((cell->type == ID($shr)) || (cell->type == ID($sshr))) {
					// We don't need to extract a specific range of bits.
					extract_y_bits = false;
					// Is the shift amount constant?
					auto b_sig = cell->getPort(ID::B);
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
						if (cell->type == ID($shr)) {
							a_expr = "asUInt(" + a_expr + ")";
						}
					}
				}
				else if ((cell->type == ID($logic_and))) {
					primop = "and";
					a_expr = "neq(" + a_expr + ", UInt(0))";
					b_expr = "neq(" + b_expr + ", UInt(0))";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == ID($logic_or))) {
					primop = "or";
					a_expr = "neq(" + a_expr + ", UInt(0))";
					b_expr = "neq(" + b_expr + ", UInt(0))";
					always_uint = true;
					firrtl_width = 1;
				}
				else if ((cell->type == ID($pow))) {
					if (a_sig.is_fully_const() && a_sig.as_int() == 2) {
						// We'll convert this to a shift. To simplify things, change the a_expr to "1"
						//	so we can use b_expr directly as a shift amount.
						// Only support 2 ** N (i.e., shift left)
						// FIRRTL will widen the result (y) by the amount of the shift.
						// We'll need to offset this by extracting the un-widened portion as Verilog would do.
						a_expr = firrtl_is_signed ? "SInt(1)" : "UInt(1)";
						extract_y_bits = true;
						// Is the shift amount constant?
						auto b_sig = cell->getPort(ID::B);
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

				auto it = cell->parameters.find(ID::B_SIGNED);
				if (it == cell->parameters.end() || !it->second.as_bool()) {
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

				cell_exprs.push_back(stringf("%s%s <= %s %s\n", indent.c_str(), y_id.c_str(), expr.c_str(), cellFileinfo.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));

				continue;
			}

			if (cell->type.in(ID($mux), ID($_MUX_)))
			{
				auto it = cell->parameters.find(ID::WIDTH);
				int width = it == cell->parameters.end()? 1 : it->second.as_int();
				string a_expr = make_expr(cell->getPort(ID::A));
				string b_expr = make_expr(cell->getPort(ID::B));
				string s_expr = make_expr(cell->getPort(ID::S));
				wire_decls.push_back(stringf("%swire %s: UInt<%d> %s\n", indent.c_str(), y_id.c_str(), width, cellFileinfo.c_str()));

				string expr = stringf("mux(%s, %s, %s)", s_expr.c_str(), b_expr.c_str(), a_expr.c_str());

				cell_exprs.push_back(stringf("%s%s <= %s %s\n", indent.c_str(), y_id.c_str(), expr.c_str(), cellFileinfo.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));

				continue;
			}

			if (cell->is_mem_cell())
			{
				// Will be handled below, as part of a Mem.
				continue;
			}

			if (cell->type.in(ID($dff)))
			{
				bool clkpol = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				if (clkpol == false)
					log_error("Negative edge clock on FF %s.%s.\n", log_id(module), log_id(cell));

				int width = cell->parameters.at(ID::WIDTH).as_int();
				string expr = make_expr(cell->getPort(ID::D));
				string clk_expr = "asClock(" + make_expr(cell->getPort(ID::CLK)) + ")";

				wire_decls.push_back(stringf("%sreg %s: UInt<%d>, %s %s\n", indent.c_str(), y_id.c_str(), width, clk_expr.c_str(), cellFileinfo.c_str()));

				cell_exprs.push_back(stringf("%s%s <= %s %s\n", indent.c_str(), y_id.c_str(), expr.c_str(), cellFileinfo.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Q));

				continue;
			}

			if (cell->type == ID($shiftx)) {
				// assign y = a[b +: y_width];
				// We'll extract the correct bits as part of the primop.

				string a_expr = make_expr(cell->getPort(ID::A));
				// Get the initial bit selector
				string b_expr = make_expr(cell->getPort(ID::B));
				wire_decls.push_back(stringf("%swire %s: UInt<%d>\n", indent.c_str(), y_id.c_str(), y_width));

				if (cell->getParam(ID::B_SIGNED).as_bool()) {
					// Use validif to constrain the selection (test the sign bit)
					auto b_string = b_expr.c_str();
					int b_sign = cell->parameters.at(ID::B_WIDTH).as_int() - 1;
					b_expr = stringf("validif(not(bits(%s, %d, %d)), %s)", b_string, b_sign, b_sign, b_string);
				}
				string expr = stringf("dshr(%s, %s)", a_expr.c_str(), b_expr.c_str());

				cell_exprs.push_back(stringf("%s%s <= %s\n", indent.c_str(), y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));
				continue;
			}
			if (cell->type == ID($shift)) {
				// assign y = a >> b;
				//  where b may be negative

				string a_expr = make_expr(cell->getPort(ID::A));
				string b_expr = make_expr(cell->getPort(ID::B));
				auto b_string = b_expr.c_str();
				string expr;
				wire_decls.push_back(stringf("%swire %s: UInt<%d>\n", indent.c_str(), y_id.c_str(), y_width));

				if (cell->getParam(ID::B_SIGNED).as_bool()) {
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
				cell_exprs.push_back(stringf("%s%s <= %s\n", indent.c_str(), y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));
				continue;
			}
			if (cell->type == ID($pos)) {
				// assign y = a;
//				printCell(cell);
				string a_expr = make_expr(cell->getPort(ID::A));
				// Verilog appears to treat the result as signed, so if the result is wider than "A",
				//  we need to pad.
				if (a_width < y_width) {
					a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
				}
				wire_decls.push_back(stringf("%swire %s: UInt<%d>\n", indent.c_str(), y_id.c_str(), y_width));
				cell_exprs.push_back(stringf("%s%s <= %s\n", indent.c_str(), y_id.c_str(), a_expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort(ID::Y));
				continue;
			}

			if (cell->type == ID($scopeinfo))
				continue;
			log_error("Cell type not supported: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
		}

		for (auto &mem : memories) {
			string mem_id = make_id(mem.memid);

			Const init_data = mem.get_init_data();
			if (!init_data.is_fully_undef())
				log_error("Memory with initialization data: %s.%s\n", log_id(module), log_id(mem.memid));

			if (mem.start_offset != 0)
				log_error("Memory with nonzero offset: %s.%s\n", log_id(module), log_id(mem.memid));

			for (int i = 0; i < GetSize(mem.rd_ports); i++)
			{
				auto &port = mem.rd_ports[i];
				string port_name(stringf("%s.r%d", mem_id.c_str(), i));

				if (port.clk_enable)
					log_error("Clocked read port %d on memory %s.%s.\n", i, log_id(module), log_id(mem.memid));

				std::ostringstream rpe;

				string addr_expr = make_expr(port.addr);
				string ena_expr = make_expr(State::S1);
				string clk_expr = make_expr(State::S0);

				rpe << stringf("%s%s.addr <= %s\n", indent.c_str(), port_name.c_str(), addr_expr.c_str());
				rpe << stringf("%s%s.en <= %s\n", indent.c_str(), port_name.c_str(), ena_expr.c_str());
				rpe << stringf("%s%s.clk <= asClock(%s)\n", indent.c_str(), port_name.c_str(), clk_expr.c_str());
				cell_exprs.push_back(rpe.str());
				register_reverse_wire_map(stringf("%s.data", port_name.c_str()), port.data);
			}

			for (int i = 0; i < GetSize(mem.wr_ports); i++)
			{
				auto &port = mem.wr_ports[i];
				string port_name(stringf("%s.w%d", mem_id.c_str(), i));

				if (!port.clk_enable)
					log_error("Unclocked write port %d on memory %s.%s.\n", i, log_id(module), log_id(mem.memid));
				if (!port.clk_polarity)
					log_error("Negedge write port %d on memory %s.%s.\n", i, log_id(module), log_id(mem.memid));
				for (int i = 1; i < GetSize(port.en); i++)
					if (port.en[0] != port.en[i])
						log_error("Complex write enable on port %d on memory %s.%s.\n", i, log_id(module), log_id(mem.memid));

				std::ostringstream wpe;

				string data_expr = make_expr(port.data);
				string addr_expr = make_expr(port.addr);
				string ena_expr = make_expr(port.en[0]);
				string clk_expr = make_expr(port.clk);
				string mask_expr = make_expr(State::S1);
				wpe << stringf("%s%s.data <= %s\n", indent.c_str(), port_name.c_str(), data_expr.c_str());
				wpe << stringf("%s%s.addr <= %s\n", indent.c_str(), port_name.c_str(), addr_expr.c_str());
				wpe << stringf("%s%s.en <= %s\n", indent.c_str(), port_name.c_str(), ena_expr.c_str());
				wpe << stringf("%s%s.clk <= asClock(%s)\n", indent.c_str(), port_name.c_str(), clk_expr.c_str());
				wpe << stringf("%s%s.mask <= %s\n", indent.c_str(), port_name.c_str(), mask_expr.c_str());

				cell_exprs.push_back(wpe.str());
			}

			std::ostringstream me;

			me << stringf("    mem %s:\n", mem_id.c_str());
			me << stringf("      data-type => UInt<%d>\n", mem.width);
			me << stringf("      depth => %d\n", mem.size);
			for (int i = 0; i < GetSize(mem.rd_ports); i++)
				me << stringf("      reader => r%d\n", i);
			for (int i = 0; i < GetSize(mem.wr_ports); i++)
				me << stringf("      writer => w%d\n", i);
			me << stringf("      read-latency => %d\n", 0);
			me << stringf("      write-latency => %d\n", 1);
			me << stringf("      read-under-write => undefined\n");

			mem_exprs.push_back(me.str());
		}

		for (auto conn : module->connections())
		{
			string y_id = next_id();
			int y_width =  GetSize(conn.first);
			string expr = make_expr(conn.second);

			wire_decls.push_back(stringf("%swire %s: UInt<%d>\n", indent.c_str(), y_id.c_str(), y_width));
			cell_exprs.push_back(stringf("%s%s <= %s\n", indent.c_str(), y_id.c_str(), expr.c_str()));
			register_reverse_wire_map(y_id, conn.first);
		}

		for (auto wire : module->wires())
		{
			string expr;
			std::string wireFileinfo = getFileinfo(wire);

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
					wire_decls.push_back(stringf("%swire %s: UInt<1> %s\n", indent.c_str(), unconn_id.c_str(), wireFileinfo.c_str()));
					// `invalid` is a firrtl construction for simulation so we will not
					// tag it with a @[fileinfo] tag as it doesn't directly correspond to
					// a specific line of verilog code.
					wire_decls.push_back(stringf("%s%s is invalid\n", indent.c_str(), unconn_id.c_str()));
				}
				wire_exprs.push_back(stringf("%s%s <= %s %s\n", indent.c_str(), make_id(wire->name), expr.c_str(), wireFileinfo.c_str()));
			} else {
				if (make_unconn_id) {
					unconn_id.clear();
				}
				// `invalid` is a firrtl construction for simulation so we will not
				// tag it with a @[fileinfo] tag as it doesn't directly correspond to
				// a specific line of verilog code.
				wire_decls.push_back(stringf("%s%s is invalid\n", indent.c_str(), make_id(wire->name)));
			}
		}

		for (auto str : port_decls)
			f << str;

		f << stringf("\n");

		for (auto str : wire_decls)
			f << str;

		f << stringf("\n");

		for (auto str : mem_exprs)
			f << str;

		f << stringf("\n");

		for (auto str : cell_exprs)
			f << str;

		f << stringf("\n");

		for (auto str : wire_exprs)
			f << str;

		f << stringf("\n");
	}

	void run()
	{
		emit_module();
	}
};

struct FirrtlBackend : public Backend {
	FirrtlBackend() : Backend("firrtl", "write design to a FIRRTL file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_firrtl [options] [filename]\n");
		log("\n");
		log("Write a FIRRTL netlist of the current design.\n");
		log("The following commands are executed by this command:\n");
		log("        pmuxtree\n");
		log("        bmuxmap\n");
		log("        demuxmap\n");
		log("        bwmuxmap\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
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

		Pass::call(design, "pmuxtree");
		Pass::call(design, "bmuxmap");
		Pass::call(design, "demuxmap");
		Pass::call(design, "bwmuxmap");

		namecache.clear();
		autoid_counter = 0;

		// Get the top module, or a reasonable facsimile - we need something for the circuit name.
		Module *top = design->top_module();
		Module *last = nullptr;
		// Generate module and wire names.
		for (auto module : design->modules()) {
			make_id(module->name);
			last = module;
			if (top == nullptr && module->get_bool_attribute(ID::top)) {
				top = module;
			}
			for (auto wire : module->wires())
				if (wire->port_id)
					make_id(wire->name);
		}

		if (top == nullptr)
			top = last;

		if (!top)
			log_cmd_error("There is no top module in this design!\n");

		std::string circuitFileinfo = getFileinfo(top);
		*f << stringf("circuit %s: %s\n", make_id(top->name), circuitFileinfo.c_str());

		emit_elaborated_extmodules(design, *f);

		// Emit non-blackbox modules.
		for (auto module : design->modules())
		{
			if (!module->get_blackbox_attribute())
			{
				FirrtlWorker worker(module, *f, design);
				worker.run();
			}
		}

		namecache.clear();
		autoid_counter = 0;
	}
} FirrtlBackend;

PRIVATE_NAMESPACE_END
