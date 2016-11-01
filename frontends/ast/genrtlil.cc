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
 *  ---
 *
 *  This is the AST frontend library.
 *
 *  The AST frontend library is not a frontend on it's own but provides a
 *  generic abstract syntax tree (AST) abstraction for HDL code and can be
 *  used by HDL frontends. See "ast.h" for an overview of the API and the
 *  Verilog frontend for an usage example.
 *
 */

#include "kernel/log.h"
#include "kernel/utils.h"
#include "libs/sha1/sha1.h"
#include "ast.h"

#include <sstream>
#include <stdarg.h>
#include <algorithm>

YOSYS_NAMESPACE_BEGIN

using namespace AST;
using namespace AST_INTERNAL;

// helper function for creating RTLIL code for unary operations
static RTLIL::SigSpec uniop2rtlil(AstNode *that, std::string type, int result_width, const RTLIL::SigSpec &arg, bool gen_attributes = true)
{
	std::stringstream sstr;
	sstr << type << "$" << that->filename << ":" << that->linenum << "$" << (autoidx++);

	RTLIL::Cell *cell = current_module->addCell(sstr.str(), type);
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	RTLIL::Wire *wire = current_module->addWire(cell->name.str() + "_Y", result_width);
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	if (gen_attributes)
		for (auto &attr : that->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), that->filename.c_str(), that->linenum);
			cell->attributes[attr.first] = attr.second->asAttrConst();
		}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(that->children[0]->is_signed);
	cell->parameters["\\A_WIDTH"] = RTLIL::Const(arg.size());
	cell->setPort("\\A", arg);

	cell->parameters["\\Y_WIDTH"] = result_width;
	cell->setPort("\\Y", wire);
	return wire;
}

// helper function for extending bit width (preferred over SigSpec::extend() because of correct undef propagation in ConstEval)
static void widthExtend(AstNode *that, RTLIL::SigSpec &sig, int width, bool is_signed)
{
	if (width <= sig.size()) {
		sig.extend_u0(width, is_signed);
		return;
	}

	std::stringstream sstr;
	sstr << "$extend" << "$" << that->filename << ":" << that->linenum << "$" << (autoidx++);

	RTLIL::Cell *cell = current_module->addCell(sstr.str(), "$pos");
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	RTLIL::Wire *wire = current_module->addWire(cell->name.str() + "_Y", width);
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	if (that != NULL)
		for (auto &attr : that->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), that->filename.c_str(), that->linenum);
			cell->attributes[attr.first] = attr.second->asAttrConst();
		}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(is_signed);
	cell->parameters["\\A_WIDTH"] = RTLIL::Const(sig.size());
	cell->setPort("\\A", sig);

	cell->parameters["\\Y_WIDTH"] = width;
	cell->setPort("\\Y", wire);
	sig = wire;
}

// helper function for creating RTLIL code for binary operations
static RTLIL::SigSpec binop2rtlil(AstNode *that, std::string type, int result_width, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	std::stringstream sstr;
	sstr << type << "$" << that->filename << ":" << that->linenum << "$" << (autoidx++);

	RTLIL::Cell *cell = current_module->addCell(sstr.str(), type);
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	RTLIL::Wire *wire = current_module->addWire(cell->name.str() + "_Y", result_width);
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	for (auto &attr : that->attributes) {
		if (attr.second->type != AST_CONSTANT)
			log_error("Attribute `%s' with non-constant value at %s:%d!\n",
					attr.first.c_str(), that->filename.c_str(), that->linenum);
		cell->attributes[attr.first] = attr.second->asAttrConst();
	}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(that->children[0]->is_signed);
	cell->parameters["\\B_SIGNED"] = RTLIL::Const(that->children[1]->is_signed);

	cell->parameters["\\A_WIDTH"] = RTLIL::Const(left.size());
	cell->parameters["\\B_WIDTH"] = RTLIL::Const(right.size());

	cell->setPort("\\A", left);
	cell->setPort("\\B", right);

	cell->parameters["\\Y_WIDTH"] = result_width;
	cell->setPort("\\Y", wire);
	return wire;
}

// helper function for creating RTLIL code for multiplexers
static RTLIL::SigSpec mux2rtlil(AstNode *that, const RTLIL::SigSpec &cond, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	log_assert(cond.size() == 1);

	std::stringstream sstr;
	sstr << "$ternary$" << that->filename << ":" << that->linenum << "$" << (autoidx++);

	RTLIL::Cell *cell = current_module->addCell(sstr.str(), "$mux");
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	RTLIL::Wire *wire = current_module->addWire(cell->name.str() + "_Y", left.size());
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);

	for (auto &attr : that->attributes) {
		if (attr.second->type != AST_CONSTANT)
			log_error("Attribute `%s' with non-constant value at %s:%d!\n",
					attr.first.c_str(), that->filename.c_str(), that->linenum);
		cell->attributes[attr.first] = attr.second->asAttrConst();
	}

	cell->parameters["\\WIDTH"] = RTLIL::Const(left.size());

	cell->setPort("\\A", right);
	cell->setPort("\\B", left);
	cell->setPort("\\S", cond);
	cell->setPort("\\Y", wire);

	return wire;
}

// helper class for converting AST always nodes to RTLIL processes
struct AST_INTERNAL::ProcessGenerator
{
	// input and output structures
	AstNode *always;
	RTLIL::SigSpec initSyncSignals;
	RTLIL::Process *proc;
	RTLIL::SigSpec outputSignals;

	// This always points to the RTLIL::CaseRule being filled at the moment
	RTLIL::CaseRule *current_case;

	// This map contains the replacement pattern to be used in the right hand side
	// of an assignment. E.g. in the code "foo = bar; foo = func(foo);" the foo in the right
	// hand side of the 2nd assignment needs to be replace with the temporary signal holding
	// the value assigned in the first assignment. So when the first assignment is processed
	// the according information is appended to subst_rvalue_from and subst_rvalue_to.
	stackmap<RTLIL::SigBit, RTLIL::SigBit> subst_rvalue_map;

	// This map contains the replacement pattern to be used in the left hand side
	// of an assignment. E.g. in the code "always @(posedge clk) foo <= bar" the signal bar
	// should not be connected to the signal foo. Instead it must be connected to the temporary
	// signal that is used as input for the register that drives the signal foo.
	stackmap<RTLIL::SigBit, RTLIL::SigBit> subst_lvalue_map;

	// The code here generates a number of temporary signal for each output register. This
	// map helps generating nice numbered names for all this temporary signals.
	std::map<RTLIL::Wire*, int> new_temp_count;

	// Buffer for generating the init action
	RTLIL::SigSpec init_lvalue, init_rvalue;

	ProcessGenerator(AstNode *always, RTLIL::SigSpec initSyncSignalsArg = RTLIL::SigSpec()) : always(always), initSyncSignals(initSyncSignalsArg)
	{
		// generate process and simple root case
		proc = new RTLIL::Process;
		proc->attributes["\\src"] = stringf("%s:%d", always->filename.c_str(), always->linenum);
		proc->name = stringf("$proc$%s:%d$%d", always->filename.c_str(), always->linenum, autoidx++);
		for (auto &attr : always->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), always->filename.c_str(), always->linenum);
			proc->attributes[attr.first] = attr.second->asAttrConst();
		}
		current_module->processes[proc->name] = proc;
		current_case = &proc->root_case;

		// create initial temporary signal for all output registers
		RTLIL::SigSpec subst_lvalue_from, subst_lvalue_to;
		collect_lvalues(subst_lvalue_from, always, true, true);
		subst_lvalue_to = new_temp_signal(subst_lvalue_from);
		subst_lvalue_map = subst_lvalue_from.to_sigbit_map(subst_lvalue_to);

		bool found_global_syncs = false;
		bool found_anyedge_syncs = false;
		for (auto child : always->children)
			if (child->type == AST_EDGE) {
				if (GetSize(child->children) == 1 && child->children.at(0)->type == AST_IDENTIFIER && child->children.at(0)->str == "\\$global_clock")
					found_global_syncs = true;
				else
					found_anyedge_syncs = true;
			}

		if (found_anyedge_syncs) {
			if (found_global_syncs)
				log_error("Found non-synthesizable event list at %s:%d!\n", always->filename.c_str(), always->linenum);
			log("Note: Assuming pure combinatorial block at %s:%d in\n", always->filename.c_str(), always->linenum);
			log("compliance with IEC 62142(E):2005 / IEEE Std. 1364.1(E):2002. Recommending\n");
			log("use of @* instead of @(...) for better match of synthesis and simulation.\n");
		}

		// create syncs for the process
		bool found_clocked_sync = false;
		for (auto child : always->children)
			if (child->type == AST_POSEDGE || child->type == AST_NEGEDGE) {
				found_clocked_sync = true;
				if (found_global_syncs || found_anyedge_syncs)
					log_error("Found non-synthesizable event list at %s:%d!\n", always->filename.c_str(), always->linenum);
				RTLIL::SyncRule *syncrule = new RTLIL::SyncRule;
				syncrule->type = child->type == AST_POSEDGE ? RTLIL::STp : RTLIL::STn;
				syncrule->signal = child->children[0]->genRTLIL();
				if (GetSize(syncrule->signal) != 1)
					log_error("Found posedge/negedge event on a signal that is not 1 bit wide at %s:%d!\n", always->filename.c_str(), always->linenum);
				addChunkActions(syncrule->actions, subst_lvalue_from, subst_lvalue_to, true);
				proc->syncs.push_back(syncrule);
			}
		if (proc->syncs.empty()) {
			RTLIL::SyncRule *syncrule = new RTLIL::SyncRule;
			syncrule->type = found_global_syncs ? RTLIL::STg : RTLIL::STa;
			syncrule->signal = RTLIL::SigSpec();
			addChunkActions(syncrule->actions, subst_lvalue_from, subst_lvalue_to, true);
			proc->syncs.push_back(syncrule);
		}

		// create initial assignments for the temporary signals
		if ((flag_nolatches || always->get_bool_attribute("\\nolatches") || current_module->get_bool_attribute("\\nolatches")) && !found_clocked_sync) {
			subst_rvalue_map = subst_lvalue_from.to_sigbit_dict(RTLIL::SigSpec(RTLIL::State::Sx, GetSize(subst_lvalue_from)));
		} else {
			addChunkActions(current_case->actions, subst_lvalue_to, subst_lvalue_from);
		}

		// process the AST
		for (auto child : always->children)
			if (child->type == AST_BLOCK)
				processAst(child);

		if (initSyncSignals.size() > 0)
		{
			RTLIL::SyncRule *sync = new RTLIL::SyncRule;
			sync->type = RTLIL::SyncType::STi;
			proc->syncs.push_back(sync);

			log_assert(init_lvalue.size() == init_rvalue.size());

			int offset = 0;
			for (auto &init_lvalue_c : init_lvalue.chunks()) {
				RTLIL::SigSpec lhs = init_lvalue_c;
				RTLIL::SigSpec rhs = init_rvalue.extract(offset, init_lvalue_c.width);
				remove_unwanted_lvalue_bits(lhs, rhs);
				sync->actions.push_back(RTLIL::SigSig(lhs, rhs));
				offset += lhs.size();
			}
		}

		outputSignals = RTLIL::SigSpec(subst_lvalue_from);
	}

	void remove_unwanted_lvalue_bits(RTLIL::SigSpec &lhs, RTLIL::SigSpec &rhs)
	{
		RTLIL::SigSpec new_lhs, new_rhs;

		log_assert(GetSize(lhs) == GetSize(rhs));
		for (int i = 0; i < GetSize(lhs); i++) {
			if (lhs[i].wire == nullptr)
				continue;
			new_lhs.append(lhs[i]);
			new_rhs.append(rhs[i]);
		}

		lhs = new_lhs;
		rhs = new_rhs;
	}

	// create new temporary signals
	RTLIL::SigSpec new_temp_signal(RTLIL::SigSpec sig)
	{
		std::vector<RTLIL::SigChunk> chunks = sig.chunks();

		for (int i = 0; i < GetSize(chunks); i++)
		{
			RTLIL::SigChunk &chunk = chunks[i];
			if (chunk.wire == NULL)
				continue;

			std::string wire_name;
			do {
				wire_name = stringf("$%d%s[%d:%d]", new_temp_count[chunk.wire]++,
						chunk.wire->name.c_str(), chunk.width+chunk.offset-1, chunk.offset);;
				if (chunk.wire->name.str().find('$') != std::string::npos)
					wire_name += stringf("$%d", autoidx++);
			} while (current_module->wires_.count(wire_name) > 0);

			RTLIL::Wire *wire = current_module->addWire(wire_name, chunk.width);
			wire->attributes["\\src"] = stringf("%s:%d", always->filename.c_str(), always->linenum);

			chunk.wire = wire;
			chunk.offset = 0;
		}

		return chunks;
	}

	// recursively traverse the AST an collect all assigned signals
	void collect_lvalues(RTLIL::SigSpec &reg, AstNode *ast, bool type_eq, bool type_le, bool run_sort_and_unify = true)
	{
		switch (ast->type)
		{
		case AST_CASE:
			for (auto child : ast->children)
				if (child != ast->children[0]) {
					log_assert(child->type == AST_COND || child->type == AST_CONDX || child->type == AST_CONDZ);
					collect_lvalues(reg, child, type_eq, type_le, false);
				}
			break;

		case AST_COND:
		case AST_CONDX:
		case AST_CONDZ:
		case AST_ALWAYS:
		case AST_INITIAL:
			for (auto child : ast->children)
				if (child->type == AST_BLOCK)
					collect_lvalues(reg, child, type_eq, type_le, false);
			break;

		case AST_BLOCK:
			for (auto child : ast->children) {
				if (child->type == AST_ASSIGN_EQ && type_eq)
					reg.append(child->children[0]->genRTLIL());
				if (child->type == AST_ASSIGN_LE && type_le)
					reg.append(child->children[0]->genRTLIL());
				if (child->type == AST_CASE || child->type == AST_BLOCK)
					collect_lvalues(reg, child, type_eq, type_le, false);
			}
			break;

		default:
			log_abort();
		}

		if (run_sort_and_unify) {
			std::set<RTLIL::SigBit> sorted_reg;
			for (auto bit : reg)
				if (bit.wire)
					sorted_reg.insert(bit);
			reg = RTLIL::SigSpec(sorted_reg);
		}
	}

	// remove all assignments to the given signal pattern in a case and all its children.
	// e.g. when the last statement in the code "a = 23; if (b) a = 42; a = 0;" is processed this
	// function is called to clean up the first two assignments as they are overwritten by
	// the third assignment.
	void removeSignalFromCaseTree(const RTLIL::SigSpec &pattern, RTLIL::CaseRule *cs)
	{
		for (auto it = cs->actions.begin(); it != cs->actions.end(); it++)
			it->first.remove2(pattern, &it->second);

		for (auto it = cs->switches.begin(); it != cs->switches.end(); it++)
			for (auto it2 = (*it)->cases.begin(); it2 != (*it)->cases.end(); it2++)
				removeSignalFromCaseTree(pattern, *it2);
	}

	// add an assignment (aka "action") but split it up in chunks. this way huge assignments
	// are avoided and the generated $mux cells have a more "natural" size.
	void addChunkActions(std::vector<RTLIL::SigSig> &actions, RTLIL::SigSpec lvalue, RTLIL::SigSpec rvalue, bool inSyncRule = false)
	{
		if (inSyncRule && initSyncSignals.size() > 0) {
			init_lvalue.append(lvalue.extract(initSyncSignals));
			init_rvalue.append(lvalue.extract(initSyncSignals, &rvalue));
			lvalue.remove2(initSyncSignals, &rvalue);
		}
		log_assert(lvalue.size() == rvalue.size());

		int offset = 0;
		for (auto &lvalue_c : lvalue.chunks()) {
			RTLIL::SigSpec lhs = lvalue_c;
			RTLIL::SigSpec rhs = rvalue.extract(offset, lvalue_c.width);
			if (inSyncRule && lvalue_c.wire && lvalue_c.wire->get_bool_attribute("\\nosync"))
				rhs = RTLIL::SigSpec(RTLIL::State::Sx, rhs.size());
			remove_unwanted_lvalue_bits(lhs, rhs);
			actions.push_back(RTLIL::SigSig(lhs, rhs));
			offset += lhs.size();
		}
	}

	// recursively process the AST and fill the RTLIL::Process
	void processAst(AstNode *ast)
	{
		switch (ast->type)
		{
		case AST_BLOCK:
			for (auto child : ast->children)
				processAst(child);
			break;

		case AST_ASSIGN_EQ:
		case AST_ASSIGN_LE:
			{
				RTLIL::SigSpec unmapped_lvalue = ast->children[0]->genRTLIL(), lvalue = unmapped_lvalue;
				RTLIL::SigSpec rvalue = ast->children[1]->genWidthRTLIL(lvalue.size(), &subst_rvalue_map.stdmap());

				pool<SigBit> lvalue_sigbits;
				for (int i = 0; i < GetSize(lvalue); i++) {
					if (lvalue_sigbits.count(lvalue[i]) > 0) {
						unmapped_lvalue.remove(i);
						lvalue.remove(i);
						rvalue.remove(i--);
					} else
						lvalue_sigbits.insert(lvalue[i]);
				}

				lvalue.replace(subst_lvalue_map.stdmap());

				if (ast->type == AST_ASSIGN_EQ) {
					for (int i = 0; i < GetSize(unmapped_lvalue); i++)
						subst_rvalue_map.set(unmapped_lvalue[i], rvalue[i]);
				}

				removeSignalFromCaseTree(lvalue, current_case);
				remove_unwanted_lvalue_bits(lvalue, rvalue);
				current_case->actions.push_back(RTLIL::SigSig(lvalue, rvalue));
			}
			break;

		case AST_CASE:
			{
				RTLIL::SwitchRule *sw = new RTLIL::SwitchRule;
				sw->attributes["\\src"] = stringf("%s:%d", ast->filename.c_str(), ast->linenum);
				sw->signal = ast->children[0]->genWidthRTLIL(-1, &subst_rvalue_map.stdmap());
				current_case->switches.push_back(sw);

				for (auto &attr : ast->attributes) {
					if (attr.second->type != AST_CONSTANT)
						log_error("Attribute `%s' with non-constant value at %s:%d!\n",
								attr.first.c_str(), ast->filename.c_str(), ast->linenum);
					sw->attributes[attr.first] = attr.second->asAttrConst();
				}

				RTLIL::SigSpec this_case_eq_lvalue;
				collect_lvalues(this_case_eq_lvalue, ast, true, false);

				RTLIL::SigSpec this_case_eq_ltemp = new_temp_signal(this_case_eq_lvalue);

				RTLIL::SigSpec this_case_eq_rvalue = this_case_eq_lvalue;
				this_case_eq_rvalue.replace(subst_rvalue_map.stdmap());

				RTLIL::CaseRule *default_case = NULL;
				RTLIL::CaseRule *last_generated_case = NULL;
				for (auto child : ast->children)
				{
					if (child == ast->children[0])
						continue;
					log_assert(child->type == AST_COND || child->type == AST_CONDX || child->type == AST_CONDZ);

					subst_lvalue_map.save();
					subst_rvalue_map.save();

					for (int i = 0; i < GetSize(this_case_eq_lvalue); i++)
						subst_lvalue_map.set(this_case_eq_lvalue[i], this_case_eq_ltemp[i]);

					RTLIL::CaseRule *backup_case = current_case;
					current_case = new RTLIL::CaseRule;
					last_generated_case = current_case;
					addChunkActions(current_case->actions, this_case_eq_ltemp, this_case_eq_rvalue);
					for (auto node : child->children) {
						if (node->type == AST_DEFAULT)
							default_case = current_case;
						else if (node->type == AST_BLOCK)
							processAst(node);
						else
							current_case->compare.push_back(node->genWidthRTLIL(sw->signal.size(), &subst_rvalue_map.stdmap()));
					}
					if (default_case != current_case)
						sw->cases.push_back(current_case);
					else
						log_assert(current_case->compare.size() == 0);
					current_case = backup_case;

					subst_lvalue_map.restore();
					subst_rvalue_map.restore();
				}

				if (last_generated_case != NULL && ast->get_bool_attribute("\\full_case") && default_case == NULL) {
					last_generated_case->compare.clear();
				} else {
					if (default_case == NULL) {
						default_case = new RTLIL::CaseRule;
						addChunkActions(default_case->actions, this_case_eq_ltemp, this_case_eq_rvalue);
					}
					sw->cases.push_back(default_case);
				}

				for (int i = 0; i < GetSize(this_case_eq_lvalue); i++)
					subst_rvalue_map.set(this_case_eq_lvalue[i], this_case_eq_ltemp[i]);

				this_case_eq_lvalue.replace(subst_lvalue_map.stdmap());
				removeSignalFromCaseTree(this_case_eq_lvalue, current_case);
				addChunkActions(current_case->actions, this_case_eq_lvalue, this_case_eq_ltemp);
			}
			break;

		case AST_WIRE:
			log_error("Found wire declaration in block without label at at %s:%d!\n", ast->filename.c_str(), ast->linenum);
			break;

		case AST_PARAMETER:
		case AST_LOCALPARAM:
			log_error("Found parameter declaration in block without label at at %s:%d!\n", ast->filename.c_str(), ast->linenum);
			break;

		case AST_NONE:
		case AST_TCALL:
		case AST_FOR:
			break;

		default:
			log_abort();
		}
	}
};

// detect sign and width of an expression
void AstNode::detectSignWidthWorker(int &width_hint, bool &sign_hint, bool *found_real)
{
	std::string type_name;
	bool sub_sign_hint = true;
	int sub_width_hint = -1;
	int this_width = 0;
	AstNode *range = NULL;
	AstNode *id_ast = NULL;

	bool local_found_real = false;
	if (found_real == NULL)
		found_real = &local_found_real;

	switch (type)
	{
	case AST_CONSTANT:
		width_hint = max(width_hint, int(bits.size()));
		if (!is_signed)
			sign_hint = false;
		break;

	case AST_REALVALUE:
		*found_real = true;
		width_hint = max(width_hint, 32);
		break;

	case AST_IDENTIFIER:
		id_ast = id2ast;
		if (id_ast == NULL && current_scope.count(str))
			id_ast = current_scope.at(str);
		if (!id_ast)
			log_error("Failed to resolve identifier %s for width detection at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
		if (id_ast->type == AST_PARAMETER || id_ast->type == AST_LOCALPARAM) {
			if (id_ast->children.size() > 1 && id_ast->children[1]->range_valid) {
				this_width = id_ast->children[1]->range_left - id_ast->children[1]->range_right + 1;
			} else
			if (id_ast->children[0]->type != AST_CONSTANT)
				while (id_ast->simplify(true, false, false, 1, -1, false, true)) { }
			if (id_ast->children[0]->type == AST_CONSTANT)
				this_width = id_ast->children[0]->bits.size();
			else
				log_error("Failed to detect width for parameter %s at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
			if (children.size() != 0)
				range = children[0];
		} else if (id_ast->type == AST_WIRE || id_ast->type == AST_AUTOWIRE) {
			if (!id_ast->range_valid) {
				if (id_ast->type == AST_AUTOWIRE)
					this_width = 1;
				else {
					// current_ast_mod->dumpAst(NULL, "mod> ");
					// log("---\n");
					// id_ast->dumpAst(NULL, "decl> ");
					// dumpAst(NULL, "ref> ");
					log_error("Failed to detect width of signal access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
				}
			} else {
				this_width = id_ast->range_left - id_ast->range_right + 1;
				if (children.size() != 0)
					range = children[0];
			}
		} else if (id_ast->type == AST_GENVAR) {
			this_width = 32;
		} else if (id_ast->type == AST_MEMORY) {
			if (!id_ast->children[0]->range_valid)
				log_error("Failed to detect width of memory access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
			this_width = id_ast->children[0]->range_left - id_ast->children[0]->range_right + 1;
		} else
			log_error("Failed to detect width for identifier %s at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
		if (range) {
			if (range->children.size() == 1)
				this_width = 1;
			else if (!range->range_valid) {
				AstNode *left_at_zero_ast = children[0]->children[0]->clone();
				AstNode *right_at_zero_ast = children[0]->children.size() >= 2 ? children[0]->children[1]->clone() : left_at_zero_ast->clone();
				while (left_at_zero_ast->simplify(true, true, false, 1, -1, false, false)) { }
				while (right_at_zero_ast->simplify(true, true, false, 1, -1, false, false)) { }
				if (left_at_zero_ast->type != AST_CONSTANT || right_at_zero_ast->type != AST_CONSTANT)
					log_error("Unsupported expression on dynamic range select on signal `%s' at %s:%d!\n",
							str.c_str(), filename.c_str(), linenum);
				this_width = left_at_zero_ast->integer - right_at_zero_ast->integer + 1;
				delete left_at_zero_ast;
				delete right_at_zero_ast;
			} else
				this_width = range->range_left - range->range_right + 1;
			sign_hint = false;
		}
		width_hint = max(width_hint, this_width);
		if (!id_ast->is_signed)
			sign_hint = false;
		break;

	case AST_TO_BITS:
		while (children[0]->simplify(true, false, false, 1, -1, false, false) == true) { }
		if (children[0]->type != AST_CONSTANT)
			log_error("Left operand of tobits expression is not constant at %s:%d!\n", filename.c_str(), linenum);
		children[1]->detectSignWidthWorker(sub_width_hint, sign_hint);
		width_hint = max(width_hint, children[0]->bitsAsConst().as_int());
		break;

	case AST_TO_SIGNED:
		children.at(0)->detectSignWidthWorker(width_hint, sub_sign_hint);
		break;

	case AST_TO_UNSIGNED:
		children.at(0)->detectSignWidthWorker(width_hint, sub_sign_hint);
		sign_hint = false;
		break;

	case AST_CONCAT:
		for (auto child : children) {
			sub_width_hint = 0;
			sub_sign_hint = true;
			child->detectSignWidthWorker(sub_width_hint, sub_sign_hint);
			this_width += sub_width_hint;
		}
		width_hint = max(width_hint, this_width);
		sign_hint = false;
		break;

	case AST_REPLICATE:
		while (children[0]->simplify(true, false, false, 1, -1, false, true) == true) { }
		if (children[0]->type != AST_CONSTANT)
			log_error("Left operand of replicate expression is not constant at %s:%d!\n", filename.c_str(), linenum);
		children[1]->detectSignWidthWorker(sub_width_hint, sub_sign_hint);
		width_hint = max(width_hint, children[0]->bitsAsConst().as_int() * sub_width_hint);
		sign_hint = false;
		break;

	case AST_NEG:
	case AST_BIT_NOT:
	case AST_POS:
		children[0]->detectSignWidthWorker(width_hint, sign_hint, found_real);
		break;

	case AST_BIT_AND:
	case AST_BIT_OR:
	case AST_BIT_XOR:
	case AST_BIT_XNOR:
		for (auto child : children)
			child->detectSignWidthWorker(width_hint, sign_hint, found_real);
		break;

	case AST_REDUCE_AND:
	case AST_REDUCE_OR:
	case AST_REDUCE_XOR:
	case AST_REDUCE_XNOR:
	case AST_REDUCE_BOOL:
		width_hint = max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_SHIFT_LEFT:
	case AST_SHIFT_RIGHT:
	case AST_SHIFT_SLEFT:
	case AST_SHIFT_SRIGHT:
	case AST_POW:
		children[0]->detectSignWidthWorker(width_hint, sign_hint, found_real);
		break;

	case AST_LT:
	case AST_LE:
	case AST_EQ:
	case AST_NE:
	case AST_EQX:
	case AST_NEX:
	case AST_GE:
	case AST_GT:
		width_hint = max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_ADD:
	case AST_SUB:
	case AST_MUL:
	case AST_DIV:
	case AST_MOD:
		for (auto child : children)
			child->detectSignWidthWorker(width_hint, sign_hint, found_real);
		break;

	case AST_LOGIC_AND:
	case AST_LOGIC_OR:
	case AST_LOGIC_NOT:
		width_hint = max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_TERNARY:
		children.at(1)->detectSignWidthWorker(width_hint, sign_hint, found_real);
		children.at(2)->detectSignWidthWorker(width_hint, sign_hint, found_real);
		break;

	case AST_MEMRD:
		if (!id2ast->is_signed)
			sign_hint = false;
		if (!id2ast->children[0]->range_valid)
			log_error("Failed to detect width of memory access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
		this_width = id2ast->children[0]->range_left - id2ast->children[0]->range_right + 1;
		width_hint = max(width_hint, this_width);
		break;

	case AST_FCALL:
		if (str == "\\$anyconst" || str == "\\$anyseq") {
			if (GetSize(children) == 1) {
				while (children[0]->simplify(true, false, false, 1, -1, false, true) == true) { }
				if (children[0]->type != AST_CONSTANT)
					log_error("System function %s called with non-const argument at %s:%d!\n",
							RTLIL::unescape_id(str).c_str(), filename.c_str(), linenum);
				width_hint = max(width_hint, int(children[0]->asInt(true)));
			}
			break;
		}
		if (str == "\\$past") {
			if (GetSize(children) > 0) {
				sub_width_hint = 0;
				sub_sign_hint = true;
				children.at(0)->detectSignWidthWorker(sub_width_hint, sub_sign_hint);
				width_hint = max(width_hint, sub_width_hint);
				sign_hint = false;
			}
			break;
		}
		/* fall through */

	// everything should have been handled above -> print error if not.
	default:
		for (auto f : log_files)
			current_ast->dumpAst(f, "verilog-ast> ");
		log_error("Don't know how to detect sign and width for %s node at %s:%d!\n",
				type2str(type).c_str(), filename.c_str(), linenum);
	}

	if (*found_real)
		sign_hint = true;
}

// detect sign and width of an expression
void AstNode::detectSignWidth(int &width_hint, bool &sign_hint, bool *found_real)
{
	width_hint = -1;
	sign_hint = true;
	if (found_real)
		*found_real = false;
	detectSignWidthWorker(width_hint, sign_hint, found_real);
}

// create RTLIL from an AST node
// all generated cells, wires and processes are added to the module pointed to by 'current_module'
// when the AST node is an expression (AST_ADD, AST_BIT_XOR, etc.), the result signal is returned.
//
// note that this function is influenced by a number of global variables that might be set when
// called from genWidthRTLIL(). also note that this function recursively calls itself to transform
// larger expressions into a netlist of cells.
RTLIL::SigSpec AstNode::genRTLIL(int width_hint, bool sign_hint)
{
	// in the following big switch() statement there are some uses of
	// Clifford's Device (http://www.clifford.at/cfun/cliffdev/). In this
	// cases this variable is used to hold the type of the cell that should
	// be instantiated for this type of AST node.
	std::string type_name;

	current_filename = filename;
	set_line_num(linenum);

	switch (type)
	{
	// simply ignore this nodes.
	// they are either leftovers from simplify() or are referenced by other nodes
	// and are only accessed here thru this references
	case AST_NONE:
	case AST_TASK:
	case AST_FUNCTION:
	case AST_DPI_FUNCTION:
	case AST_AUTOWIRE:
	case AST_LOCALPARAM:
	case AST_DEFPARAM:
	case AST_GENVAR:
	case AST_GENFOR:
	case AST_GENBLOCK:
	case AST_GENIF:
	case AST_GENCASE:
	case AST_PACKAGE:
		break;

	// remember the parameter, needed for example in techmap
	case AST_PARAMETER:
		current_module->avail_parameters.insert(str);
		break;

	// create an RTLIL::Wire for an AST_WIRE node
	case AST_WIRE: {
			if (current_module->wires_.count(str) != 0)
				log_error("Re-definition of signal `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);
			if (!range_valid)
				log_error("Signal `%s' with non-constant width at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			log_assert(range_left >= range_right || (range_left == -1 && range_right == 0));

			RTLIL::Wire *wire = current_module->addWire(str, range_left - range_right + 1);
			wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			wire->start_offset = range_right;
			wire->port_id = port_id;
			wire->port_input = is_input;
			wire->port_output = is_output;
			wire->upto = range_swapped;

			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				wire->attributes[attr.first] = attr.second->asAttrConst();
			}
		}
		break;

	// create an RTLIL::Memory for an AST_MEMORY node
	case AST_MEMORY: {
			if (current_module->memories.count(str) != 0)
				log_error("Re-definition of memory `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			log_assert(children.size() >= 2);
			log_assert(children[0]->type == AST_RANGE);
			log_assert(children[1]->type == AST_RANGE);

			if (!children[0]->range_valid || !children[1]->range_valid)
				log_error("Memory `%s' with non-constant width or size at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			RTLIL::Memory *memory = new RTLIL::Memory;
			memory->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			memory->name = str;
			memory->width = children[0]->range_left - children[0]->range_right + 1;
			if (children[1]->range_right < children[1]->range_left) {
				memory->start_offset = children[1]->range_right;
				memory->size = children[1]->range_left - children[1]->range_right + 1;
			} else {
				memory->start_offset = children[1]->range_left;
				memory->size = children[1]->range_right - children[1]->range_left + 1;
			}
			current_module->memories[memory->name] = memory;

			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				memory->attributes[attr.first] = attr.second->asAttrConst();
			}
		}
		break;

	// simply return the corresponding RTLIL::SigSpec for an AST_CONSTANT node
	case AST_CONSTANT:
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);

			is_signed = sign_hint;
			return RTLIL::SigSpec(bitsAsConst());
		}

	case AST_REALVALUE:
		{
			RTLIL::SigSpec sig = realAsConst(width_hint);
			log_warning("converting real value %e to binary %s at %s:%d.\n",
					realvalue, log_signal(sig), filename.c_str(), linenum);
			return sig;
		}

	// simply return the corresponding RTLIL::SigSpec for an AST_IDENTIFIER node
	// for identifiers with dynamic bit ranges (e.g. "foo[bar]" or "foo[bar+3:bar]") a
	// shifter cell is created and the output signal of this cell is returned
	case AST_IDENTIFIER:
		{
			RTLIL::Wire *wire = NULL;
			RTLIL::SigChunk chunk;

			int add_undef_bits_msb = 0;
			int add_undef_bits_lsb = 0;

			if (id2ast && id2ast->type == AST_AUTOWIRE && current_module->wires_.count(str) == 0) {
				RTLIL::Wire *wire = current_module->addWire(str);
				wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
				wire->name = str;
				if (flag_autowire)
					log_warning("Identifier `%s' is implicitly declared at %s:%d.\n", str.c_str(), filename.c_str(), linenum);
				else
					log_error("Identifier `%s' is implicitly declared at %s:%d and `default_nettype is set to none.\n", str.c_str(), filename.c_str(), linenum);
			}
			else if (id2ast->type == AST_PARAMETER || id2ast->type == AST_LOCALPARAM) {
				if (id2ast->children[0]->type != AST_CONSTANT)
					log_error("Parameter %s does not evaluate to constant value at %s:%d!\n",
							str.c_str(), filename.c_str(), linenum);
				chunk = RTLIL::Const(id2ast->children[0]->bits);
				goto use_const_chunk;
			}
			else if (!id2ast || (id2ast->type != AST_WIRE && id2ast->type != AST_AUTOWIRE &&
					id2ast->type != AST_MEMORY) || current_module->wires_.count(str) == 0)
				log_error("Identifier `%s' doesn't map to any signal at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			if (id2ast->type == AST_MEMORY)
				log_error("Identifier `%s' does map to an unexpanded memory at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			wire = current_module->wires_[str];
			chunk.wire = wire;
			chunk.width = wire->width;
			chunk.offset = 0;

		use_const_chunk:
			if (children.size() != 0) {
				log_assert(children[0]->type == AST_RANGE);
				int source_width = id2ast->range_left - id2ast->range_right + 1;
				int source_offset = id2ast->range_right;
				if (!children[0]->range_valid) {
					AstNode *left_at_zero_ast = children[0]->children[0]->clone();
					AstNode *right_at_zero_ast = children[0]->children.size() >= 2 ? children[0]->children[1]->clone() : left_at_zero_ast->clone();
					while (left_at_zero_ast->simplify(true, true, false, 1, -1, false, false)) { }
					while (right_at_zero_ast->simplify(true, true, false, 1, -1, false, false)) { }
					if (left_at_zero_ast->type != AST_CONSTANT || right_at_zero_ast->type != AST_CONSTANT)
						log_error("Unsupported expression on dynamic range select on signal `%s' at %s:%d!\n",
								str.c_str(), filename.c_str(), linenum);
					int width = left_at_zero_ast->integer - right_at_zero_ast->integer + 1;
					AstNode *fake_ast = new AstNode(AST_NONE, clone(), children[0]->children.size() >= 2 ?
							children[0]->children[1]->clone() : children[0]->children[0]->clone());
					fake_ast->children[0]->delete_children();
					RTLIL::SigSpec shift_val = fake_ast->children[1]->genRTLIL();
					if (id2ast->range_right != 0) {
						shift_val = current_module->Sub(NEW_ID, shift_val, id2ast->range_right, fake_ast->children[1]->is_signed);
						fake_ast->children[1]->is_signed = true;
					}
					if (id2ast->range_swapped) {
						shift_val = current_module->Sub(NEW_ID, RTLIL::SigSpec(source_width - width), shift_val, fake_ast->children[1]->is_signed);
						fake_ast->children[1]->is_signed = true;
					}
					if (GetSize(shift_val) >= 32)
						fake_ast->children[1]->is_signed = true;
					RTLIL::SigSpec sig = binop2rtlil(fake_ast, "$shiftx", width, fake_ast->children[0]->genRTLIL(), shift_val);
					delete left_at_zero_ast;
					delete right_at_zero_ast;
					delete fake_ast;
					return sig;
				} else {
					chunk.width = children[0]->range_left - children[0]->range_right + 1;
					chunk.offset = children[0]->range_right - source_offset;
					if (id2ast->range_swapped)
						chunk.offset = (id2ast->range_left - id2ast->range_right + 1) - (chunk.offset + chunk.width);
					if (chunk.offset >= source_width || chunk.offset + chunk.width < 0) {
						if (chunk.width == 1)
							log_warning("Range select out of bounds on signal `%s' at %s:%d: Setting result bit to undef.\n",
									str.c_str(), filename.c_str(), linenum);
						else
							log_warning("Range select out of bounds on signal `%s' at %s:%d: Setting all %d result bits to undef.\n",
									str.c_str(), filename.c_str(), linenum, chunk.width);
						chunk = RTLIL::SigChunk(RTLIL::State::Sx, chunk.width);
					} else {
						if (chunk.width + chunk.offset > source_width) {
							add_undef_bits_msb = (chunk.width + chunk.offset) - source_width;
							chunk.width -= add_undef_bits_msb;
						}
						if (chunk.offset < 0) {
							add_undef_bits_lsb = -chunk.offset;
							chunk.width -= add_undef_bits_lsb;
							chunk.offset += add_undef_bits_lsb;
						}
						if (add_undef_bits_lsb)
							log_warning("Range select out of bounds on signal `%s' at %s:%d: Setting %d LSB bits to undef.\n",
									str.c_str(), filename.c_str(), linenum, add_undef_bits_lsb);
						if (add_undef_bits_msb)
							log_warning("Range select out of bounds on signal `%s' at %s:%d: Setting %d MSB bits to undef.\n",
									str.c_str(), filename.c_str(), linenum, add_undef_bits_msb);
					}
				}
			}

			RTLIL::SigSpec sig = { RTLIL::SigSpec(RTLIL::State::Sx, add_undef_bits_msb), chunk, RTLIL::SigSpec(RTLIL::State::Sx, add_undef_bits_lsb) };

			if (genRTLIL_subst_ptr)
				sig.replace(*genRTLIL_subst_ptr);

			is_signed = children.size() > 0 ? false : id2ast->is_signed && sign_hint;
			return sig;
		}

	// just pass thru the signal. the parent will evaluate the is_signed property and interpret the SigSpec accordingly
	case AST_TO_SIGNED:
	case AST_TO_UNSIGNED: {
			RTLIL::SigSpec sig = children[0]->genRTLIL();
			if (sig.size() < width_hint)
				sig.extend_u0(width_hint, sign_hint);
			is_signed = sign_hint;
			return sig;
	}

	// concatenation of signals can be done directly using RTLIL::SigSpec
	case AST_CONCAT: {
			RTLIL::SigSpec sig;
			for (auto it = children.begin(); it != children.end(); it++)
				sig.append((*it)->genRTLIL());
			if (sig.size() < width_hint)
				sig.extend_u0(width_hint, false);
			return sig;
		}

	// replication of signals can be done directly using RTLIL::SigSpec
	case AST_REPLICATE: {
			RTLIL::SigSpec left = children[0]->genRTLIL();
			RTLIL::SigSpec right = children[1]->genRTLIL();
			if (!left.is_fully_const())
				log_error("Left operand of replicate expression is not constant at %s:%d!\n", filename.c_str(), linenum);
			int count = left.as_int();
			RTLIL::SigSpec sig;
			for (int i = 0; i < count; i++)
				sig.append(right);
			if (sig.size() < width_hint)
				sig.extend_u0(width_hint, false);
			is_signed = false;
			return sig;
		}

	// generate cells for unary operations: $not, $pos, $neg
	if (0) { case AST_BIT_NOT: type_name = "$not"; }
	if (0) { case AST_POS:     type_name = "$pos"; }
	if (0) { case AST_NEG:     type_name = "$neg"; }
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL(width_hint, sign_hint);
			is_signed = children[0]->is_signed;
			int width = arg.size();
			if (width_hint > 0) {
				width = width_hint;
				widthExtend(this, arg, width, is_signed);
			}
			return uniop2rtlil(this, type_name, width, arg);
		}

	// generate cells for binary operations: $and, $or, $xor, $xnor
	if (0) { case AST_BIT_AND:  type_name = "$and"; }
	if (0) { case AST_BIT_OR:   type_name = "$or"; }
	if (0) { case AST_BIT_XOR:  type_name = "$xor"; }
	if (0) { case AST_BIT_XNOR: type_name = "$xnor"; }
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);
			RTLIL::SigSpec left = children[0]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec right = children[1]->genRTLIL(width_hint, sign_hint);
			int width = max(left.size(), right.size());
			if (width_hint > 0)
				width = width_hint;
			is_signed = children[0]->is_signed && children[1]->is_signed;
			return binop2rtlil(this, type_name, width, left, right);
		}

	// generate cells for unary operations: $reduce_and, $reduce_or, $reduce_xor, $reduce_xnor
	if (0) { case AST_REDUCE_AND:  type_name = "$reduce_and"; }
	if (0) { case AST_REDUCE_OR:   type_name = "$reduce_or"; }
	if (0) { case AST_REDUCE_XOR:  type_name = "$reduce_xor"; }
	if (0) { case AST_REDUCE_XNOR: type_name = "$reduce_xnor"; }
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL();
			RTLIL::SigSpec sig = uniop2rtlil(this, type_name, max(width_hint, 1), arg);
			return sig;
		}

	// generate cells for unary operations: $reduce_bool
	// (this is actually just an $reduce_or, but for clarity a different cell type is used)
	if (0) { case AST_REDUCE_BOOL:  type_name = "$reduce_bool"; }
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL();
			RTLIL::SigSpec sig = arg.size() > 1 ? uniop2rtlil(this, type_name, max(width_hint, 1), arg) : arg;
			return sig;
		}

	// generate cells for binary operations: $shl, $shr, $sshl, $sshr
	if (0) { case AST_SHIFT_LEFT:   type_name = "$shl"; }
	if (0) { case AST_SHIFT_RIGHT:  type_name = "$shr"; }
	if (0) { case AST_SHIFT_SLEFT:  type_name = "$sshl"; }
	if (0) { case AST_SHIFT_SRIGHT: type_name = "$sshr"; }
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);
			RTLIL::SigSpec left = children[0]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec right = children[1]->genRTLIL();
			int width = width_hint > 0 ? width_hint : left.size();
			is_signed = children[0]->is_signed;
			return binop2rtlil(this, type_name, width, left, right);
		}

	// generate cells for binary operations: $pow
	case AST_POW:
		{
			int right_width;
			bool right_signed;
			children[1]->detectSignWidth(right_width, right_signed);
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);
			RTLIL::SigSpec left = children[0]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec right = children[1]->genRTLIL(right_width, right_signed);
			int width = width_hint > 0 ? width_hint : left.size();
			is_signed = children[0]->is_signed;
			if (!flag_noopt && left.is_fully_const() && left.as_int() == 2 && !right_signed)
				return binop2rtlil(this, "$shl", width, RTLIL::SigSpec(1, left.size()), right);
			return binop2rtlil(this, "$pow", width, left, right);
		}

	// generate cells for binary operations: $lt, $le, $eq, $ne, $ge, $gt
	if (0) { case AST_LT:  type_name = "$lt"; }
	if (0) { case AST_LE:  type_name = "$le"; }
	if (0) { case AST_EQ:  type_name = "$eq"; }
	if (0) { case AST_NE:  type_name = "$ne"; }
	if (0) { case AST_EQX: type_name = "$eqx"; }
	if (0) { case AST_NEX: type_name = "$nex"; }
	if (0) { case AST_GE:  type_name = "$ge"; }
	if (0) { case AST_GT:  type_name = "$gt"; }
		{
			int width = max(width_hint, 1);
			width_hint = -1, sign_hint = true;
			children[0]->detectSignWidthWorker(width_hint, sign_hint);
			children[1]->detectSignWidthWorker(width_hint, sign_hint);
			RTLIL::SigSpec left = children[0]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec right = children[1]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec sig = binop2rtlil(this, type_name, width, left, right);
			return sig;
		}

	// generate cells for binary operations: $add, $sub, $mul, $div, $mod
	if (0) { case AST_ADD: type_name = "$add"; }
	if (0) { case AST_SUB: type_name = "$sub"; }
	if (0) { case AST_MUL: type_name = "$mul"; }
	if (0) { case AST_DIV: type_name = "$div"; }
	if (0) { case AST_MOD: type_name = "$mod"; }
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);
			RTLIL::SigSpec left = children[0]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec right = children[1]->genRTLIL(width_hint, sign_hint);
		#if 0
			int width = max(left.size(), right.size());
			if (width > width_hint && width_hint > 0)
				width = width_hint;
			if (width < width_hint) {
				if (type == AST_ADD || type == AST_SUB || type == AST_DIV)
					width++;
				if (type == AST_SUB && (!children[0]->is_signed || !children[1]->is_signed))
					width = width_hint;
				if (type == AST_MUL)
					width = min(left.size() + right.size(), width_hint);
			}
		#else
			int width = max(max(left.size(), right.size()), width_hint);
		#endif
			is_signed = children[0]->is_signed && children[1]->is_signed;
			return binop2rtlil(this, type_name, width, left, right);
		}

	// generate cells for binary operations: $logic_and, $logic_or
	if (0) { case AST_LOGIC_AND: type_name = "$logic_and"; }
	if (0) { case AST_LOGIC_OR:  type_name = "$logic_or"; }
		{
			RTLIL::SigSpec left = children[0]->genRTLIL();
			RTLIL::SigSpec right = children[1]->genRTLIL();
			return binop2rtlil(this, type_name, max(width_hint, 1), left, right);
		}

	// generate cells for unary operations: $logic_not
	case AST_LOGIC_NOT:
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL();
			return uniop2rtlil(this, "$logic_not", max(width_hint, 1), arg);
		}

	// generate multiplexer for ternary operator (aka ?:-operator)
	case AST_TERNARY:
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);

			RTLIL::SigSpec cond = children[0]->genRTLIL();
			RTLIL::SigSpec val1 = children[1]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec val2 = children[2]->genRTLIL(width_hint, sign_hint);

			if (cond.size() > 1)
				cond = uniop2rtlil(this, "$reduce_bool", 1, cond, false);

			int width = max(val1.size(), val2.size());
			is_signed = children[1]->is_signed && children[2]->is_signed;
			widthExtend(this, val1, width, is_signed);
			widthExtend(this, val2, width, is_signed);

			RTLIL::SigSpec sig = mux2rtlil(this, cond, val1, val2);

			if (sig.size() < width_hint)
				sig.extend_u0(width_hint, sign_hint);
			return sig;
		}

	// generate $memrd cells for memory read ports
	case AST_MEMRD:
		{
			std::stringstream sstr;
			sstr << "$memrd$" << str << "$" << filename << ":" << linenum << "$" << (autoidx++);

			RTLIL::Cell *cell = current_module->addCell(sstr.str(), "$memrd");
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);

			RTLIL::Wire *wire = current_module->addWire(cell->name.str() + "_DATA", current_module->memories[str]->width);
			wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);

			int mem_width, mem_size, addr_bits;
			is_signed = id2ast->is_signed;
			id2ast->meminfo(mem_width, mem_size, addr_bits);

			RTLIL::SigSpec addr_sig = children[0]->genRTLIL();

			cell->setPort("\\CLK", RTLIL::SigSpec(RTLIL::State::Sx, 1));
			cell->setPort("\\EN", RTLIL::SigSpec(RTLIL::State::Sx, 1));
			cell->setPort("\\ADDR", addr_sig);
			cell->setPort("\\DATA", RTLIL::SigSpec(wire));

			cell->parameters["\\MEMID"] = RTLIL::Const(str);
			cell->parameters["\\ABITS"] = RTLIL::Const(GetSize(addr_sig));
			cell->parameters["\\WIDTH"] = RTLIL::Const(wire->width);

			cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(0);
			cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(0);
			cell->parameters["\\TRANSPARENT"] = RTLIL::Const(0);

			return RTLIL::SigSpec(wire);
		}

	// generate $memwr cells for memory write ports
	case AST_MEMWR:
	case AST_MEMINIT:
		{
			std::stringstream sstr;
			sstr << (type == AST_MEMWR ? "$memwr$" : "$meminit$") << str << "$" << filename << ":" << linenum << "$" << (autoidx++);

			RTLIL::Cell *cell = current_module->addCell(sstr.str(), type == AST_MEMWR ? "$memwr" : "$meminit");
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);

			int mem_width, mem_size, addr_bits;
			id2ast->meminfo(mem_width, mem_size, addr_bits);

			int num_words = 1;
			if (type == AST_MEMINIT) {
				if (children[2]->type != AST_CONSTANT)
					log_error("Memory init with non-constant word count at %s:%d!\n", filename.c_str(), linenum);
				num_words = int(children[2]->asInt(false));
				cell->parameters["\\WORDS"] = RTLIL::Const(num_words);
			}

			SigSpec addr_sig = children[0]->genRTLIL();

			cell->setPort("\\ADDR", addr_sig);
			cell->setPort("\\DATA", children[1]->genWidthRTLIL(current_module->memories[str]->width * num_words));

			cell->parameters["\\MEMID"] = RTLIL::Const(str);
			cell->parameters["\\ABITS"] = RTLIL::Const(GetSize(addr_sig));
			cell->parameters["\\WIDTH"] = RTLIL::Const(current_module->memories[str]->width);

			if (type == AST_MEMWR) {
				cell->setPort("\\CLK", RTLIL::SigSpec(RTLIL::State::Sx, 1));
				cell->setPort("\\EN", children[2]->genRTLIL());
				cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(0);
				cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(0);
			}

			cell->parameters["\\PRIORITY"] = RTLIL::Const(autoidx-1);
		}
		break;

	// generate $assert cells
	case AST_ASSERT:
	case AST_ASSUME:
		{
			const char *celltype = "$assert";
			if (type == AST_ASSUME) celltype = "$assume";

			log_assert(children.size() == 2);

			RTLIL::SigSpec check = children[0]->genRTLIL();
			if (GetSize(check) != 1)
				check = current_module->ReduceBool(NEW_ID, check);

			RTLIL::SigSpec en = children[1]->genRTLIL();
			if (GetSize(en) != 1)
				en = current_module->ReduceBool(NEW_ID, en);

			std::stringstream sstr;
			sstr << celltype << "$" << filename << ":" << linenum << "$" << (autoidx++);

			RTLIL::Cell *cell = current_module->addCell(sstr.str(), celltype);
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);

			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				cell->attributes[attr.first] = attr.second->asAttrConst();
			}

			cell->setPort("\\A", check);
			cell->setPort("\\EN", en);
		}
		break;

	// add entries to current_module->connections for assignments (outside of always blocks)
	case AST_ASSIGN:
		{
			RTLIL::SigSpec left = children[0]->genRTLIL();
			RTLIL::SigSpec right = children[1]->genWidthRTLIL(left.size());
			if (left.has_const()) {
				RTLIL::SigSpec new_left, new_right;
				for (int i = 0; i < GetSize(left); i++)
					if (left[i].wire) {
						new_left.append(left[i]);
						new_right.append(right[i]);
					}
				log_warning("Ignoring assignment to constant bits at %s:%d:\n"
						"    old assignment: %s = %s\n    new assignment: %s = %s.\n",
						filename.c_str(), linenum, log_signal(left), log_signal(right),
						log_signal(new_left), log_signal(new_right));
				left = new_left;
				right = new_right;
			}
			current_module->connect(RTLIL::SigSig(left, right));
		}
		break;

	// create an RTLIL::Cell for an AST_CELL
	case AST_CELL:
		{
			int port_counter = 0, para_counter = 0;

			if (current_module->count_id(str) != 0)
				log_error("Re-definition of cell `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			RTLIL::Cell *cell = current_module->addCell(str, "");
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);

			for (auto it = children.begin(); it != children.end(); it++) {
				AstNode *child = *it;
				if (child->type == AST_CELLTYPE) {
					cell->type = child->str;
					if (flag_icells && cell->type.substr(0, 2) == "\\$")
						cell->type = cell->type.substr(1);
					continue;
				}
				if (child->type == AST_PARASET) {
					IdString paraname = child->str.empty() ? stringf("$%d", ++para_counter) : child->str;
					if (child->children[0]->type == AST_REALVALUE) {
						log_warning("Replacing floating point parameter %s.%s = %f with string at %s:%d.\n",
							log_id(cell), log_id(paraname), child->children[0]->realvalue,
							filename.c_str(), linenum);
						auto strnode = AstNode::mkconst_str(stringf("%f", child->children[0]->realvalue));
						strnode->cloneInto(child->children[0]);
						delete strnode;
					}
					if (child->children[0]->type != AST_CONSTANT)
						log_error("Parameter %s.%s with non-constant value at %s:%d!\n",
								log_id(cell), log_id(paraname), filename.c_str(), linenum);
					cell->parameters[paraname] = child->children[0]->asParaConst();
					continue;
				}
				if (child->type == AST_ARGUMENT) {
					RTLIL::SigSpec sig;
					if (child->children.size() > 0)
						sig = child->children[0]->genRTLIL();
					if (child->str.size() == 0) {
						char buf[100];
						snprintf(buf, 100, "$%d", ++port_counter);
						cell->setPort(buf, sig);
					} else {
						cell->setPort(child->str, sig);
					}
					continue;
				}
				log_abort();
			}
			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				cell->attributes[attr.first] = attr.second->asAttrConst();
			}
		}
		break;

	// use ProcessGenerator for always blocks
	case AST_ALWAYS: {
			AstNode *always = this->clone();
			ProcessGenerator generator(always);
			ignoreThisSignalsInInitial.append(generator.outputSignals);
			delete always;
		} break;

	case AST_INITIAL: {
			AstNode *always = this->clone();
			ProcessGenerator generator(always, ignoreThisSignalsInInitial);
			delete always;
		} break;

	case AST_FCALL: {
			if (str == "\\$anyconst" || str == "\\$anyseq")
			{
				string myid = stringf("%s$%d", str.c_str() + 1, autoidx++);
				int width = width_hint;

				if (GetSize(children) > 1)
					log_error("System function %s got %d arguments, expected 1 or 0 at %s:%d.\n",
							RTLIL::unescape_id(str).c_str(), GetSize(children), filename.c_str(), linenum);

				if (GetSize(children) == 1) {
					if (children[0]->type != AST_CONSTANT)
						log_error("System function %s called with non-const argument at %s:%d!\n",
								RTLIL::unescape_id(str).c_str(), filename.c_str(), linenum);
					width = children[0]->asInt(true);
				}

				if (width <= 0)
					log_error("Failed to detect width of %s at %s:%d!\n",
							RTLIL::unescape_id(str).c_str(), filename.c_str(), linenum);

				Cell *cell = current_module->addCell(myid, str.substr(1));
				cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
				cell->parameters["\\WIDTH"] = width;

				Wire *wire = current_module->addWire(myid + "_wire", width);
				wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
				cell->setPort("\\Y", wire);

				is_signed = sign_hint;
				return SigSpec(wire);
			}
		} /* fall through */

	// everything should have been handled above -> print error if not.
	default:
		for (auto f : log_files)
			current_ast->dumpAst(f, "verilog-ast> ");
		type_name = type2str(type);
		log_error("Don't know how to generate RTLIL code for %s node at %s:%d!\n",
				type_name.c_str(), filename.c_str(), linenum);
	}

	return RTLIL::SigSpec();
}

// this is a wrapper for AstNode::genRTLIL() when a specific signal width is requested and/or
// signals must be substituted before being used as input values (used by ProcessGenerator)
// note that this is using some global variables to communicate this special settings to AstNode::genRTLIL().
RTLIL::SigSpec AstNode::genWidthRTLIL(int width, const dict<RTLIL::SigBit, RTLIL::SigBit> *new_subst_ptr)
{
	const dict<RTLIL::SigBit, RTLIL::SigBit> *backup_subst_ptr = genRTLIL_subst_ptr;

	if (new_subst_ptr)
		genRTLIL_subst_ptr = new_subst_ptr;

	bool sign_hint = true;
	int width_hint = width;
	detectSignWidthWorker(width_hint, sign_hint);
	RTLIL::SigSpec sig = genRTLIL(width_hint, sign_hint);

	genRTLIL_subst_ptr = backup_subst_ptr;

	if (width >= 0)
		sig.extend_u0(width, is_signed);

	return sig;
}

YOSYS_NAMESPACE_END

