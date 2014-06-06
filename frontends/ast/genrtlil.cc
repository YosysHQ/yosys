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
#include "libs/sha1/sha1.h"
#include "ast.h"

#include <sstream>
#include <stdarg.h>
#include <assert.h>
#include <algorithm>

using namespace AST;
using namespace AST_INTERNAL;

// helper function for creating RTLIL code for unary operations
static RTLIL::SigSpec uniop2rtlil(AstNode *that, std::string type, int result_width, const RTLIL::SigSpec &arg, bool gen_attributes = true)
{
	std::stringstream sstr;
	sstr << type << "$" << that->filename << ":" << that->linenum << "$" << (RTLIL::autoidx++);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	cell->name = sstr.str();
	cell->type = type;
	current_module->cells[cell->name] = cell;

	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	wire->name = cell->name + "_Y";
	wire->width = result_width;
	current_module->wires[wire->name] = wire;

	RTLIL::SigChunk chunk;
	chunk.wire = wire;
	chunk.width = wire->width;
	chunk.offset = 0;

	RTLIL::SigSpec sig;
	sig.chunks.push_back(chunk);
	sig.width = chunk.width;

	if (gen_attributes)
		for (auto &attr : that->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), that->filename.c_str(), that->linenum);
			cell->attributes[attr.first] = attr.second->asAttrConst();
		}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(that->children[0]->is_signed);
	cell->parameters["\\A_WIDTH"] = RTLIL::Const(arg.width);
	cell->connections["\\A"] = arg;

	cell->parameters["\\Y_WIDTH"] = result_width;
	cell->connections["\\Y"] = sig;
	return sig;
}

// helper function for extending bit width (preferred over SigSpec::extend() because of correct undef propagation in ConstEval)
static void widthExtend(AstNode *that, RTLIL::SigSpec &sig, int width, bool is_signed, std::string celltype)
{
	if (width <= sig.width) {
		sig.extend(width, is_signed);
		return;
	}

	std::stringstream sstr;
	sstr << "$extend" << "$" << that->filename << ":" << that->linenum << "$" << (RTLIL::autoidx++);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	cell->name = sstr.str();
	cell->type = celltype;
	current_module->cells[cell->name] = cell;

	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	wire->name = cell->name + "_Y";
	wire->width = width;
	current_module->wires[wire->name] = wire;

	RTLIL::SigChunk chunk;
	chunk.wire = wire;
	chunk.width = wire->width;
	chunk.offset = 0;

	RTLIL::SigSpec new_sig;
	new_sig.chunks.push_back(chunk);
	new_sig.width = chunk.width;

	if (that != NULL)
		for (auto &attr : that->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), that->filename.c_str(), that->linenum);
			cell->attributes[attr.first] = attr.second->asAttrConst();
		}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(is_signed);
	cell->parameters["\\A_WIDTH"] = RTLIL::Const(sig.width);
	cell->connections["\\A"] = sig;

	cell->parameters["\\Y_WIDTH"] = width;
	cell->connections["\\Y"] = new_sig;
	sig = new_sig;
}

// helper function for creating RTLIL code for binary operations
static RTLIL::SigSpec binop2rtlil(AstNode *that, std::string type, int result_width, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	std::stringstream sstr;
	sstr << type << "$" << that->filename << ":" << that->linenum << "$" << (RTLIL::autoidx++);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	cell->name = sstr.str();
	cell->type = type;
	current_module->cells[cell->name] = cell;

	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	wire->name = cell->name + "_Y";
	wire->width = result_width;
	current_module->wires[wire->name] = wire;

	RTLIL::SigChunk chunk;
	chunk.wire = wire;
	chunk.width = wire->width;
	chunk.offset = 0;

	RTLIL::SigSpec sig;
	sig.chunks.push_back(chunk);
	sig.width = chunk.width;

	for (auto &attr : that->attributes) {
		if (attr.second->type != AST_CONSTANT)
			log_error("Attribute `%s' with non-constant value at %s:%d!\n",
					attr.first.c_str(), that->filename.c_str(), that->linenum);
		cell->attributes[attr.first] = attr.second->asAttrConst();
	}

	cell->parameters["\\A_SIGNED"] = RTLIL::Const(that->children[0]->is_signed);
	cell->parameters["\\B_SIGNED"] = RTLIL::Const(that->children[1]->is_signed);

	cell->parameters["\\A_WIDTH"] = RTLIL::Const(left.width);
	cell->parameters["\\B_WIDTH"] = RTLIL::Const(right.width);

	cell->connections["\\A"] = left;
	cell->connections["\\B"] = right;

	cell->parameters["\\Y_WIDTH"] = result_width;
	cell->connections["\\Y"] = sig;
	return sig;
}

// helper function for creating RTLIL code for multiplexers
static RTLIL::SigSpec mux2rtlil(AstNode *that, const RTLIL::SigSpec &cond, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	assert(cond.width == 1);

	std::stringstream sstr;
	sstr << "$ternary$" << that->filename << ":" << that->linenum << "$" << (RTLIL::autoidx++);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	cell->name = sstr.str();
	cell->type = "$mux";
	current_module->cells[cell->name] = cell;

	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->attributes["\\src"] = stringf("%s:%d", that->filename.c_str(), that->linenum);
	wire->name = cell->name + "_Y";
	wire->width = left.width;
	current_module->wires[wire->name] = wire;

	RTLIL::SigChunk chunk;
	chunk.wire = wire;
	chunk.width = wire->width;
	chunk.offset = 0;

	RTLIL::SigSpec sig;
	sig.chunks.push_back(chunk);
	sig.width = chunk.width;

	for (auto &attr : that->attributes) {
		if (attr.second->type != AST_CONSTANT)
			log_error("Attribute `%s' with non-constant value at %s:%d!\n",
					attr.first.c_str(), that->filename.c_str(), that->linenum);
		cell->attributes[attr.first] = attr.second->asAttrConst();
	}

	cell->parameters["\\WIDTH"] = RTLIL::Const(left.width);

	cell->connections["\\A"] = right;
	cell->connections["\\B"] = left;
	cell->connections["\\S"] = cond;
	cell->connections["\\Y"] = sig;

	return sig;
}

// helper class for converting AST always nodes to RTLIL processes
struct AST_INTERNAL::ProcessGenerator
{
	// input and output structures
	AstNode *always;
	RTLIL::SigSpec initSyncSignals;
	RTLIL::Process *proc;
	const RTLIL::SigSpec &outputSignals;

	// This always points to the RTLIL::CaseRule beeing filled at the moment
	RTLIL::CaseRule *current_case;

	// This two variables contain the replacement pattern to be used in the right hand side
	// of an assignment. E.g. in the code "foo = bar; foo = func(foo);" the foo in the right
	// hand side of the 2nd assignment needs to be replace with the temporary signal holding
	// the value assigned in the first assignment. So when the first assignement is processed
	// the according information is appended to subst_rvalue_from and subst_rvalue_to.
	RTLIL::SigSpec subst_rvalue_from, subst_rvalue_to;

	// This two variables contain the replacement pattern to be used in the left hand side
	// of an assignment. E.g. in the code "always @(posedge clk) foo <= bar" the signal bar
	// should not be connected to the signal foo. Instead it must be connected to the temporary
	// signal that is used as input for the register that drives the signal foo.
	RTLIL::SigSpec subst_lvalue_from, subst_lvalue_to;

	// The code here generates a number of temprorary signal for each output register. This
	// map helps generating nice numbered names for all this temporary signals.
	std::map<RTLIL::Wire*, int> new_temp_count;

	// Buffer for generating the init action
	RTLIL::SigSpec init_lvalue, init_rvalue;

	ProcessGenerator(AstNode *always, RTLIL::SigSpec initSyncSignalsArg = RTLIL::SigSpec()) : always(always), initSyncSignals(initSyncSignalsArg), outputSignals(subst_lvalue_from)
	{
		// generate process and simple root case
		proc = new RTLIL::Process;
		proc->attributes["\\src"] = stringf("%s:%d", always->filename.c_str(), always->linenum);
		proc->name = stringf("$proc$%s:%d$%d", always->filename.c_str(), always->linenum, RTLIL::autoidx++);
		for (auto &attr : always->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), always->filename.c_str(), always->linenum);
			proc->attributes[attr.first] = attr.second->asAttrConst();
		}
		current_module->processes[proc->name] = proc;
		current_case = &proc->root_case;

		// create initial temporary signal for all output registers
		collect_lvalues(subst_lvalue_from, always, true, true);
		subst_lvalue_to = new_temp_signal(subst_lvalue_from);

		bool found_anyedge_syncs = false;
		for (auto child : always->children)
			if (child->type == AST_EDGE)
				found_anyedge_syncs = true;

		if (found_anyedge_syncs) {
			log("Note: Assuming pure combinatorial block at %s:%d in\n", always->filename.c_str(), always->linenum);
			log("compliance with IEC 62142(E):2005 / IEEE Std. 1364.1(E):2002. Recommending\n");
			log("use of @* instead of @(...) for better match of synthesis and simulation.\n");
		}

		// create syncs for the process
		bool found_clocked_sync = false;
		for (auto child : always->children)
			if (child->type == AST_POSEDGE || child->type == AST_NEGEDGE) {
				found_clocked_sync = true;
				if (found_anyedge_syncs)
					log_error("Found non-synthesizable event list at %s:%d!\n", always->filename.c_str(), always->linenum);
				RTLIL::SyncRule *syncrule = new RTLIL::SyncRule;
				syncrule->type = child->type == AST_POSEDGE ? RTLIL::STp : RTLIL::STn;
				syncrule->signal = child->children[0]->genRTLIL();
				addChunkActions(syncrule->actions, subst_lvalue_from, subst_lvalue_to, true);
				proc->syncs.push_back(syncrule);
			}
		if (proc->syncs.empty()) {
			RTLIL::SyncRule *syncrule = new RTLIL::SyncRule;
			syncrule->type = RTLIL::STa;
			syncrule->signal = RTLIL::SigSpec();
			addChunkActions(syncrule->actions, subst_lvalue_from, subst_lvalue_to, true);
			proc->syncs.push_back(syncrule);
		}

		// create initial assignments for the temporary signals
		if ((flag_nolatches || always->get_bool_attribute("\\nolatches") || current_module->get_bool_attribute("\\nolatches")) && !found_clocked_sync) {
			subst_rvalue_from = subst_lvalue_from;
			subst_rvalue_to = RTLIL::SigSpec(RTLIL::State::Sx, subst_rvalue_from.width);
		} else {
			addChunkActions(current_case->actions, subst_lvalue_to, subst_lvalue_from);
		}

		// process the AST
		for (auto child : always->children)
			if (child->type == AST_BLOCK)
				processAst(child);

		if (initSyncSignals.width > 0)
		{
			RTLIL::SyncRule *sync = new RTLIL::SyncRule;
			sync->type = RTLIL::SyncType::STi;
			proc->syncs.push_back(sync);

			assert(init_lvalue.width == init_rvalue.width);
			init_lvalue.optimize();
			init_rvalue.optimize();

			int offset = 0;
			for (size_t i = 0; i < init_lvalue.chunks.size(); i++) {
				RTLIL::SigSpec lhs = init_lvalue.chunks[i];
				RTLIL::SigSpec rhs = init_rvalue.extract(offset, init_lvalue.chunks[i].width);
				sync->actions.push_back(RTLIL::SigSig(lhs, rhs));
				offset += lhs.width;
			}
		}
	}

	// create new temporary signals
	RTLIL::SigSpec new_temp_signal(RTLIL::SigSpec sig)
	{
		sig.optimize();
		for (size_t i = 0; i < sig.chunks.size(); i++)
		{
			RTLIL::SigChunk &chunk = sig.chunks[i];
			if (chunk.wire == NULL)
				continue;

			RTLIL::Wire *wire = new RTLIL::Wire;
			wire->attributes["\\src"] = stringf("%s:%d", always->filename.c_str(), always->linenum);
			do {
				wire->name = stringf("$%d%s[%d:%d]", new_temp_count[chunk.wire]++,
						chunk.wire->name.c_str(), chunk.width+chunk.offset-1, chunk.offset);;
				if (chunk.wire->name.find('$') != std::string::npos)
					wire->name += stringf("$%d", RTLIL::autoidx++);
			} while (current_module->wires.count(wire->name) > 0);
			wire->width = chunk.width;
			current_module->wires[wire->name] = wire;

			chunk.wire = wire;
			chunk.offset = 0;
		}
		return sig;
	}

	// recursively traverse the AST an collect all assigned signals
	void collect_lvalues(RTLIL::SigSpec &reg, AstNode *ast, bool type_eq, bool type_le, bool run_sort_and_unify = true)
	{
		switch (ast->type)
		{
		case AST_CASE:
			for (auto child : ast->children)
				if (child != ast->children[0]) {
					assert(child->type == AST_COND);
					collect_lvalues(reg, child, type_eq, type_le, false);
				}
			break;

		case AST_COND:
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
			assert(0);
		}

		if (run_sort_and_unify)
			reg.sort_and_unify();
	}

	// remove all assignments to the given signal pattern in a case and all its children.
	// e.g. when the last statement in the code "a = 23; if (b) a = 42; a = 0;" is processed this
	// function is called to clean up the first two assignments as they are overwritten by
	// the third assignment.
	void removeSignalFromCaseTree(RTLIL::SigSpec pattern, RTLIL::CaseRule *cs)
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
		if (inSyncRule && initSyncSignals.width > 0) {
			init_lvalue.append(lvalue.extract(initSyncSignals));
			init_rvalue.append(lvalue.extract(initSyncSignals, &rvalue));
			lvalue.remove2(initSyncSignals, &rvalue);
		}
		assert(lvalue.width == rvalue.width);
		lvalue.optimize();
		rvalue.optimize();

		int offset = 0;
		for (size_t i = 0; i < lvalue.chunks.size(); i++) {
			RTLIL::SigSpec lhs = lvalue.chunks[i];
			RTLIL::SigSpec rhs = rvalue.extract(offset, lvalue.chunks[i].width);
			if (inSyncRule && lvalue.chunks[i].wire && lvalue.chunks[i].wire->get_bool_attribute("\\nosync"))
				rhs = RTLIL::SigSpec(RTLIL::State::Sx, rhs.width);
			actions.push_back(RTLIL::SigSig(lhs, rhs));
			offset += lhs.width;
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
				RTLIL::SigSpec rvalue = ast->children[1]->genWidthRTLIL(lvalue.width, &subst_rvalue_from, &subst_rvalue_to);
				lvalue.replace(subst_lvalue_from, subst_lvalue_to);

				if (ast->type == AST_ASSIGN_EQ) {
					subst_rvalue_from.remove2(unmapped_lvalue, &subst_rvalue_to);
					subst_rvalue_from.append(unmapped_lvalue);
					subst_rvalue_from.optimize();
					subst_rvalue_to.append(rvalue);
					subst_rvalue_to.optimize();
				}

				removeSignalFromCaseTree(lvalue, current_case);
				current_case->actions.push_back(RTLIL::SigSig(lvalue, rvalue));
			}
			break;

		case AST_CASE:
			{
				RTLIL::SwitchRule *sw = new RTLIL::SwitchRule;
				sw->signal = ast->children[0]->genWidthRTLIL(-1, &subst_rvalue_from, &subst_rvalue_to);
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
				this_case_eq_rvalue.replace(subst_rvalue_from, subst_rvalue_to);

				RTLIL::SigSpec backup_subst_lvalue_from = subst_lvalue_from;
				RTLIL::SigSpec backup_subst_lvalue_to = subst_lvalue_to;

				RTLIL::SigSpec backup_subst_rvalue_from = subst_rvalue_from;
				RTLIL::SigSpec backup_subst_rvalue_to = subst_rvalue_to;

				RTLIL::CaseRule *default_case = NULL;
				RTLIL::CaseRule *last_generated_case = NULL;
				for (auto child : ast->children)
				{
					if (child == ast->children[0])
						continue;
					assert(child->type == AST_COND);

					subst_lvalue_from = backup_subst_lvalue_from;
					subst_lvalue_to = backup_subst_lvalue_to;

					subst_rvalue_from = backup_subst_rvalue_from;
					subst_rvalue_to = backup_subst_rvalue_to;

					subst_lvalue_from.remove2(this_case_eq_lvalue, &subst_lvalue_to);
					subst_lvalue_from.append(this_case_eq_lvalue);
					subst_lvalue_from.optimize();
					subst_lvalue_to.append(this_case_eq_ltemp);
					subst_lvalue_to.optimize();

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
							current_case->compare.push_back(node->genWidthRTLIL(sw->signal.width, &subst_rvalue_from, &subst_rvalue_to));
					}
					if (default_case != current_case)
						sw->cases.push_back(current_case);
					else
						log_assert(current_case->compare.size() == 0);
					current_case = backup_case;
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

				subst_lvalue_from = backup_subst_lvalue_from;
				subst_lvalue_to = backup_subst_lvalue_to;

				subst_rvalue_from = backup_subst_rvalue_from;
				subst_rvalue_to = backup_subst_rvalue_to;

				subst_rvalue_from.remove2(this_case_eq_lvalue, &subst_rvalue_to);
				subst_rvalue_from.append(this_case_eq_lvalue);
				subst_rvalue_from.optimize();
				subst_rvalue_to.append(this_case_eq_ltemp);
				subst_rvalue_to.optimize();

				this_case_eq_lvalue.replace(subst_lvalue_from, subst_lvalue_to);
				removeSignalFromCaseTree(this_case_eq_lvalue, current_case);
				addChunkActions(current_case->actions, this_case_eq_lvalue, this_case_eq_ltemp);
			}
			break;

		case AST_WIRE:
			log_error("Found wire declaration in block without label at at %s:%d!\n", ast->filename.c_str(), ast->linenum);
			break;

		case AST_TCALL:
		case AST_FOR:
			break;

		default:
			log_abort();
		}
	}
};

// detect sign and width of an expression
void AstNode::detectSignWidthWorker(int &width_hint, bool &sign_hint)
{
	std::string type_name;
	bool sub_sign_hint = true;
	int sub_width_hint = -1;
	int this_width = 0;
	AstNode *range = NULL;
	AstNode *id_ast = NULL;

	switch (type)
	{
	case AST_CONSTANT:
		width_hint = std::max(width_hint, int(bits.size()));
		if (!is_signed)
			sign_hint = false;
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
			if (id_ast->children[0]->type == AST_CONSTANT) {
				this_width = id_ast->children[0]->bits.size();
			} else
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
					log_error("Failed to detect with of signal access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
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
				log_error("Failed to detect with of memory access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
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
		} else
			width_hint = std::max(width_hint, this_width);
		if (!id_ast->is_signed)
			sign_hint = false;
		break;

	case AST_TO_BITS:
		while (children[0]->simplify(true, false, false, 1, -1, false, false) == true) { }
		if (children[0]->type != AST_CONSTANT)
			log_error("Left operand of tobits expression is not constant at %s:%d!\n", filename.c_str(), linenum);
		children[1]->detectSignWidthWorker(sub_width_hint, sign_hint);
		width_hint = std::max(width_hint, children[0]->bitsAsConst().as_int());
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
		width_hint = std::max(width_hint, this_width);
		sign_hint = false;
		break;

	case AST_REPLICATE:
		while (children[0]->simplify(true, false, false, 1, -1, false, true) == true) { }
		if (children[0]->type != AST_CONSTANT)
			log_error("Left operand of replicate expression is not constant at %s:%d!\n", filename.c_str(), linenum);
		children[1]->detectSignWidthWorker(sub_width_hint, sub_sign_hint);
		width_hint = std::max(width_hint, children[0]->bitsAsConst().as_int() * sub_width_hint);
		sign_hint = false;
		break;

	case AST_NEG:
	case AST_BIT_NOT:
	case AST_POS:
		children[0]->detectSignWidthWorker(width_hint, sign_hint);
		break;

	case AST_BIT_AND:
	case AST_BIT_OR:
	case AST_BIT_XOR:
	case AST_BIT_XNOR:
		for (auto child : children)
			child->detectSignWidthWorker(width_hint, sign_hint);
		break;

	case AST_REDUCE_AND:
	case AST_REDUCE_OR:
	case AST_REDUCE_XOR:
	case AST_REDUCE_XNOR:
	case AST_REDUCE_BOOL:
		width_hint = std::max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_SHIFT_LEFT:
	case AST_SHIFT_RIGHT:
	case AST_SHIFT_SLEFT:
	case AST_SHIFT_SRIGHT:
	case AST_POW:
		children[0]->detectSignWidthWorker(width_hint, sign_hint);
		break;

	case AST_LT:
	case AST_LE:
	case AST_EQ:
	case AST_NE:
	case AST_EQX:
	case AST_NEX:
	case AST_GE:
	case AST_GT:
		width_hint = std::max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_ADD:
	case AST_SUB:
	case AST_MUL:
	case AST_DIV:
	case AST_MOD:
		for (auto child : children)
			child->detectSignWidthWorker(width_hint, sign_hint);
		break;

	case AST_LOGIC_AND:
	case AST_LOGIC_OR:
	case AST_LOGIC_NOT:
		width_hint = std::max(width_hint, 1);
		sign_hint = false;
		break;

	case AST_TERNARY:
		children.at(1)->detectSignWidthWorker(width_hint, sign_hint);
		children.at(2)->detectSignWidthWorker(width_hint, sign_hint);
		break;

	case AST_MEMRD:
		if (!id2ast->is_signed)
			sign_hint = false;
		if (!id2ast->children[0]->range_valid)
			log_error("Failed to detect with of memory access `%s' at %s:%d!\n", str.c_str(), filename.c_str(), linenum);
		this_width = id2ast->children[0]->range_left - id2ast->children[0]->range_right + 1;
		width_hint = std::max(width_hint, this_width);
		break;

	// everything should have been handled above -> print error if not.
	default:
		for (auto f : log_files)
			current_ast->dumpAst(f, "verilog-ast> ");
		log_error("Don't know how to detect sign and width for %s node at %s:%d!\n",
				type2str(type).c_str(), filename.c_str(), linenum);
	}
}

// detect sign and width of an expression
void AstNode::detectSignWidth(int &width_hint, bool &sign_hint)
{
	width_hint = -1, sign_hint = true;
	detectSignWidthWorker(width_hint, sign_hint);
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
	// be instanciated for this type of AST node.
	std::string type_name;

	current_filename = filename;
	set_line_num(linenum);

	switch (type)
	{
	// simply ignore this nodes.
	// they are eighter leftovers from simplify() or are referenced by other nodes
	// and are only accessed here thru this references
	case AST_TASK:
	case AST_FUNCTION:
	case AST_AUTOWIRE:
	case AST_LOCALPARAM:
	case AST_DEFPARAM:
	case AST_GENVAR:
	case AST_GENFOR:
	case AST_GENBLOCK:
	case AST_GENIF:
	case AST_GENCASE:
		break;

	// remember the parameter, needed for example in techmap
	case AST_PARAMETER:
		current_module->avail_parameters.insert(str);
		break;

	// create an RTLIL::Wire for an AST_WIRE node
	case AST_WIRE: {
			if (current_module->wires.count(str) != 0)
				log_error("Re-definition of signal `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);
			if (!range_valid)
				log_error("Signal `%s' with non-constant width at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			if (range_left < range_right && (range_left != -1 || range_right != 0)) {
				int tmp = range_left;
				range_left = range_right;
				range_right = tmp;
			}

			RTLIL::Wire *wire = new RTLIL::Wire;
			wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			wire->name = str;
			wire->width = range_left - range_right + 1;
			wire->start_offset = range_right;
			wire->port_id = port_id;
			wire->port_input = is_input;
			wire->port_output = is_output;
			current_module->wires[wire->name] = wire;

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

			assert(children.size() >= 2);
			assert(children[0]->type == AST_RANGE);
			assert(children[1]->type == AST_RANGE);

			if (!children[0]->range_valid || !children[1]->range_valid)
				log_error("Memory `%s' with non-constant width or size at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			RTLIL::Memory *memory = new RTLIL::Memory;
			memory->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			memory->name = str;
			memory->width = children[0]->range_left - children[0]->range_right + 1;
			memory->start_offset = children[0]->range_right;
			memory->size = children[1]->range_left - children[1]->range_right;
			current_module->memories[memory->name] = memory;

			if (memory->size < 0)
				memory->size *= -1;
			memory->size += std::min(children[1]->range_left, children[1]->range_right) + 1;

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

	// simply return the corresponding RTLIL::SigSpec for an AST_IDENTIFIER node
	// for identifiers with dynamic bit ranges (e.g. "foo[bar]" or "foo[bar+3:bar]") a
	// shifter cell is created and the output signal of this cell is returned
	case AST_IDENTIFIER:
		{
			RTLIL::Wire *wire = NULL;
			RTLIL::SigChunk chunk;

			if (id2ast && id2ast->type == AST_AUTOWIRE && current_module->wires.count(str) == 0) {
				RTLIL::Wire *wire = new RTLIL::Wire;
				wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
				wire->name = str;
				if (flag_autowire)
					log("Warning: Identifier `%s' is implicitly declared at %s:%d.\n", str.c_str(), filename.c_str(), linenum);
				else
					log_error("Identifier `%s' is implicitly declared at %s:%d and `default_nettype is set to none.\n", str.c_str(), filename.c_str(), linenum);
				current_module->wires[str] = wire;
			}
			else if (id2ast->type == AST_PARAMETER || id2ast->type == AST_LOCALPARAM) {
				if (id2ast->children[0]->type != AST_CONSTANT)
					log_error("Parameter %s does not evaluate to constant value at %s:%d!\n",
							str.c_str(), filename.c_str(), linenum);
				chunk = RTLIL::Const(id2ast->children[0]->bits);
				goto use_const_chunk;
			}
			else if (!id2ast || (id2ast->type != AST_WIRE && id2ast->type != AST_AUTOWIRE &&
					id2ast->type != AST_MEMORY) || current_module->wires.count(str) == 0)
				log_error("Identifier `%s' doesn't map to any signal at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			if (id2ast->type == AST_MEMORY)
				log_error("Identifier `%s' does map to an unexpanded memory at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			wire = current_module->wires[str];
			chunk.wire = wire;
			chunk.width = wire->width;
			chunk.offset = 0;

		use_const_chunk:
			if (children.size() != 0) {
				assert(children[0]->type == AST_RANGE);
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
					RTLIL::SigSpec sig = binop2rtlil(fake_ast, "$shr", width,
							fake_ast->children[0]->genRTLIL(), fake_ast->children[1]->genRTLIL());
					delete left_at_zero_ast;
					delete right_at_zero_ast;
					delete fake_ast;
					return sig;
				} else {
					chunk.offset = children[0]->range_right - id2ast->range_right;
					chunk.width = children[0]->range_left - children[0]->range_right + 1;
					if (children[0]->range_left > id2ast->range_left || id2ast->range_right > children[0]->range_right)
						log_error("Range select out of bounds on signal `%s' at %s:%d!\n",
								str.c_str(), filename.c_str(), linenum);
				}
			}

			RTLIL::SigSpec sig;
			sig.chunks.push_back(chunk);
			sig.width = chunk.width;

			if (genRTLIL_subst_from && genRTLIL_subst_to)
				sig.replace(*genRTLIL_subst_from, *genRTLIL_subst_to);

			is_signed = children.size() > 0 ? false : id2ast->is_signed && sign_hint;
			return sig;
		}

	// just pass thru the signal. the parent will evaluate the is_signed property and interpret the SigSpec accordingly
	case AST_TO_SIGNED:
	case AST_TO_UNSIGNED: {
			RTLIL::SigSpec sig = children[0]->genRTLIL();
			if (sig.width < width_hint)
				sig.extend_u0(width_hint, sign_hint);
			is_signed = sign_hint;
			return sig;
	}

	// concatenation of signals can be done directly using RTLIL::SigSpec
	case AST_CONCAT: {
			RTLIL::SigSpec sig;
			sig.width = 0;
			for (auto it = children.begin(); it != children.end(); it++) {
				RTLIL::SigSpec s = (*it)->genRTLIL();
				for (size_t i = 0; i < s.chunks.size(); i++) {
					sig.chunks.push_back(s.chunks[i]);
					sig.width += s.chunks[i].width;
				}
			}
			if (sig.width < width_hint)
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
			if (sig.width < width_hint)
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
			int width = arg.width;
			if (width_hint > 0) {
				width = width_hint;
				widthExtend(this, arg, width, is_signed, "$pos");
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
			int width = std::max(left.width, right.width);
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
			RTLIL::SigSpec sig = uniop2rtlil(this, type_name, std::max(width_hint, 1), arg);
			return sig;
		}

	// generate cells for unary operations: $reduce_bool
	// (this is actually just an $reduce_or, but for clearity a different cell type is used)
	if (0) { case AST_REDUCE_BOOL:  type_name = "$reduce_bool"; }
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL();
			RTLIL::SigSpec sig = arg.width > 1 ? uniop2rtlil(this, type_name, std::max(width_hint, 1), arg) : arg;
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
			int width = width_hint > 0 ? width_hint : left.width;
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
			int width = width_hint > 0 ? width_hint : left.width;
			is_signed = children[0]->is_signed;
			if (!flag_noopt && left.is_fully_const() && left.as_int() == 2 && !right_signed)
				return binop2rtlil(this, "$shl", width, RTLIL::SigSpec(1, left.width), right);
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
			int width = std::max(width_hint, 1);
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
			int width = std::max(left.width, right.width);
			if (width > width_hint && width_hint > 0)
				width = width_hint;
			if (width < width_hint) {
				if (type == AST_ADD || type == AST_SUB || type == AST_DIV)
					width++;
				if (type == AST_SUB && (!children[0]->is_signed || !children[1]->is_signed))
					width = width_hint;
				if (type == AST_MUL)
					width = std::min(left.width + right.width, width_hint);
			}
		#else
			int width = std::max(std::max(left.width, right.width), width_hint);
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
			return binop2rtlil(this, type_name, std::max(width_hint, 1), left, right);
		}

	// generate cells for unary operations: $logic_not
	case AST_LOGIC_NOT:
		{
			RTLIL::SigSpec arg = children[0]->genRTLIL();
			return uniop2rtlil(this, "$logic_not", std::max(width_hint, 1), arg);
		}

	// generate multiplexer for ternary operator (aka ?:-operator)
	case AST_TERNARY:
		{
			if (width_hint < 0)
				detectSignWidth(width_hint, sign_hint);

			RTLIL::SigSpec cond = children[0]->genRTLIL();
			RTLIL::SigSpec val1 = children[1]->genRTLIL(width_hint, sign_hint);
			RTLIL::SigSpec val2 = children[2]->genRTLIL(width_hint, sign_hint);

			if (cond.width > 1)
				cond = uniop2rtlil(this, "$reduce_bool", 1, cond, false);

			int width = std::max(val1.width, val2.width);
			is_signed = children[1]->is_signed && children[2]->is_signed;
			widthExtend(this, val1, width, is_signed, "$bu0");
			widthExtend(this, val2, width, is_signed, "$bu0");

			RTLIL::SigSpec sig = mux2rtlil(this, cond, val1, val2);

			if (sig.width < width_hint)
				sig.extend_u0(width_hint, sign_hint);
			return sig;
		}

	// generate $memrd cells for memory read ports
	case AST_MEMRD:
		{
			std::stringstream sstr;
			sstr << "$memrd$" << str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);

			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			cell->name = sstr.str();
			cell->type = "$memrd";
			current_module->cells[cell->name] = cell;

			RTLIL::Wire *wire = new RTLIL::Wire;
			wire->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			wire->name = cell->name + "_DATA";
			wire->width = current_module->memories[str]->width;
			current_module->wires[wire->name] = wire;

			int addr_bits = 1;
			while ((1 << addr_bits) < current_module->memories[str]->size)
				addr_bits++;

			cell->connections["\\CLK"] = RTLIL::SigSpec(RTLIL::State::Sx, 1);
			cell->connections["\\ADDR"] = children[0]->genWidthRTLIL(addr_bits);
			cell->connections["\\DATA"] = RTLIL::SigSpec(wire);

			cell->parameters["\\MEMID"] = RTLIL::Const(str);
			cell->parameters["\\ABITS"] = RTLIL::Const(addr_bits);
			cell->parameters["\\WIDTH"] = RTLIL::Const(wire->width);

			cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(0);
			cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(0);
			cell->parameters["\\TRANSPARENT"] = RTLIL::Const(0);

			return RTLIL::SigSpec(wire);
		}

	// generate $memwr cells for memory write ports
	case AST_MEMWR:
		{
			std::stringstream sstr;
			sstr << "$memwr$" << str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);

			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			cell->name = sstr.str();
			cell->type = "$memwr";
			current_module->cells[cell->name] = cell;

			int addr_bits = 1;
			while ((1 << addr_bits) < current_module->memories[str]->size)
				addr_bits++;

			cell->connections["\\CLK"] = RTLIL::SigSpec(RTLIL::State::Sx, 1);
			cell->connections["\\ADDR"] = children[0]->genWidthRTLIL(addr_bits);
			cell->connections["\\DATA"] = children[1]->genWidthRTLIL(current_module->memories[str]->width);
			cell->connections["\\EN"] = children[2]->genRTLIL();

			if (cell->connections["\\EN"].width > 1)
				cell->connections["\\EN"] = uniop2rtlil(this, "$reduce_bool", 1, cell->connections["\\EN"], false);

			cell->parameters["\\MEMID"] = RTLIL::Const(str);
			cell->parameters["\\ABITS"] = RTLIL::Const(addr_bits);
			cell->parameters["\\WIDTH"] = RTLIL::Const(current_module->memories[str]->width);

			cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(0);
			cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(0);

			cell->parameters["\\PRIORITY"] = RTLIL::Const(RTLIL::autoidx-1);
		}
		break;

	// generate $assert cells
	case AST_ASSERT:
		{
			log_assert(children.size() == 2);

			RTLIL::SigSpec check = children[0]->genRTLIL();
			log_assert(check.width == 1);

			RTLIL::SigSpec en = children[1]->genRTLIL();
			log_assert(en.width == 1);

			std::stringstream sstr;
			sstr << "$assert$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);

			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			cell->name = sstr.str();
			cell->type = "$assert";
			current_module->cells[cell->name] = cell;

			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				cell->attributes[attr.first] = attr.second->asAttrConst();
			}

			cell->connections["\\A"] = check;
			cell->connections["\\EN"] = en;
		}
		break;

	// add entries to current_module->connections for assignments (outside of always blocks)
	case AST_ASSIGN:
		{
			if (children[0]->type == AST_IDENTIFIER && children[0]->id2ast && children[0]->id2ast->type == AST_AUTOWIRE) {
				RTLIL::SigSpec right = children[1]->genRTLIL();
				RTLIL::SigSpec left = children[0]->genWidthRTLIL(right.width);
				current_module->connections.push_back(RTLIL::SigSig(left, right));
			} else {
				RTLIL::SigSpec left = children[0]->genRTLIL();
				RTLIL::SigSpec right = children[1]->genWidthRTLIL(left.width);
				current_module->connections.push_back(RTLIL::SigSig(left, right));
			}
		}
		break;

	// create an RTLIL::Cell for an AST_CELL
	case AST_CELL:
		{
			int port_counter = 0, para_counter = 0;
			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->attributes["\\src"] = stringf("%s:%d", filename.c_str(), linenum);
			cell->name = str;
			for (auto it = children.begin(); it != children.end(); it++) {
				AstNode *child = *it;
				if (child->type == AST_CELLTYPE) {
					cell->type = child->str;
					if (flag_icells && cell->type.substr(0, 2) == "\\$")
						cell->type = cell->type.substr(1);
					continue;
				}
				if (child->type == AST_PARASET) {
					if (child->children[0]->type != AST_CONSTANT)
						log_error("Parameter `%s' with non-constant value at %s:%d!\n",
								child->str.c_str(), filename.c_str(), linenum);
					if (child->str.size() == 0) {
						char buf[100];
						snprintf(buf, 100, "$%d", ++para_counter);
						cell->parameters[buf] = child->children[0]->asParaConst();
					} else {
						cell->parameters[child->str] = child->children[0]->asParaConst();
					}
					continue;
				}
				if (child->type == AST_ARGUMENT) {
					RTLIL::SigSpec sig;
					if (child->children.size() > 0)
						sig = child->children[0]->genRTLIL();
					if (child->str.size() == 0) {
						char buf[100];
						snprintf(buf, 100, "$%d", ++port_counter);
						cell->connections[buf] = sig;
					} else {
						cell->connections[child->str] = sig;
					}
					continue;
				}
				assert(0);
			}
			for (auto &attr : attributes) {
				if (attr.second->type != AST_CONSTANT)
					log_error("Attribute `%s' with non-constant value at %s:%d!\n",
							attr.first.c_str(), filename.c_str(), linenum);
				cell->attributes[attr.first] = attr.second->asAttrConst();
			}
			if (current_module->cells.count(cell->name) != 0)
				log_error("Re-definition of cell `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);
			current_module->cells[str] = cell;
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
// signals must be substituted before beeing used as input values (used by ProcessGenerator)
// note that this is using some global variables to communicate this special settings to AstNode::genRTLIL().
RTLIL::SigSpec AstNode::genWidthRTLIL(int width, RTLIL::SigSpec *subst_from,  RTLIL::SigSpec *subst_to)
{
	RTLIL::SigSpec *backup_subst_from = genRTLIL_subst_from;
	RTLIL::SigSpec *backup_subst_to = genRTLIL_subst_to;

	if (subst_from)
		genRTLIL_subst_from = subst_from;
	if (subst_to)
		genRTLIL_subst_to = subst_to;

	bool sign_hint = true;
	int width_hint = width;
	detectSignWidthWorker(width_hint, sign_hint);
	RTLIL::SigSpec sig = genRTLIL(width_hint, sign_hint);

	genRTLIL_subst_from = backup_subst_from;
	genRTLIL_subst_to = backup_subst_to;

	if (width >= 0)
		sig.extend_u0(width, is_signed);

	return sig;
}

