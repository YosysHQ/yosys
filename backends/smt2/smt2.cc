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
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Smt2Worker
{
	CellTypes ct;
	SigMap sigmap;
	RTLIL::Module *module;
	bool bvmode;
	int idcounter;

	std::vector<std::string> decls, trans;
	std::map<RTLIL::SigBit, RTLIL::Cell*> bit_driver;
	std::set<RTLIL::Cell*> exported_cells;

	std::map<RTLIL::SigBit, std::pair<int, int>> fcache;
	std::map<int, int> bvsizes;

	Smt2Worker(RTLIL::Module *module, bool bvmode) : ct(module->design), sigmap(module), module(module), bvmode(bvmode), idcounter(0)
	{
		decls.push_back(stringf("(declare-sort |%s_s| 0)\n", log_id(module)));

		for (auto cell : module->cells())
		for (auto &conn : cell->connections()) {
			bool is_input = ct.cell_input(cell->type, conn.first);
			bool is_output = ct.cell_output(cell->type, conn.first);
			if (is_output && !is_input)
				for (auto bit : sigmap(conn.second)) {
					if (bit_driver.count(bit))
						log_error("Found multiple drivers for %s.\n", log_signal(bit));
					bit_driver[bit] = cell;
				}
			else if (is_output || !is_input)
				log_error("Unsupported or unknown directionality on port %s of cell %s.%s (%s).\n",
						log_id(conn.first), log_id(module), log_id(cell), log_id(cell->type));
		}
	}

	void register_bool(RTLIL::SigBit bit, int id)
	{
		sigmap.apply(bit);
		log_assert(fcache.count(bit) == 0);
		fcache[bit] = std::pair<int, int>(id, -1);
	}

	std::string get_bool(RTLIL::SigBit bit, const char *state_name = "state")
	{
		sigmap.apply(bit);

		if (bit_driver.count(bit))
			export_cell(bit_driver.at(bit));

		if (fcache.count(bit) == 0) {
			decls.push_back(stringf("(declare-fun |%s#%d| (|%s_s|) Bool) ; %s\n",
					log_id(module), idcounter, log_id(module), log_signal(bit)));
			register_bool(bit, idcounter++);
		}

		auto f = fcache.at(bit);
		log_assert(f.second == -1);
		return stringf("(|%s#%d| %s)", log_id(module), f.first, state_name);
	}

	std::string get_bv(RTLIL::SigSpec sig, const char *state_name = "state")
	{
		std::vector<std::string> subexpr;

		for (auto bit : sig)
			subexpr.push_back(stringf("(ite %s #b1 #b0)", get_bool(bit, state_name).c_str()));

		if (GetSize(subexpr) > 1) {
			std::string expr = "(concat";
			for (int i = GetSize(subexpr)-1; i >= 0; i--)
				expr += " " + subexpr[i];
			return expr + ")";
		} else {
			log_assert(GetSize(subexpr) == 1);
			return subexpr[0];
		}
	}

	void export_gate(RTLIL::Cell *cell, std::string expr)
	{
		RTLIL::SigBit bit = sigmap(cell->getPort("\\Y")[0]);
		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bool(cell->getPort("\\A")[0]);
			else if (ch == 'B') processed_expr += get_bool(cell->getPort("\\B")[0]);
			else if (ch == 'C') processed_expr += get_bool(cell->getPort("\\C")[0]);
			else if (ch == 'D') processed_expr += get_bool(cell->getPort("\\D")[0]);
			else if (ch == 'S') processed_expr += get_bool(cell->getPort("\\S")[0]);
			else processed_expr += ch;
		}

		decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
				log_id(module), idcounter, log_id(module), processed_expr.c_str(), log_signal(bit)));
		register_bool(bit, idcounter++);
		return;
	}

	void export_cell(RTLIL::Cell *cell)
	{
		if (exported_cells.count(cell))
			return;
		exported_cells.insert(cell);

		if (cell->type == "$_DFF_P_" || cell->type == "$_DFF_N_")
		{
			std::string expr_d = get_bool(cell->getPort("\\D")[0]);
			std::string expr_q = get_bool(cell->getPort("\\Q")[0], "next_state");
			trans.push_back(stringf("  (= %s %s)\n", expr_d.c_str(), expr_q.c_str()));
			return;
		}

		if (cell->type == "$_BUF_") return export_gate(cell, "A");
		if (cell->type == "$_NOT_") return export_gate(cell, "(not A)");
		if (cell->type == "$_AND_") return export_gate(cell, "(and A B)");
		if (cell->type == "$_NAND_") return export_gate(cell, "(not (and A B))");
		if (cell->type == "$_OR_") return export_gate(cell, "(or A B)");
		if (cell->type == "$_NOR_") return export_gate(cell, "(not (or A B))");
		if (cell->type == "$_XOR_") return export_gate(cell, "(xor A B)");
		if (cell->type == "$_XNOR_") return export_gate(cell, "(not (xor A B))");
		if (cell->type == "$_MUX_") return export_gate(cell, "(ite S B A)");
		if (cell->type == "$_AOI3_") return export_gate(cell, "(not (or (and A B) C))");
		if (cell->type == "$_OAI3_") return export_gate(cell, "(not (and (or A B) C))");
		if (cell->type == "$_AOI4_") return export_gate(cell, "(not (or (and A B) (and C D)))");
		if (cell->type == "$_OAI4_") return export_gate(cell, "(not (and (or A B) (or C D)))");

		log_error("Unsupported cell type %s for cell %s.%s.\n",
				log_id(cell->type), log_id(module), log_id(cell));
	}

	void run()
	{
		for (auto wire : module->wires())
			if (wire->port_id || wire->get_bool_attribute("\\keep")) {
				RTLIL::SigSpec sig = sigmap(wire);
				if (bvmode && GetSize(sig) > 1) {
					decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) (_ BitVec %d) %s)\n",
							log_id(module), log_id(wire), log_id(module), GetSize(sig), get_bv(sig).c_str()));
				} else {
					for (int i = 0; i < GetSize(sig); i++)
						if (GetSize(sig) > 1)
							decls.push_back(stringf("(define-fun |%s_n %s %d| ((state |%s_s|)) Bool %s)\n",
									log_id(module), log_id(wire), i, log_id(module), get_bool(sig[i]).c_str()));
						else
							decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) Bool %s)\n",
									log_id(module), log_id(wire), log_id(module), get_bool(sig[i]).c_str()));
				}
			}
	}

	void write(std::ostream &f)
	{
		for (auto it : decls)
			f << it;
		f << stringf("(define-fun |%s_t| ((state |%s_s|)(next_state |%s_s|)) Bool (and\n", log_id(module), log_id(module), log_id(module));
		for (auto it : trans)
			f << it;
		f << "true true))\n";
	}
};

struct Smt2Backend : public Backend {
	Smt2Backend() : Backend("smt2", "write design to SMT-LIBv2 file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smt2 [options] [filename]\n");
		log("\n");
		log("Write a SMT-LIBv2 [1] description of the current design. For a module with name\n");
		log("'<mod>' this will declare the sort '<mod>_s' (state of the module) and the the\n");
		log("function '<mod>_t' (state transition function).\n");
		log("\n");
		log("The '<mod>_s' sort represents the a module state. Additional '<mod>_n' functions\n");
		log("are provided that can be used to access the values of all signals in the module.\n");
		log("Only ports, and signals with the 'keep' attribute set are made available via\n");
		log("such functions. Without the -bv option, multi-bit wires are exported as\n");
		log("separate functions of type Bool for the individual bits. With the -bv option\n");
		log("multi-bit wires are exported as single functions of type BitVec.\n");
		log("\n");
		log("The '<mod>_t' function evaluates to 'true' when the given pair of states\n");
		log("describes a valid state transition.\n");
		log("\n");
		log("    -bv\n");
		log("        enable support for BitVec (FixedSizeBitVectors theory). with this\n");
		log("        option set multi-bit wires are represented using the BitVec sort and\n");
		log("        support for coarse grain cells (incl. arithmetic) is enabled.\n");
		log("\n");
		log("    -tpl <template_file>\n");
		log("        use the given template file. the line containing only the token '%%%%'\n");
		log("        is replaced with the regular output of this command.\n");
		log("\n");
		log("[1] For more information on SMT-LIBv2 visit http://smt-lib.org/ or read David\n");
		log("R. Cok's tutorial: http://www.grammatech.com/resources/smt/SMTLIBTutorial.pdf\n");
		log("\n");
		log("---------------------------------------------------------------------------\n");
		log("\n");
		log("Example:\n");
		log("\n");
		log("Consider the following module (test.v). We want to prove that the output can\n");
		log("never transition from a non-zero value to a zero value.\n");
		log("\n");
		log("        module test(input clk, output reg [3:0] y);\n");
		log("          always @(posedge clk)\n");
		log("            y <= (y << 1) | ^y;\n");
		log("        endmodule\n");
		log("\n");
		log("For this proof we create the following template (test.tpl).\n");
		log("\n");
		log("        ; we need QF_UFBV for this poof\n");
		log("        (set-logic QF_UFBV)\n");
		log("\n");
		log("        ; insert the auto-generated code here\n");
		log("        %%%%\n");
		log("\n");
		log("        ; declare two state variables s1 and s2\n");
		log("        (declare-fun s1 () test_s)\n");
		log("        (declare-fun s2 () test_s)\n");
		log("\n");
		log("        ; state s2 is the successor of state s1\n");
		log("        (assert (test_t s1 s2))\n");
		log("\n");
		log("        ; we are looking for a model with y non-zero in s1\n");
		log("        (assert (distinct (|test_n y| s1) #b0000))\n");
		log("\n");
		log("        ; we are looking for a model with y zero in s2\n");
		log("        (assert (= (|test_n y| s2) #b0000))\n");
		log("\n");
		log("        ; is there such a model?\n");
		log("        (check-sat)\n");
		log("\n");
		log("The following yosys script will create a 'test.smt2' file for our proof:\n");
		log("\n");
		log("        read_verilog test.v\n");
		log("        hierarchy; proc; techmap; opt -fast\n");
		log("        write_smt2 -bv -tpl test.tpl test.smt2\n");
		log("\n");
		log("Running 'cvc4 test.smt2' will print 'unsat' because y can never transition\n");
		log("from non-zero to zero in the test design.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::ifstream template_f;
		bool bvmode = false;

		log_header("Executing SMT2 backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tpl" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-bv") {
				bvmode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line)) {
				int indent = 0;
				while (indent < GetSize(line) && (line[indent] == ' ' || line[indent] == '\t'))
					indent++;
				if (line.substr(indent, 2) == "%%")
					break;
				*f << line << std::endl;
			}
		}

		*f << stringf("; SMT-LIBv2 description generated by %s\n", yosys_version_str);

		for (auto module : design->modules())
		{
			if (module->get_bool_attribute("\\blackbox") || module->has_memories_warn() || module->has_processes_warn())
				continue;

			log("Creating SMT-LIBv2 representation of module %s.\n", log_id(module));

			Smt2Worker worker(module, bvmode);
			worker.run();
			worker.write(*f);
		}

		*f << stringf("; end of yosys output\n");

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line))
				*f << line << std::endl;
		}
	}
} Smt2Backend;

PRIVATE_NAMESPACE_END
