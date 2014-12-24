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

	std::vector<std::string> decls, clauses, trans;
	std::map<RTLIL::SigBit, std::string> bool_cache;
	std::map<RTLIL::IdString, std::vector<RTLIL::Cell*>> cells_by_type;

	Smt2Worker(RTLIL::Module *module) : ct(module->design), sigmap(module), module(module)
	{
		decls.push_back(stringf("(declare-sort |%s_s| 0)\n", log_id(module)));
	}

	std::string get_bool(RTLIL::SigBit bit, const char *state_name = "state")
	{
		sigmap.apply(bit);

		if (bit.wire == nullptr)
			return bit.data == RTLIL::State::S1 ? "true" : "false";

		if (!bool_cache.count(bit)) {
			std::string name = stringf("|%s_n %s %d|", log_id(module), log_id(bit.wire), bit.offset);
			for (auto &c : name)
				if (c == '\\') c = '/';
			decls.push_back(stringf("(declare-fun %s (|%s_s|) Bool)\n", name.c_str(), log_id(module)));
			bool_cache[bit] = name;
		}

		return stringf("(%s %s)", bool_cache.at(bit).c_str(), state_name);
	}

	void make_wire(RTLIL::Wire *wire)
	{
		for (int i = 0; i < GetSize(wire); i++)
			get_bool(RTLIL::SigBit(wire, i));
	}

	void run_gates()
	{
		// basic gate-level logic cell types

		for (auto cell : cells_by_type["$_BUF_"])
			clauses.push_back(stringf("  (= %s %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_BUF_");

		for (auto cell : cells_by_type["$_NOT_"])
			clauses.push_back(stringf("  (distinct %s %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_NOT_");

		for (auto cell : cells_by_type["$_AND_"])
			clauses.push_back(stringf("  (= (and %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_AND_");

		for (auto cell : cells_by_type["$_OR_"])
			clauses.push_back(stringf("  (= (or %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_OR_");

		for (auto cell : cells_by_type["$_XOR_"])
			clauses.push_back(stringf("  (= (xor %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_XOR_");

		for (auto cell : cells_by_type["$_MUX_"])
			clauses.push_back(stringf("  (= (ite %s %s %s) %s)\n",
					get_bool(cell->getPort("\\S").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_MUX_");


		// inverted gate-level logic cell types

		for (auto cell : cells_by_type["$_NAND_"])
			clauses.push_back(stringf("  (distinct (and %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_NAND_");

		for (auto cell : cells_by_type["$_NOR_"])
			clauses.push_back(stringf("  (distinct (or %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_NOR_");

		for (auto cell : cells_by_type["$_XNOR_"])
			clauses.push_back(stringf("  (distinct (xor %s %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_XNOR_");


		// advanced cmos-style logic cell types

		for (auto cell : cells_by_type["$_AOI3_"])
			clauses.push_back(stringf("  (distinct (or (and %s %s) %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\C").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_AOI3_");

		for (auto cell : cells_by_type["$_AOI4_"])
			clauses.push_back(stringf("  (distinct (or (and %s %s) (and %s %s)) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\C").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\D").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_AOI4_");

		for (auto cell : cells_by_type["$_OAI3_"])
			clauses.push_back(stringf("  (distinct (or (and %s %s) %s) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\C").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_OAI3_");

		for (auto cell : cells_by_type["$_OAI4_"])
			clauses.push_back(stringf("  (distinct (or (and %s %s) (and %s %s)) %s)\n",
					get_bool(cell->getPort("\\A").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\B").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\C").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\D").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Y").to_single_sigbit()).c_str()));
		cells_by_type.erase("$_OAI4_");


		// simple DFF cells (ignoring clock domains)

		for (auto cell : cells_by_type["$_DFF_P_"])
			trans.push_back(stringf("  (= %s %s)\n",
					get_bool(cell->getPort("\\D").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Q").to_single_sigbit(), "next_state").c_str()));
		cells_by_type.erase("$_DFF_P_");

		for (auto cell : cells_by_type["$_DFF_N_"])
			trans.push_back(stringf("  (= %s %s)\n",
					get_bool(cell->getPort("\\D").to_single_sigbit()).c_str(),
					get_bool(cell->getPort("\\Q").to_single_sigbit(), "next_state").c_str()));
		cells_by_type.erase("$_DFF_N_");
	}

	void run()
	{
		for (auto port : module->ports)
			make_wire(module->wire(port));

		for (auto cell : module->cells())
			cells_by_type[cell->type].push_back(cell);

		run_gates();

		for (auto &it : cells_by_type)
			log_error("Found %d cells of unsupported type %s in module %s.\n", GetSize(it.second), log_id(it.first), log_id(module));
	}

	void write(std::ostream &f)
	{
		for (auto it : decls)
			f << it;
		f << stringf("(define-fun |%s_c| ((state |%s_s|)) Bool (and\n", log_id(module), log_id(module));
		for (auto it : clauses)
			f << it;
		f << "true true))\n";
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
		log("Write a SMT-LIBv2 description of the current design. For a module with name\n");
		log("'<mod>' this will declare the sort '<mod>_s' and the two functions '<mod>_c'\n");
		log("(of arity 1) and '<mod>_t' (of arity 2).\n");
		log("\n");
		log("The sort represents the state of the module. Additional '<mod>_n' functions are\n");
		log("declared that can be used to access the values of all signals in the module.\n");
		log("\n");
		log("The '<mod>_c' function evaluates to 'true' when the given state is consistent\n");
		log("with the description of the models.\n");
		log("\n");
		log("The '<mod>_t' function evaluates to 'true' when the given pair of states is\n");
		log("describes a valid state transition, provided that '<mod>_c' is true for both\n");
		log("states.\n");
		log("\n");
		log("    -tpl <template_file>\n");
		log("        use the given template file. the line containing only the token '%%%%'\n");
		log("        is replaced with the regular output of this command.\n");
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
		log("        ; we only need QF_UF for this poof\n");
		log("        (set-logic QF_UF)\n");
		log("\n");
		log("        ; insert the auto-generated code here\n");
		log("        %%%%\n");
		log("\n");
		log("        ; declare two state variables s1 and s2\n");
		log("        (declare-fun s1 () test_s)\n");
		log("        (declare-fun s2 () test_s)\n");
		log("\n");
		log("        ; both states are valid and s2 follows s1\n");
		log("        (assert (test_c s1))\n");
		log("        (assert (test_c s2))\n");
		log("        (assert (test_t s1 s2))\n");
		log("\n");
		log("        ; we are looking for a solution with y non-zero in s1\n");
		log("        (assert (or (|test_n y 0| s1) (|test_n y 1| s1)\n");
		log("                    (|test_n y 2| s1) (|test_n y 3| s1)))\n");
		log("\n");
		log("        ; we are looking for a solution with y zero in s2\n");
		log("        (assert (not (or (|test_n y 0| s2) (|test_n y 1| s2)\n");
		log("                         (|test_n y 2| s2) (|test_n y 3| s2))))\n");
		log("\n");
		log("        ; is there such a solution?\n");
		log("        (check-sat)\n");
		log("\n");
		log("The following yosys script will create a 'test.smt2' file for our proof:\n");
		log("\n");
		log("        read_verilog test.v\n");
		log("        hierarchy; proc; techmap; opt -fast\n");
		log("        write_smt2 -template test.tpl test.smt2\n");
		log("\n");
		log("Running 'cvc4 test.smt2' will print 'unsat' because y can never transition\n");
		log("from non-zero to zero in the test design.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::ifstream template_f;
		log_header("Executing SMT2 backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-template" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
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

			Smt2Worker worker(module);
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
