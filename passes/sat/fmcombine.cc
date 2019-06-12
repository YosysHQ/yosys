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
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct opts_t
{
	bool initeq = false;
	bool anyeq = false;
	bool fwd = false;
	bool bwd = false;
	bool nop = false;
};

struct FmcombineWorker
{
	const opts_t &opts;
	Design *design;
	Module *original = nullptr;
	Module *module = nullptr;
	IdString orig_type, combined_type;

	FmcombineWorker(Design *design, IdString orig_type, const opts_t &opts) :
			opts(opts), design(design), original(design->module(orig_type)),
			orig_type(orig_type), combined_type("$fmcombine" + orig_type.str())
	{
	}

	SigSpec import_sig(SigSpec sig, const string &suffix)
	{
		SigSpec newsig;
		for (auto chunk : sig.chunks()) {
			if (chunk.wire != nullptr)
				chunk.wire = module->wire(chunk.wire->name.str() + suffix);
			newsig.append(chunk);
		}
		return newsig;
	}

	Cell *import_prim_cell(Cell *cell, const string &suffix)
	{
		Cell *c = module->addCell(cell->name.str() + suffix, cell->type);
		c->parameters = cell->parameters;
		c->attributes = cell->attributes;

		for (auto &conn : cell->connections())
			c->setPort(conn.first, import_sig(conn.second, suffix));

		return c;
	}

	void import_hier_cell(Cell *cell)
	{
		if (!cell->parameters.empty())
			log_cmd_error("Cell %s.%s has unresolved instance parameters.\n", log_id(original), log_id(cell));

		FmcombineWorker sub_worker(design, cell->type, opts);
		sub_worker.generate();

		Cell *c = module->addCell(cell->name.str() + "_combined", sub_worker.combined_type);
		// c->parameters = cell->parameters;
		c->attributes = cell->attributes;

		for (auto &conn : cell->connections()) {
			c->setPort(conn.first.str() + "_gold", import_sig(conn.second, "_gold"));
			c->setPort(conn.first.str() + "_gate", import_sig(conn.second, "_gate"));
		}
	}

	void generate()
	{
		if (design->module(combined_type)) {
			// log("Combined module %s already exists.\n", log_id(combined_type));
			return;
		}

		log("Generating combined module %s from module %s.\n", log_id(combined_type), log_id(orig_type));
		module = design->addModule(combined_type);

		for (auto wire : original->wires()) {
			module->addWire(wire->name.str() + "_gold", wire);
			module->addWire(wire->name.str() + "_gate", wire);
		}
		module->fixup_ports();

		for (auto cell : original->cells()) {
			if (design->module(cell->type) == nullptr) {
				if (opts.anyeq && cell->type.in("$anyseq", "$anyconst")) {
					Cell *gold = import_prim_cell(cell, "_gold");
					for (auto &conn : cell->connections())
						module->connect(import_sig(conn.second, "_gate"), gold->getPort(conn.first));
				} else {
					Cell *gold = import_prim_cell(cell, "_gold");
					Cell *gate = import_prim_cell(cell, "_gate");
					if (opts.initeq) {
						if (cell->type.in("$ff", "$dff", "$dffe",
								"$dffsr", "$adff", "$dlatch", "$dlatchsr")) {
							SigSpec gold_q = gold->getPort("\\Q");
							SigSpec gate_q = gate->getPort("\\Q");
							SigSpec en = module->Initstate(NEW_ID);
							SigSpec eq = module->Eq(NEW_ID, gold_q, gate_q);
							module->addAssume(NEW_ID, eq, en);
						}
					}
				}
			} else {
				import_hier_cell(cell);
			}
		}

		for (auto &conn : original->connections()) {
			module->connect(import_sig(conn.first, "_gold"), import_sig(conn.second, "_gold"));
			module->connect(import_sig(conn.first, "_gate"), import_sig(conn.second, "_gate"));
		}

		if (opts.nop)
			return;

		CellTypes ct;
		ct.setup_internals_eval();
		ct.setup_stdcells_eval();

		SigMap sigmap(module);

		dict<SigBit, SigBit> data_bit_to_eq_net;
		dict<Cell*, SigSpec> cell_to_eq_nets;
		dict<SigSpec, SigSpec> reduce_db;
		dict<SigSpec, SigSpec> invert_db;

		for (auto cell : original->cells())
		{
			if (!ct.cell_known(cell->type))
				continue;

			for (auto &conn : cell->connections())
			{
				if (!cell->output(conn.first))
					continue;

				SigSpec A = import_sig(conn.second, "_gold");
				SigSpec B = import_sig(conn.second, "_gate");
				SigBit EQ = module->Eq(NEW_ID, A, B);

				for (auto bit : sigmap({A, B}))
					data_bit_to_eq_net[bit] = EQ;

				cell_to_eq_nets[cell].append(EQ);
			}
		}

		for (auto cell : original->cells())
		{
			if (!ct.cell_known(cell->type))
				continue;

			bool skip_cell = !cell_to_eq_nets.count(cell);
			pool<SigBit> src_eq_bits;

			for (auto &conn : cell->connections())
			{
				if (skip_cell)
					break;

				if (cell->output(conn.first))
					continue;

				SigSpec A = import_sig(conn.second, "_gold");
				SigSpec B = import_sig(conn.second, "_gate");

				for (auto bit : sigmap({A, B})) {
					if (data_bit_to_eq_net.count(bit))
						src_eq_bits.insert(data_bit_to_eq_net.at(bit));
					else
						skip_cell = true;
				}
			}

			if (!skip_cell) {
				SigSpec antecedent = SigSpec(src_eq_bits);
				antecedent.sort_and_unify();

				if (GetSize(antecedent) > 1) {
					if (reduce_db.count(antecedent) == 0)
						reduce_db[antecedent] = module->ReduceAnd(NEW_ID, antecedent);
					antecedent = reduce_db.at(antecedent);
				}

				SigSpec consequent = cell_to_eq_nets.at(cell);
				consequent.sort_and_unify();

				if (GetSize(consequent) > 1) {
					if (reduce_db.count(consequent) == 0)
						reduce_db[consequent] = module->ReduceAnd(NEW_ID, consequent);
					consequent = reduce_db.at(consequent);
				}

				if (opts.fwd)
					module->addAssume(NEW_ID, consequent, antecedent);

				if (opts.bwd)
				{
					if (invert_db.count(antecedent) == 0)
						invert_db[antecedent] = module->Not(NEW_ID, antecedent);

					if (invert_db.count(consequent) == 0)
						invert_db[consequent] = module->Not(NEW_ID, consequent);

					module->addAssume(NEW_ID, invert_db.at(antecedent), invert_db.at(consequent));
				}
			}
		}
	}
};

struct FmcombinePass : public Pass {
	FmcombinePass() : Pass("fmcombine", "combine two instances of a cell into one") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fmcombine [options] module_name gold_cell gate_cell\n");
		// log("    fmcombine [options] @gold_cell @gate_cell\n");
		log("\n");
		log("This pass takes two cells, which are instances of the same module, and replaces\n");
		log("them with one instance of a special 'combined' module, that effectively\n");
		log("contains two copies of the original module, plus some formal properties.\n");
		log("\n");
		log("This is useful for formal test benches that check what differences in behavior\n");
		log("a slight difference in input causes in a module.\n");
		log("\n");
		log("    -initeq\n");
		log("        Insert assumptions that initially all FFs in both circuits have the\n");
		log("        same initial values.\n");
		log("\n");
		log("    -anyeq\n");
		log("        Do not duplicate $anyseq/$anyconst cells.\n");
		log("\n");
		log("    -fwd\n");
		log("        Insert forward hint assumptions into the combined module.\n");
		log("\n");
		log("    -bwd\n");
		log("        Insert backward hint assumptions into the combined module.\n");
		log("        (Backward hints are logically equivalend to fordward hits, but\n");
		log("        some solvers are faster with bwd hints, or even both -bwd and -fwd.)\n");
		log("\n");
		log("    -nop\n");
		log("        Don't insert hint assumptions into the combined module.\n");
		log("        (This should not provide any speedup over the original design, but\n");
		log("        strangely sometimes it does.)\n");
		log("\n");
		log("If none of -fwd, -bwd, and -nop is given, then -fwd is used as default.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		opts_t opts;
		Module *module = nullptr;
		Cell *gold_cell = nullptr;
		Cell *gate_cell = nullptr;

		log_header(design, "Executing FMCOMBINE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-o" && argidx+1 < args.size()) {
			// 	filename = args[++argidx];
			// 	continue;
			// }
			if (args[argidx] == "-initeq") {
				opts.initeq = true;
				continue;
			}
			if (args[argidx] == "-anyeq") {
				opts.anyeq = true;
				continue;
			}
			if (args[argidx] == "-fwd") {
				opts.fwd = true;
				continue;
			}
			if (args[argidx] == "-bwd") {
				opts.bwd = true;
				continue;
			}
			if (args[argidx] == "-nop") {
				opts.nop = true;
				continue;
			}
			break;
		}
		if (argidx+2 == args.size())
		{
			string gold_name = args[argidx++];
			string gate_name = args[argidx++];
			log_cmd_error("fmcombine @gold_cell @gate_cell call style is not implemented yet.");
		}
		else if (argidx+3 == args.size())
		{
			IdString module_name = RTLIL::escape_id(args[argidx++]);
			IdString gold_name = RTLIL::escape_id(args[argidx++]);
			IdString gate_name = RTLIL::escape_id(args[argidx++]);

			module = design->module(module_name);
			if (module == nullptr)
				log_cmd_error("Module %s not found.\n", log_id(module_name));

			gold_cell = module->cell(gold_name);
			if (gold_cell == nullptr)
				log_cmd_error("Gold cell %s not found in module %s.\n", log_id(gold_name), log_id(module));

			gate_cell = module->cell(gate_name);
			if (gate_cell == nullptr)
				log_cmd_error("Gate cell %s not found in module %s.\n", log_id(gate_name), log_id(module));
		}
		else
		{
			log_cmd_error("Invalid number of arguments.\n");
		}
		// extra_args(args, argidx, design);

		if (opts.nop && (opts.fwd || opts.bwd))
			log_cmd_error("Option -nop can not be combined with -fwd and/or -bwd.\n");

		if (!opts.nop && !opts.fwd && !opts.bwd)
			opts.fwd = true;

		if (gold_cell->type != gate_cell->type)
			log_cmd_error("Types of gold and gate cells do not match.\n");
		if (!gold_cell->parameters.empty())
			log_cmd_error("Gold cell has unresolved instance parameters.\n");
		if (!gate_cell->parameters.empty())
			log_cmd_error("Gate cell has unresolved instance parameters.\n");

		FmcombineWorker worker(design, gold_cell->type, opts);
		worker.generate();
		IdString combined_cell_name = module->uniquify(stringf("\\%s_%s", log_id(gold_cell), log_id(gate_cell)));

		Cell *cell = module->addCell(combined_cell_name, worker.combined_type);
		cell->attributes = gold_cell->attributes;
		cell->add_strpool_attribute("\\src", gate_cell->get_strpool_attribute("\\src"));

		log("Combining cells %s and %s in module %s into new cell %s.\n", log_id(gold_cell), log_id(gate_cell), log_id(module), log_id(cell));

		for (auto &conn : gold_cell->connections())
			cell->setPort(conn.first.str() + "_gold", conn.second);
		module->remove(gold_cell);

		for (auto &conn : gate_cell->connections())
			cell->setPort(conn.first.str() + "_gate", conn.second);
		module->remove(gate_cell);
	}
} FmcombinePass;

PRIVATE_NAMESPACE_END
