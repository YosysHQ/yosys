/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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
#include "kernel/satgen.h"
#include "kernel/consteval.h"
#include "kernel/celledges.h"
#include "kernel/macc.h"
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static uint32_t xorshift32_state = 123456789;

static uint32_t xorshift32(uint32_t limit) {
	xorshift32_state ^= xorshift32_state << 13;
	xorshift32_state ^= xorshift32_state >> 17;
	xorshift32_state ^= xorshift32_state << 5;
	return xorshift32_state % limit;
}

static void create_gold_module(RTLIL::Design *design, RTLIL::IdString cell_type, std::string cell_type_flags, bool constmode, bool muxdiv)
{
	RTLIL::Module *module = design->addModule("\\gold");
	RTLIL::Cell *cell = module->addCell("\\UUT", cell_type);
	RTLIL::Wire *wire;

	if (cell_type.in("$mux", "$pmux"))
	{
		int width = 1 + xorshift32(8);
		int swidth = cell_type == "$mux" ? 1 : 1 + xorshift32(8);

		wire = module->addWire("\\A");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\A", wire);

		wire = module->addWire("\\B");
		wire->width = width * swidth;
		wire->port_input = true;
		cell->setPort("\\B", wire);

		wire = module->addWire("\\S");
		wire->width = swidth;
		wire->port_input = true;
		cell->setPort("\\S", wire);

		wire = module->addWire("\\Y");
		wire->width = width;
		wire->port_output = true;
		cell->setPort("\\Y", wire);
	}

	if (cell_type == "$fa")
	{
		int width = 1 + xorshift32(8);

		wire = module->addWire("\\A");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\A", wire);

		wire = module->addWire("\\B");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\B", wire);

		wire = module->addWire("\\C");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\C", wire);

		wire = module->addWire("\\X");
		wire->width = width;
		wire->port_output = true;
		cell->setPort("\\X", wire);

		wire = module->addWire("\\Y");
		wire->width = width;
		wire->port_output = true;
		cell->setPort("\\Y", wire);
	}

	if (cell_type == "$lcu")
	{
		int width = 1 + xorshift32(8);

		wire = module->addWire("\\P");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\P", wire);

		wire = module->addWire("\\G");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\G", wire);

		wire = module->addWire("\\CI");
		wire->port_input = true;
		cell->setPort("\\CI", wire);

		wire = module->addWire("\\CO");
		wire->width = width;
		wire->port_output = true;
		cell->setPort("\\CO", wire);
	}

	if (cell_type == "$macc")
	{
		Macc macc;
		int width = 1 + xorshift32(8);
		int depth = 1 + xorshift32(6);
		int mulbits_a = 0, mulbits_b = 0;

		RTLIL::Wire *wire_a = module->addWire("\\A");
		wire_a->width = 0;
		wire_a->port_input = true;

		for (int i = 0; i < depth; i++)
		{
			int size_a = xorshift32(width) + 1;
			int size_b = depth > 4 ? 0 : xorshift32(width) + 1;

			if (mulbits_a + size_a*size_b <= 96 && mulbits_b + size_a + size_b <= 16 && xorshift32(2) == 1) {
				mulbits_a += size_a * size_b;
				mulbits_b += size_a + size_b;
			} else
				size_b = 0;

			Macc::port_t this_port;

			wire_a->width += size_a;
			this_port.in_a = RTLIL::SigSpec(wire_a, wire_a->width - size_a, size_a);

			wire_a->width += size_b;
			this_port.in_b = RTLIL::SigSpec(wire_a, wire_a->width - size_b, size_b);

			this_port.is_signed = xorshift32(2) == 1;
			this_port.do_subtract = xorshift32(2) == 1;
			macc.ports.push_back(this_port);
		}

		wire = module->addWire("\\B");
		wire->width = xorshift32(mulbits_a ? xorshift32(4)+1 : xorshift32(16)+1);
		wire->port_input = true;
		macc.bit_ports = wire;

		wire = module->addWire("\\Y");
		wire->width = width;
		wire->port_output = true;
		cell->setPort("\\Y", wire);

		macc.to_cell(cell);
	}

	if (cell_type == "$lut")
	{
		int width = 1 + xorshift32(6);

		wire = module->addWire("\\A");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\A", wire);

		wire = module->addWire("\\Y");
		wire->port_output = true;
		cell->setPort("\\Y", wire);

		RTLIL::SigSpec config;
		for (int i = 0; i < (1 << width); i++)
			config.append(xorshift32(2) ? State::S1 : State::S0);

		cell->setParam("\\LUT", config.as_const());
	}

	if (cell_type == "$sop")
	{
		int width = 1 + xorshift32(8);
		int depth = 1 + xorshift32(8);

		wire = module->addWire("\\A");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\A", wire);

		wire = module->addWire("\\Y");
		wire->port_output = true;
		cell->setPort("\\Y", wire);

		RTLIL::SigSpec config;
		for (int i = 0; i < width*depth; i++)
			switch (xorshift32(3)) {
				case 0:
					config.append(State::S1);
					config.append(State::S0);
					break;
				case 1:
					config.append(State::S0);
					config.append(State::S1);
					break;
				case 2:
					config.append(State::S0);
					config.append(State::S0);
					break;
			}

		cell->setParam("\\DEPTH", depth);
		cell->setParam("\\TABLE", config.as_const());
	}

	if (cell_type_flags.find('A') != std::string::npos) {
		wire = module->addWire("\\A");
		wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->setPort("\\A", wire);
	}

	if (cell_type_flags.find('B') != std::string::npos) {
		wire = module->addWire("\\B");
		if (cell_type_flags.find('h') != std::string::npos)
			wire->width = 1 + xorshift32(6);
		else
			wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->setPort("\\B", wire);
	}

	if (cell_type_flags.find('S') != std::string::npos && xorshift32(2)) {
		if (cell_type_flags.find('A') != std::string::npos)
			cell->parameters["\\A_SIGNED"] = true;
		if (cell_type_flags.find('B') != std::string::npos)
			cell->parameters["\\B_SIGNED"] = true;
	}

	if (cell_type_flags.find('s') != std::string::npos) {
		if (cell_type_flags.find('A') != std::string::npos && xorshift32(2))
			cell->parameters["\\A_SIGNED"] = true;
		if (cell_type_flags.find('B') != std::string::npos && xorshift32(2))
			cell->parameters["\\B_SIGNED"] = true;
	}

	if (cell_type_flags.find('Y') != std::string::npos) {
		wire = module->addWire("\\Y");
		wire->width = 1 + xorshift32(8);
		wire->port_output = true;
		cell->setPort("\\Y", wire);
	}

	if (muxdiv && cell_type.in("$div", "$mod")) {
		auto b_not_zero = module->ReduceBool(NEW_ID, cell->getPort("\\B"));
		auto div_out = module->addWire(NEW_ID, GetSize(cell->getPort("\\Y")));
		module->addMux(NEW_ID, RTLIL::SigSpec(0, GetSize(div_out)), div_out, b_not_zero, cell->getPort("\\Y"));
		cell->setPort("\\Y", div_out);
	}

	if (cell_type == "$alu")
	{
		wire = module->addWire("\\CI");
		wire->port_input = true;
		cell->setPort("\\CI", wire);

		wire = module->addWire("\\BI");
		wire->port_input = true;
		cell->setPort("\\BI", wire);

		wire = module->addWire("\\X");
		wire->width = GetSize(cell->getPort("\\Y"));
		wire->port_output = true;
		cell->setPort("\\X", wire);

		wire = module->addWire("\\CO");
		wire->width = GetSize(cell->getPort("\\Y"));
		wire->port_output = true;
		cell->setPort("\\CO", wire);
	}

	if (constmode)
	{
		auto conn_list = cell->connections();
		for (auto &conn : conn_list)
		{
			RTLIL::SigSpec sig = conn.second;

			if (GetSize(sig) == 0 || sig[0].wire == nullptr || sig[0].wire->port_output)
				continue;

			int n, m;
			switch (xorshift32(5))
			{
			case 0:
				n = xorshift32(GetSize(sig) + 1);
				for (int i = 0; i < n; i++)
					sig[i] = xorshift32(2) == 1 ? State::S1 : State::S0;
				break;
			case 1:
				n = xorshift32(GetSize(sig) + 1);
				for (int i = n; i < GetSize(sig); i++)
					sig[i] = xorshift32(2) == 1 ? State::S1 : State::S0;
				break;
			case 2:
				n = xorshift32(GetSize(sig));
				m = xorshift32(GetSize(sig));
				for (int i = min(n, m); i < max(n, m); i++)
					sig[i] = xorshift32(2) == 1 ? State::S1 : State::S0;
				break;
			}

			cell->setPort(conn.first, sig);
		}
	}

	module->fixup_ports();
	cell->fixup_parameters();
	cell->check();
}

static void run_edges_test(RTLIL::Design *design, bool verbose)
{
	Module *module = *design->modules().begin();
	Cell *cell = *module->cells().begin();

	ezSatPtr ezptr;
	ezSAT &ez = *ezptr.get();

	SigMap sigmap(module);
	SatGen satgen(&ez, &sigmap);

	FwdCellEdgesDatabase edges_db(sigmap);
	if (!edges_db.add_edges_from_cell(cell))
		log_error("Creating edge database failed for this cell!\n");

	dict<SigBit, pool<SigBit>> satgen_db;

	satgen.setContext(&sigmap, "X:");
	satgen.importCell(cell);

	satgen.setContext(&sigmap, "Y:");
	satgen.importCell(cell);

	vector<tuple<SigBit, int, int>> input_db, output_db;

	for (auto &conn : cell->connections())
	{
		SigSpec bits = sigmap(conn.second);

		satgen.setContext(&sigmap, "X:");
		std::vector<int> xbits = satgen.importSigSpec(bits);

		satgen.setContext(&sigmap, "Y:");
		std::vector<int> ybits = satgen.importSigSpec(bits);

		for (int i = 0; i < GetSize(bits); i++)
			if (cell->input(conn.first))
				input_db.emplace_back(bits[i], xbits[i], ybits[i]);
			else
				output_db.emplace_back(bits[i], xbits[i], ybits[i]);
	}

	if (verbose)
		log("\nSAT solving for all edges:\n");

	for (int i = 0; i < GetSize(input_db); i++)
	{
		SigBit inbit = std::get<0>(input_db[i]);

		if (verbose)
			log("  Testing input signal %s:\n", log_signal(inbit));

		vector<int> xinbits, yinbits;
		for (int k = 0; k < GetSize(input_db); k++)
			if (k != i) {
				xinbits.push_back(std::get<1>(input_db[k]));
				yinbits.push_back(std::get<2>(input_db[k]));
			}

		int xyinbit_ok = ez.vec_eq(xinbits, yinbits);

		for (int k = 0; k < GetSize(output_db); k++)
		{
			SigBit outbit = std::get<0>(output_db[k]);
			int xoutbit = std::get<1>(output_db[k]);
			int youtbit = std::get<2>(output_db[k]);

			bool is_edge = ez.solve(xyinbit_ok, ez.XOR(xoutbit, youtbit));

			if (is_edge)
				satgen_db[inbit].insert(outbit);

			if (verbose) {
				bool is_ref_edge = edges_db.db.count(inbit) && edges_db.db.at(inbit).count(outbit);
				log("    %c %s %s\n", is_edge ? 'x' : 'o', log_signal(outbit), is_edge == is_ref_edge ? "OK" : "ERROR");
			}
		}
	}

	if (satgen_db == edges_db.db)
		log("PASS.\n");
	else
		log_error("SAT-based edge table does not match the database!\n");
}

static void run_eval_test(RTLIL::Design *design, bool verbose, bool nosat, std::string uut_name, std::ofstream &vlog_file)
{
	log("Eval testing:%c", verbose ? '\n' : ' ');

	RTLIL::Module *gold_mod = design->module("\\gold");
	RTLIL::Module *gate_mod = design->module("\\gate");
	ConstEval gold_ce(gold_mod), gate_ce(gate_mod);

	ezSatPtr ez1, ez2;
	SigMap sigmap(gold_mod);
	SatGen satgen1(ez1.get(), &sigmap);
	SatGen satgen2(ez2.get(), &sigmap);
	satgen2.model_undef = true;

	if (!nosat)
		for (auto cell : gold_mod->cells()) {
			satgen1.importCell(cell);
			satgen2.importCell(cell);
		}

	if (vlog_file.is_open())
	{
		vlog_file << stringf("\nmodule %s;\n", uut_name.c_str());

		for (auto port : gold_mod->ports) {
			RTLIL::Wire *wire = gold_mod->wire(port);
			if (wire->port_input)
				vlog_file << stringf("  reg [%d:0] %s;\n", GetSize(wire)-1, log_id(wire));
			else
				vlog_file << stringf("  wire [%d:0] %s_expr, %s_noexpr;\n", GetSize(wire)-1, log_id(wire), log_id(wire));
		}

		vlog_file << stringf("  %s_expr uut_expr(", uut_name.c_str());
		for (int i = 0; i < GetSize(gold_mod->ports); i++)
			vlog_file << stringf("%s.%s(%s%s)", i ? ", " : "", log_id(gold_mod->ports[i]), log_id(gold_mod->ports[i]),
					gold_mod->wire(gold_mod->ports[i])->port_input ? "" : "_expr");
		vlog_file << stringf(");\n");

		vlog_file << stringf("  %s_expr uut_noexpr(", uut_name.c_str());
		for (int i = 0; i < GetSize(gold_mod->ports); i++)
			vlog_file << stringf("%s.%s(%s%s)", i ? ", " : "", log_id(gold_mod->ports[i]), log_id(gold_mod->ports[i]),
					gold_mod->wire(gold_mod->ports[i])->port_input ? "" : "_noexpr");
		vlog_file << stringf(");\n");

		vlog_file << stringf("  task run;\n");
		vlog_file << stringf("    begin\n");
		vlog_file << stringf("      $display(\"%s\");\n", uut_name.c_str());
	}

	for (int i = 0; i < 64; i++)
	{
		log(verbose ? "\n" : ".");
		gold_ce.clear();
		gate_ce.clear();

		RTLIL::SigSpec in_sig, in_val;
		RTLIL::SigSpec out_sig, out_val;
		std::string vlog_pattern_info;

		for (auto port : gold_mod->ports)
		{
			RTLIL::Wire *gold_wire = gold_mod->wire(port);
			RTLIL::Wire *gate_wire = gate_mod->wire(port);

			log_assert(gold_wire != nullptr);
			log_assert(gate_wire != nullptr);
			log_assert(gold_wire->port_input == gate_wire->port_input);
			log_assert(GetSize(gold_wire) == GetSize(gate_wire));

			if (!gold_wire->port_input)
				continue;

			RTLIL::Const in_value;
			for (int i = 0; i < GetSize(gold_wire); i++)
				in_value.bits.push_back(xorshift32(2) ? State::S1 : State::S0);

			if (xorshift32(4) == 0) {
				int inv_chance = 1 + xorshift32(8);
				for (int i = 0; i < GetSize(gold_wire); i++)
					if (xorshift32(inv_chance) == 0)
						in_value.bits[i] = RTLIL::Sx;
			}

			if (verbose)
				log("%s: %s\n", log_id(gold_wire), log_signal(in_value));

			in_sig.append(gold_wire);
			in_val.append(in_value);

			gold_ce.set(gold_wire, in_value);
			gate_ce.set(gate_wire, in_value);

			if (vlog_file.is_open() && GetSize(in_value) > 0) {
				vlog_file << stringf("      %s = 'b%s;\n", log_id(gold_wire), in_value.as_string().c_str());
				if (!vlog_pattern_info.empty())
					vlog_pattern_info += " ";
				vlog_pattern_info += stringf("%s=%s", log_id(gold_wire), log_signal(in_value));
			}
		}

		if (vlog_file.is_open())
			vlog_file << stringf("      #1;\n");

		for (auto port : gold_mod->ports)
		{
			RTLIL::Wire *gold_wire = gold_mod->wire(port);
			RTLIL::Wire *gate_wire = gate_mod->wire(port);

			log_assert(gold_wire != nullptr);
			log_assert(gate_wire != nullptr);
			log_assert(gold_wire->port_output == gate_wire->port_output);
			log_assert(GetSize(gold_wire) == GetSize(gate_wire));

			if (!gold_wire->port_output)
				continue;

			RTLIL::SigSpec gold_outval(gold_wire);
			RTLIL::SigSpec gate_outval(gate_wire);

			if (!gold_ce.eval(gold_outval))
				log_error("Failed to eval %s in gold module.\n", log_id(gold_wire));

			if (!gate_ce.eval(gate_outval))
				log_error("Failed to eval %s in gate module.\n", log_id(gate_wire));

			bool gold_gate_mismatch = false;
			for (int i = 0; i < GetSize(gold_wire); i++) {
				if (gold_outval[i] == RTLIL::Sx)
					continue;
				if (gold_outval[i] == gate_outval[i])
					continue;
				gold_gate_mismatch = true;
				break;
			}

			if (gold_gate_mismatch)
				log_error("Mismatch in output %s: gold:%s != gate:%s\n", log_id(gate_wire), log_signal(gold_outval), log_signal(gate_outval));

			if (verbose)
				log("%s: %s\n", log_id(gold_wire), log_signal(gold_outval));

			out_sig.append(gold_wire);
			out_val.append(gold_outval);

			if (vlog_file.is_open()) {
				vlog_file << stringf("      $display(\"[%s] %s expected: %%b, expr: %%b, noexpr: %%b\", %d'b%s, %s_expr, %s_noexpr);\n",
						vlog_pattern_info.c_str(), log_id(gold_wire), GetSize(gold_outval), gold_outval.as_string().c_str(), log_id(gold_wire), log_id(gold_wire));
				vlog_file << stringf("      if (%s_expr !== %d'b%s) begin $display(\"ERROR\"); $finish; end\n", log_id(gold_wire), GetSize(gold_outval), gold_outval.as_string().c_str());
				vlog_file << stringf("      if (%s_noexpr !== %d'b%s) begin $display(\"ERROR\"); $finish; end\n", log_id(gold_wire), GetSize(gold_outval), gold_outval.as_string().c_str());
			}
		}

		if (verbose)
			log("EVAL:  %s\n", out_val.as_string().c_str());

		if (!nosat)
		{
			std::vector<int> sat1_in_sig = satgen1.importSigSpec(in_sig);
			std::vector<int> sat1_in_val = satgen1.importSigSpec(in_val);

			std::vector<int> sat1_model = satgen1.importSigSpec(out_sig);
			std::vector<bool> sat1_model_value;

			if (!ez1->solve(sat1_model, sat1_model_value, ez1->vec_eq(sat1_in_sig, sat1_in_val)))
				log_error("Evaluating sat model 1 (no undef modeling) failed!\n");

			if (verbose) {
				log("SAT 1: ");
				for (int i = GetSize(out_sig)-1; i >= 0; i--)
					log("%c", sat1_model_value.at(i) ? '1' : '0');
				log("\n");
			}

			for (int i = 0; i < GetSize(out_sig); i++) {
				if (out_val[i] != State::S0 && out_val[i] != State::S1)
					continue;
				if (out_val[i] == State::S0 && sat1_model_value.at(i) == false)
					continue;
				if (out_val[i] == State::S1 && sat1_model_value.at(i) == true)
					continue;
				log_error("Mismatch in sat model 1 (no undef modeling) output!\n");
			}

			std::vector<int> sat2_in_def_sig = satgen2.importDefSigSpec(in_sig);
			std::vector<int> sat2_in_def_val = satgen2.importDefSigSpec(in_val);

			std::vector<int> sat2_in_undef_sig = satgen2.importUndefSigSpec(in_sig);
			std::vector<int> sat2_in_undef_val = satgen2.importUndefSigSpec(in_val);

			std::vector<int> sat2_model_def_sig = satgen2.importDefSigSpec(out_sig);
			std::vector<int> sat2_model_undef_sig = satgen2.importUndefSigSpec(out_sig);

			std::vector<int> sat2_model;
			sat2_model.insert(sat2_model.end(), sat2_model_def_sig.begin(), sat2_model_def_sig.end());
			sat2_model.insert(sat2_model.end(), sat2_model_undef_sig.begin(), sat2_model_undef_sig.end());

			std::vector<bool> sat2_model_value;

			if (!ez2->solve(sat2_model, sat2_model_value, ez2->vec_eq(sat2_in_def_sig, sat2_in_def_val), ez2->vec_eq(sat2_in_undef_sig, sat2_in_undef_val)))
				log_error("Evaluating sat model 2 (undef modeling) failed!\n");

			if (verbose) {
				log("SAT 2: ");
				for (int i = GetSize(out_sig)-1; i >= 0; i--)
					log("%c", sat2_model_value.at(GetSize(out_sig) + i) ? 'x' : sat2_model_value.at(i) ? '1' : '0');
				log("\n");
			}

			for (int i = 0; i < GetSize(out_sig); i++) {
				if (sat2_model_value.at(GetSize(out_sig) + i)) {
					if (out_val[i] != State::S0 && out_val[i] != State::S1)
						continue;
				} else {
					if (out_val[i] == State::S0 && sat2_model_value.at(i) == false)
						continue;
					if (out_val[i] == State::S1 && sat2_model_value.at(i) == true)
						continue;
				}
				log_error("Mismatch in sat model 2 (undef modeling) output!\n");
			}
		}
	}

	if (vlog_file.is_open()) {
		vlog_file << stringf("    end\n");
		vlog_file << stringf("  endtask\n");
		vlog_file << stringf("endmodule\n");
	}

	if (!verbose)
		log(" ok.\n");
}

struct TestCellPass : public Pass {
	TestCellPass() : Pass("test_cell", "automatically test the implementation of a cell type") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_cell [options] {cell-types}\n");
		log("\n");
		log("Tests the internal implementation of the given cell type (for example '$add')\n");
		log("by comparing SAT solver, EVAL and TECHMAP implementations of the cell types..\n");
		log("\n");
		log("Run with 'all' instead of a cell type to run the test on all supported\n");
		log("cell types. Use for example 'all /$add' for all cell types except $add.\n");
		log("\n");
		log("    -n {integer}\n");
		log("        create this number of cell instances and test them (default = 100).\n");
		log("\n");
		log("    -s {positive_integer}\n");
		log("        use this value as rng seed value (default = unix time).\n");
		log("\n");
		log("    -f {ilang_file}\n");
		log("        don't generate circuits. instead load the specified ilang file.\n");
		log("\n");
		log("    -w {filename_prefix}\n");
		log("        don't test anything. just generate the circuits and write them\n");
		log("        to ilang files with the specified prefix\n");
		log("\n");
		log("    -map {filename}\n");
		log("        pass this option to techmap.\n");
		log("\n");
		log("    -simlib\n");
		log("        use \"techmap -D SIMLIB_NOCHECKS -map +/simlib.v -max_iter 2 -autoproc\"\n");
		log("\n");
		log("    -aigmap\n");
		log("        instead of calling \"techmap\", call \"aigmap\"\n");
		log("\n");
		log("    -muxdiv\n");
		log("        when creating test benches with dividers, create an additional mux\n");
		log("        to mask out the division-by-zero case\n");
		log("\n");
		log("    -script {script_file}\n");
		log("        instead of calling \"techmap\", call \"script {script_file}\".\n");
		log("\n");
		log("    -const\n");
		log("        set some input bits to random constant values\n");
		log("\n");
		log("    -nosat\n");
		log("        do not check SAT model or run SAT equivalence checking\n");
		log("\n");
		log("    -noeval\n");
		log("        do not check const-eval models\n");
		log("\n");
		log("    -edges\n");
		log("        test cell edges db creator against sat-based implementation\n");
		log("\n");
		log("    -v\n");
		log("        print additional debug information to the console\n");
		log("\n");
		log("    -vlog {filename}\n");
		log("        create a Verilog test bench to test simlib and write_verilog\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design*) YS_OVERRIDE
	{
		int num_iter = 100;
		std::string techmap_cmd = "techmap -assert";
		std::string ilang_file, write_prefix;
		xorshift32_state = 0;
		std::ofstream vlog_file;
		bool muxdiv = false;
		bool verbose = false;
		bool constmode = false;
		bool nosat = false;
		bool noeval = false;
		bool edges = false;

		int argidx;
		for (argidx = 1; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-n" && argidx+1 < GetSize(args)) {
				num_iter = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-s" && argidx+1 < GetSize(args)) {
				xorshift32_state = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-map" && argidx+1 < GetSize(args)) {
				techmap_cmd += " -map " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-f" && argidx+1 < GetSize(args)) {
				ilang_file = args[++argidx];
				num_iter = 1;
				continue;
			}
			if (args[argidx] == "-w" && argidx+1 < GetSize(args)) {
				write_prefix = args[++argidx];
				continue;
			}
			if (args[argidx] == "-script" && argidx+1 < GetSize(args)) {
				techmap_cmd = "script " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-simlib") {
				techmap_cmd = "techmap -D SIMLIB_NOCHECKS -map +/simlib.v -max_iter 2 -autoproc";
				continue;
			}
			if (args[argidx] == "-aigmap") {
				techmap_cmd = "aigmap";
				continue;
			}
			if (args[argidx] == "-muxdiv") {
				muxdiv = true;
				continue;
			}
			if (args[argidx] == "-const") {
				constmode = true;
				continue;
			}
			if (args[argidx] == "-nosat") {
				nosat = true;
				continue;
			}
			if (args[argidx] == "-noeval") {
				noeval = true;
				continue;
			}
			if (args[argidx] == "-edges") {
				edges = true;
				continue;
			}
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-vlog" && argidx+1 < GetSize(args)) {
				vlog_file.open(args[++argidx], std::ios_base::trunc);
				if (!vlog_file.is_open())
					log_cmd_error("Failed to open output file `%s'.\n", args[argidx].c_str());
				continue;
			}
			break;
		}

		if (xorshift32_state == 0) {
			xorshift32_state = time(NULL) & 0x7fffffff;
			log("Rng seed value: %d\n", int(xorshift32_state));
		}

		std::map<std::string, std::string> cell_types;
		std::vector<std::string> selected_cell_types;

		cell_types["$not"] = "ASY";
		cell_types["$pos"] = "ASY";
		cell_types["$neg"] = "ASY";

		cell_types["$and"]  = "ABSY";
		cell_types["$or"]   = "ABSY";
		cell_types["$xor"]  = "ABSY";
		cell_types["$xnor"] = "ABSY";

		cell_types["$reduce_and"]  = "ASY";
		cell_types["$reduce_or"]   = "ASY";
		cell_types["$reduce_xor"]  = "ASY";
		cell_types["$reduce_xnor"] = "ASY";
		cell_types["$reduce_bool"] = "ASY";

		cell_types["$shl"]    = "ABshY";
		cell_types["$shr"]    = "ABshY";
		cell_types["$sshl"]   = "ABshY";
		cell_types["$sshr"]   = "ABshY";
		cell_types["$shift"]  = "ABshY";
		cell_types["$shiftx"] = "ABshY";

		cell_types["$lt"]  = "ABSY";
		cell_types["$le"]  = "ABSY";
		cell_types["$eq"]  = "ABSY";
		cell_types["$ne"]  = "ABSY";
		// cell_types["$eqx"] = "ABSY";
		// cell_types["$nex"] = "ABSY";
		cell_types["$ge"]  = "ABSY";
		cell_types["$gt"]  = "ABSY";

		cell_types["$add"] = "ABSY";
		cell_types["$sub"] = "ABSY";
		cell_types["$mul"] = "ABSY";
		cell_types["$div"] = "ABSY";
		cell_types["$mod"] = "ABSY";
		// cell_types["$pow"] = "ABsY";

		cell_types["$logic_not"] = "ASY";
		cell_types["$logic_and"] = "ABSY";
		cell_types["$logic_or"]  = "ABSY";

		if (edges) {
			cell_types["$mux"] = "*";
			cell_types["$pmux"] = "*";
		}

		// cell_types["$slice"] = "A";
		// cell_types["$concat"] = "A";

		cell_types["$lut"] = "*";
		cell_types["$sop"] = "*";
		cell_types["$alu"] = "ABSY";
		cell_types["$lcu"] = "*";
		cell_types["$macc"] = "*";
		cell_types["$fa"] = "*";

		for (; argidx < GetSize(args); argidx++)
		{
			if (args[argidx].rfind("-", 0) == 0)
				log_cmd_error("Unexpected option: %s\n", args[argidx].c_str());

			if (args[argidx] == "all") {
				for (auto &it : cell_types)
					if (std::count(selected_cell_types.begin(), selected_cell_types.end(), it.first) == 0)
						selected_cell_types.push_back(it.first);
				continue;
			}

			if (args[argidx].compare(0, 1, "/") == 0) {
				std::vector<std::string> new_selected_cell_types;
				for (auto it : selected_cell_types)
					if (it != args[argidx].substr(1))
						new_selected_cell_types.push_back(it);
				new_selected_cell_types.swap(selected_cell_types);
				continue;
			}

			if (cell_types.count(args[argidx]) == 0) {
				std::string cell_type_list;
				int charcount = 100;
				for (auto &it : cell_types) {
					if (charcount > 60) {
						cell_type_list += "\n" + it.first;
						charcount = 0;
					} else
						cell_type_list += " " + it.first;
					charcount += GetSize(it.first);
				}
				log_cmd_error("The cell type `%s' is currently not supported. Try one of these:%s\n",
						args[argidx].c_str(), cell_type_list.c_str());
			}

			if (std::count(selected_cell_types.begin(), selected_cell_types.end(), args[argidx]) == 0)
				selected_cell_types.push_back(args[argidx]);
		}

		if (!ilang_file.empty()) {
			if (!selected_cell_types.empty())
				log_cmd_error("Do not specify any cell types when using -f.\n");
			selected_cell_types.push_back("ilang");
		}

		if (selected_cell_types.empty())
			log_cmd_error("No cell type to test specified.\n");

		std::vector<std::string> uut_names;

		for (auto cell_type : selected_cell_types)
			for (int i = 0; i < num_iter; i++)
			{
				RTLIL::Design *design = new RTLIL::Design;
				if (cell_type == "ilang")
					Frontend::frontend_call(design, NULL, std::string(), "ilang " + ilang_file);
				else
					create_gold_module(design, cell_type, cell_types.at(cell_type), constmode, muxdiv);
				if (!write_prefix.empty()) {
					Pass::call(design, stringf("write_ilang %s_%s_%05d.il", write_prefix.c_str(), cell_type.c_str()+1, i));
				} else if (edges) {
					Pass::call(design, "dump gold");
					run_edges_test(design, verbose);
				} else {
					Pass::call(design, stringf("copy gold gate; cd gate; %s; cd ..; opt -fast gate", techmap_cmd.c_str()));
					if (!nosat)
						Pass::call(design, "miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter");
					if (verbose)
						Pass::call(design, "dump gate");
					Pass::call(design, "dump gold");
					if (!nosat)
						Pass::call(design, "sat -verify -enable_undef -prove trigger 0 -show-inputs -show-outputs miter");
					std::string uut_name = stringf("uut_%s_%d", cell_type.substr(1).c_str(), i);
					if (vlog_file.is_open()) {
						Pass::call(design, stringf("copy gold %s_expr; select %s_expr", uut_name.c_str(), uut_name.c_str()));
						Backend::backend_call(design, &vlog_file, "<test_cell -vlog>", "verilog -selected");
						Pass::call(design, stringf("copy gold %s_noexpr; select %s_noexpr", uut_name.c_str(), uut_name.c_str()));
						Backend::backend_call(design, &vlog_file, "<test_cell -vlog>", "verilog -selected -noexpr");
						uut_names.push_back(uut_name);
					}
					if (!noeval)
						run_eval_test(design, verbose, nosat, uut_name, vlog_file);
				}
				delete design;
			}

		if (vlog_file.is_open()) {
			vlog_file << "\nmodule testbench;\n";
			for (auto &uut : uut_names)
				vlog_file << stringf("  %s %s ();\n", uut.c_str(), uut.c_str());
			vlog_file << "  initial begin\n";
			for (auto &uut : uut_names)
				vlog_file << "    " << uut << ".run;\n";
			vlog_file << "  end\n";
			vlog_file << "endmodule\n";
		}
	}
} TestCellPass;

PRIVATE_NAMESPACE_END
