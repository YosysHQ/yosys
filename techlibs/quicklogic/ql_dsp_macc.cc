/*
 * Copyright 2020-2022 F4PGA Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 */

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "ql_dsp_macc_pm.h"

// ============================================================================

bool use_dsp_cfg_params;

static void create_ql_macc_dsp(ql_dsp_macc_pm &pm)
{
	auto &st = pm.st_ql_dsp_macc;

	// Reject if multiplier drives anything else than either $add or $add and
	// $mux
	if (st.mux == nullptr && st.mul_nusers > 2) {
		return;
	}

	// Determine whether the output is taken from before or after the ff
	bool out_ff;
	if (st.ff_d_nusers == 2 && st.ff_q_nusers == 3) {
		out_ff = true;
	} else if (st.ff_d_nusers == 3 && st.ff_q_nusers == 2) {
		out_ff = false;
	} else {
		// Illegal, cannot take the two outputs simulataneously
		return;
	}

	// No mux, the adder can driver either the ff or the ff + output
	if (st.mux == nullptr) {
		if (out_ff && st.add_nusers != 2) {
			return;
		}
		if (!out_ff && st.add_nusers != 3) {
			return;
		}
	}
	// Mux present, the adder cannot drive anything else
	else {
		if (st.add_nusers != 2) {
			return;
		}
	}

	// Mux can driver either the ff or the ff + output
	if (st.mux != nullptr) {
		if (out_ff && st.mux_nusers != 2) {
			return;
		}
		if (!out_ff && st.mux_nusers != 3) {
			return;
		}
	}

	// Accept only posedge clocked FFs
	if (st.ff->getParam(ID(CLK_POLARITY)).as_int() != 1) {
		return;
	}

	// Get port widths
	size_t a_width = GetSize(st.mul->getPort(ID(A)));
	size_t b_width = GetSize(st.mul->getPort(ID(B)));
	size_t z_width = GetSize(st.ff->getPort(ID(Q)));

	size_t min_width = std::min(a_width, b_width);
	size_t max_width = std::max(a_width, b_width);

	// Signed / unsigned
	bool a_signed = st.mul->getParam(ID(A_SIGNED)).as_bool();
	bool b_signed = st.mul->getParam(ID(B_SIGNED)).as_bool();

	// Determine DSP type or discard if too narrow / wide
	RTLIL::IdString type;
	size_t tgt_a_width;
	size_t tgt_b_width;
	size_t tgt_z_width;

	string cell_base_name = "dsp_t1";
	string cell_size_name = "";
	string cell_cfg_name = "";
	string cell_full_name = "";

	if (min_width <= 2 && max_width <= 2 && z_width <= 4) {
		// Too narrow
		return;
	} else if (min_width <= 9 && max_width <= 10 && z_width <= 19) {
		cell_size_name = "_10x9x32";
		tgt_a_width = 10;
		tgt_b_width = 9;
		tgt_z_width = 19;
	} else if (min_width <= 18 && max_width <= 20 && z_width <= 38) {
		cell_size_name = "_20x18x64";
		tgt_a_width = 20;
		tgt_b_width = 18;
		tgt_z_width = 38;
	} else {
		// Too wide
		return;
	}

	if (use_dsp_cfg_params)
		cell_cfg_name = "_cfg_params";
	else
		cell_cfg_name = "_cfg_ports";

	cell_full_name = cell_base_name + cell_size_name + cell_cfg_name;

	type = RTLIL::escape_id(cell_full_name);
	log("Inferring MACC %zux%zu->%zu as %s from:\n", a_width, b_width, z_width, RTLIL::unescape_id(type).c_str());

	for (auto cell : {st.mul, st.add, st.mux, st.ff}) {
		if (cell != nullptr) {
			log(" %s (%s)\n", RTLIL::unescape_id(cell->name).c_str(), RTLIL::unescape_id(cell->type).c_str());
		}
	}

	// Build the DSP cell name
	std::string name;
	name += RTLIL::unescape_id(st.mul->name) + "_";
	name += RTLIL::unescape_id(st.add->name) + "_";
	if (st.mux != nullptr) {
		name += RTLIL::unescape_id(st.mux->name) + "_";
	}
	name += RTLIL::unescape_id(st.ff->name);

	// Add the DSP cell
	RTLIL::Cell *cell = pm.module->addCell(RTLIL::escape_id(name), type);

	// Set attributes
	cell->set_bool_attribute(RTLIL::escape_id("is_inferred"), true);

	// Get input/output data signals
	RTLIL::SigSpec sig_a;
	RTLIL::SigSpec sig_b;
	RTLIL::SigSpec sig_z;

	if (a_width >= b_width) {
		sig_a = st.mul->getPort(ID(A));
		sig_b = st.mul->getPort(ID(B));
	} else {
		sig_a = st.mul->getPort(ID(B));
		sig_b = st.mul->getPort(ID(A));
	}

	sig_z = out_ff ? st.ff->getPort(ID(Q)) : st.ff->getPort(ID(D));

	// Connect input data ports, sign extend / pad with zeros
	sig_a.extend_u0(tgt_a_width, a_signed);
	sig_b.extend_u0(tgt_b_width, b_signed);
	cell->setPort(RTLIL::escape_id("a_i"), sig_a);
	cell->setPort(RTLIL::escape_id("b_i"), sig_b);

	// Connect output data port, pad if needed
	if ((size_t)GetSize(sig_z) < tgt_z_width) {
		auto *wire = pm.module->addWire(NEW_ID, tgt_z_width - GetSize(sig_z));
		sig_z.append(wire);
	}
	cell->setPort(RTLIL::escape_id("z_o"), sig_z);

	// Connect clock, reset and enable
	cell->setPort(RTLIL::escape_id("clock_i"), st.ff->getPort(ID(CLK)));

	RTLIL::SigSpec rst;
	RTLIL::SigSpec ena;

	if (st.ff->hasPort(ID(ARST))) {
		if (st.ff->getParam(ID(ARST_POLARITY)).as_int() != 1) {
			rst = pm.module->Not(NEW_ID, st.ff->getPort(ID(ARST)));
		} else {
			rst = st.ff->getPort(ID(ARST));
		}
	} else {
		rst = RTLIL::SigSpec(RTLIL::S0);
	}

	if (st.ff->hasPort(ID(EN))) {
		if (st.ff->getParam(ID(EN_POLARITY)).as_int() != 1) {
			ena = pm.module->Not(NEW_ID, st.ff->getPort(ID(EN)));
		} else {
			ena = st.ff->getPort(ID(EN));
		}
	} else {
		ena = RTLIL::SigSpec(RTLIL::S1);
	}

	cell->setPort(RTLIL::escape_id("reset_i"), rst);
	cell->setPort(RTLIL::escape_id("load_acc_i"), ena);

	// Insert feedback_i control logic used for clearing / loading the accumulator
	if (st.mux != nullptr) {
		RTLIL::SigSpec sig_s = st.mux->getPort(ID(S));

		// Depending on the mux port ordering insert inverter if needed
		log_assert(st.mux_ab == ID(A) || st.mux_ab == ID(B));
		if (st.mux_ab == ID(A)) {
			sig_s = pm.module->Not(NEW_ID, sig_s);
		}

		// Assemble the full control signal for the feedback_i port
		RTLIL::SigSpec sig_f;
		sig_f.append(sig_s);
		sig_f.append(RTLIL::S0);
		sig_f.append(RTLIL::S0);
		cell->setPort(RTLIL::escape_id("feedback_i"), sig_f);
	}
	// No acc clear/load
	else {
		cell->setPort(RTLIL::escape_id("feedback_i"), RTLIL::SigSpec(RTLIL::S0, 3));
	}

	// Connect control ports
	cell->setPort(RTLIL::escape_id("unsigned_a_i"), RTLIL::SigSpec(a_signed ? RTLIL::S0 : RTLIL::S1));
	cell->setPort(RTLIL::escape_id("unsigned_b_i"), RTLIL::SigSpec(b_signed ? RTLIL::S0 : RTLIL::S1));

	// Connect config bits
	if (use_dsp_cfg_params) {
		cell->setParam(RTLIL::escape_id("SATURATE_ENABLE"), RTLIL::Const(RTLIL::S0));
		cell->setParam(RTLIL::escape_id("SHIFT_RIGHT"), RTLIL::Const(RTLIL::S0, 6));
		cell->setParam(RTLIL::escape_id("ROUND"), RTLIL::Const(RTLIL::S0));
		cell->setParam(RTLIL::escape_id("REGISTER_INPUTS"), RTLIL::Const(RTLIL::S0));
		// 3 - output post acc; 1 - output pre acc
		cell->setParam(RTLIL::escape_id("OUTPUT_SELECT"), out_ff ? RTLIL::Const(1, 3) : RTLIL::Const(3, 3));
	} else {
		cell->setPort(RTLIL::escape_id("saturate_enable_i"), RTLIL::SigSpec(RTLIL::S0));
		cell->setPort(RTLIL::escape_id("shift_right_i"), RTLIL::SigSpec(RTLIL::S0, 6));
		cell->setPort(RTLIL::escape_id("round_i"), RTLIL::SigSpec(RTLIL::S0));
		cell->setPort(RTLIL::escape_id("register_inputs_i"), RTLIL::SigSpec(RTLIL::S0));
		// 3 - output post acc; 1 - output pre acc
		cell->setPort(RTLIL::escape_id("output_select_i"), out_ff ? RTLIL::Const(1, 3) : RTLIL::Const(3, 3));
	}

	bool subtract = (st.add->type == RTLIL::escape_id("$sub"));
	cell->setPort(RTLIL::escape_id("subtract_i"), RTLIL::SigSpec(subtract ? RTLIL::S1 : RTLIL::S0));

	// Mark the cells for removal
	pm.autoremove(st.mul);
	pm.autoremove(st.add);
	if (st.mux != nullptr) {
		pm.autoremove(st.mux);
	}
	pm.autoremove(st.ff);
}

struct QlDspMacc : public Pass {

	QlDspMacc() : Pass("ql_dsp_macc", "Does something") {}

	void help() override
	{
		log("\n");
		log("    ql_dsp_macc [options] [selection]\n");
		log("\n");
		log("    -use_dsp_cfg_params\n");
		log("        By default use DSP blocks with configuration bits available at module ports.\n");
		log("        Specifying this forces usage of DSP block with configuration bits available as module parameters\n");
		log("\n");
	}

	void clear_flags() override { use_dsp_cfg_params = false; }

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_MACC pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < a_Args.size(); argidx++) {
			if (a_Args[argidx] == "-use_dsp_cfg_params") {
				use_dsp_cfg_params = true;
				continue;
			}

			break;
		}
		extra_args(a_Args, argidx, a_Design);

		for (auto module : a_Design->selected_modules()) {
			ql_dsp_macc_pm(module, module->selected_cells()).run_ql_dsp_macc(create_ql_macc_dsp);
		}
	}

} QlDspMacc;

PRIVATE_NAMESPACE_END
