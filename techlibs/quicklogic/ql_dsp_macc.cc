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

#include "techlibs/quicklogic/ql_dsp_macc_pm.h"

// ============================================================================

static void create_ql_macc_dsp(ql_dsp_macc_pm &pm)
{
    auto &st = pm.st_ql_dsp_macc;

    // Get port widths
    size_t a_width = GetSize(st.mul->getPort(ID(A)));
    size_t b_width = GetSize(st.mul->getPort(ID(B)));
    size_t z_width = GetSize(st.ff->getPort(ID(Q)));

    size_t min_width = std::min(a_width, b_width);
    size_t max_width = std::max(a_width, b_width);

    // Signed / unsigned
    bool ab_signed = st.mul->getParam(ID(A_SIGNED)).as_bool();
    log_assert(ab_signed == st.mul->getParam(ID(B_SIGNED)).as_bool());

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
        log_debug("\trejected: too narrow (%zd %zd %zd)\n", min_width, max_width, z_width);
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
        log_debug("\trejected: too wide (%zd %zd %zd)\n", min_width, max_width, z_width);
        return;
    }

    type = RTLIL::escape_id(cell_base_name + cell_size_name + "_cfg_ports");
    log("Inferring MACC %zux%zu->%zu as %s from:\n", a_width, b_width, z_width, log_id(type));

    for (auto cell : {st.mul, st.add, st.mux, st.ff})
    if (cell)
        log("  %s (%s)\n", log_id(cell), log_id(cell->type));

    // Add the DSP cell
    RTLIL::Cell *cell = pm.module->addCell(NEW_ID, type);

    // Set attributes
    cell->set_bool_attribute(ID(is_inferred), true);

    // Get input/output data signals
    RTLIL::SigSpec sig_a, sig_b, sig_z;
    sig_a = st.mul->getPort(ID(A));
    sig_b = st.mul->getPort(ID(B));
    sig_z = st.output_registered ? st.ff->getPort(ID(Q)) : st.ff->getPort(ID(D));

    if (a_width < b_width)
        std::swap(sig_a, sig_b);

    // Connect input data ports, sign extend / pad with zeros
    sig_a.extend_u0(tgt_a_width, ab_signed);
    sig_b.extend_u0(tgt_b_width, ab_signed);
    cell->setPort(ID(a_i), sig_a);
    cell->setPort(ID(b_i), sig_b);

    // Connect output data port, pad if needed
    if ((size_t) GetSize(sig_z) < tgt_z_width) {
        auto *wire = pm.module->addWire(NEW_ID, tgt_z_width - GetSize(sig_z));
        sig_z.append(wire);
    }
    cell->setPort(ID(z_o), sig_z);

    // Connect clock, reset and enable
    cell->setPort(ID(clock_i), st.ff->getPort(ID(CLK)));

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

    cell->setPort(ID(reset_i), rst);
    cell->setPort(ID(load_acc_i), ena);

    // Insert feedback_i control logic used for clearing / loading the accumulator
    if (st.mux_in_pattern) {
        RTLIL::SigSpec sig_s = st.mux->getPort(ID(S));

        // Depending on the mux port ordering insert inverter if needed
        log_assert(st.mux_ab.in(ID(A), ID(B)));
        if (st.mux_ab == ID(A))
            sig_s = pm.module->Not(NEW_ID, sig_s);

        // Assemble the full control signal for the feedback_i port
        RTLIL::SigSpec sig_f;
        sig_f.append(sig_s);
        sig_f.append(RTLIL::S0);
        sig_f.append(RTLIL::S0);
        cell->setPort(ID(feedback_i), sig_f);
    }
    // No acc clear/load
    else {
        cell->setPort(ID(feedback_i), RTLIL::SigSpec(RTLIL::S0, 3));
    }

    // Connect control ports
    cell->setPort(ID(unsigned_a_i), RTLIL::SigSpec(ab_signed ? RTLIL::S0 : RTLIL::S1));
    cell->setPort(ID(unsigned_b_i), RTLIL::SigSpec(ab_signed ? RTLIL::S0 : RTLIL::S1));

    // Connect config bits
    cell->setPort(ID(saturate_enable_i), RTLIL::SigSpec(RTLIL::S0));
    cell->setPort(ID(shift_right_i), RTLIL::SigSpec(RTLIL::S0, 6));
    cell->setPort(ID(round_i), RTLIL::SigSpec(RTLIL::S0));
    cell->setPort(ID(register_inputs_i), RTLIL::SigSpec(RTLIL::S0));
    // 3 - output post acc; 1 - output pre acc
    cell->setPort(ID(output_select_i), RTLIL::Const(st.output_registered ? 1 : 3, 3));

    bool subtract = (st.add->type == ID($sub));
    cell->setPort(ID(subtract_i), RTLIL::SigSpec(subtract ? RTLIL::S1 : RTLIL::S0));

    // Mark the cells for removal
    pm.autoremove(st.mul);
    pm.autoremove(st.add);
    if (st.mux != nullptr) {
        pm.autoremove(st.mux);
    }
    pm.autoremove(st.ff);
}

struct QlDspMacc : public Pass {
	QlDspMacc() : Pass("ql_dsp_macc", "infer QuickLogic multiplier-accumulator DSP cells") {}

	void help() override
	{
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_dsp_macc [selection]\n");
        log("\n");
        log("This pass looks for a multiply-accumulate pattern based on which it infers a\n");
        log("QuickLogic DSP cell.\n");
		log("\n");
	}

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_MACC pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < a_Args.size(); argidx++) {
			break;
		}
		extra_args(a_Args, argidx, a_Design);

		for (auto module : a_Design->selected_modules())
			ql_dsp_macc_pm(module, module->selected_cells()).run_ql_dsp_macc(create_ql_macc_dsp);
	}

} QlDspMacc;

PRIVATE_NAMESPACE_END
