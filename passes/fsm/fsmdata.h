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

#ifndef FSMDATA_H
#define FSMDATA_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct FsmData
{
	int num_inputs, num_outputs, state_bits, reset_state;
	struct transition_t { int state_in, state_out; RTLIL::Const ctrl_in, ctrl_out; };
	std::vector<transition_t> transition_table;
	std::vector<RTLIL::Const> state_table;

	void copy_to_cell(RTLIL::Cell *cell)
	{
		cell->parameters[ID::CTRL_IN_WIDTH] = RTLIL::Const(num_inputs);
		cell->parameters[ID::CTRL_OUT_WIDTH] = RTLIL::Const(num_outputs);

		int state_num_log2 = 0;
		for (int i = state_table.size(); i > 0; i = i >> 1)
			state_num_log2++;
		state_num_log2 = max(state_num_log2, 1);

		cell->parameters[ID::STATE_BITS] = RTLIL::Const(state_bits);
		cell->parameters[ID::STATE_NUM] = RTLIL::Const(state_table.size());
		cell->parameters[ID::STATE_NUM_LOG2] = RTLIL::Const(state_num_log2);
		cell->parameters[ID::STATE_RST] = RTLIL::Const(reset_state);
		cell->parameters[ID::STATE_TABLE] = RTLIL::Const();

		for (int i = 0; i < int(state_table.size()); i++) {
			std::vector<RTLIL::State> &bits_table = cell->parameters[ID::STATE_TABLE].bits;
			std::vector<RTLIL::State> &bits_state = state_table[i].bits;
			bits_table.insert(bits_table.end(), bits_state.begin(), bits_state.end());
		}

		cell->parameters[ID::TRANS_NUM] = RTLIL::Const(transition_table.size());
		cell->parameters[ID::TRANS_TABLE] = RTLIL::Const();
		for (int i = 0; i < int(transition_table.size()); i++)
		{
			std::vector<RTLIL::State> &bits_table = cell->parameters[ID::TRANS_TABLE].bits;
			transition_t &tr = transition_table[i];

			RTLIL::Const const_state_in = RTLIL::Const(tr.state_in, state_num_log2);
			RTLIL::Const const_state_out = RTLIL::Const(tr.state_out, state_num_log2);
			std::vector<RTLIL::State> &bits_state_in = const_state_in.bits;
			std::vector<RTLIL::State> &bits_state_out = const_state_out.bits;

			std::vector<RTLIL::State> &bits_ctrl_in = tr.ctrl_in.bits;
			std::vector<RTLIL::State> &bits_ctrl_out = tr.ctrl_out.bits;

			// append lsb first
			bits_table.insert(bits_table.end(), bits_ctrl_out.begin(), bits_ctrl_out.end());
			bits_table.insert(bits_table.end(), bits_state_out.begin(), bits_state_out.end());
			bits_table.insert(bits_table.end(), bits_ctrl_in.begin(), bits_ctrl_in.end());
			bits_table.insert(bits_table.end(), bits_state_in.begin(), bits_state_in.end());
		}
	}

	void copy_from_cell(RTLIL::Cell *cell)
	{
		num_inputs = cell->parameters[ID::CTRL_IN_WIDTH].as_int();
		num_outputs = cell->parameters[ID::CTRL_OUT_WIDTH].as_int();

		state_bits = cell->parameters[ID::STATE_BITS].as_int();
		reset_state = cell->parameters[ID::STATE_RST].as_int();

		int state_num = cell->parameters[ID::STATE_NUM].as_int();
		int state_num_log2 = cell->parameters[ID::STATE_NUM_LOG2].as_int();
		int trans_num = cell->parameters[ID::TRANS_NUM].as_int();

		if (reset_state < 0 || reset_state >= state_num)
			reset_state = -1;

		RTLIL::Const state_table = cell->parameters[ID::STATE_TABLE];
		RTLIL::Const trans_table = cell->parameters[ID::TRANS_TABLE];

		for (int i = 0; i < state_num; i++) {
			RTLIL::Const state_code;
			int off_begin = i*state_bits, off_end = off_begin + state_bits;
			state_code.bits.insert(state_code.bits.begin(), state_table.bits.begin()+off_begin, state_table.bits.begin()+off_end);
			this->state_table.push_back(state_code);
		}

		for (int i = 0; i < trans_num; i++)
		{
			auto off_ctrl_out = trans_table.bits.begin() + i*(num_inputs+num_outputs+2*state_num_log2);
			auto off_state_out = off_ctrl_out + num_outputs;
			auto off_ctrl_in = off_state_out + state_num_log2;
			auto off_state_in = off_ctrl_in + num_inputs;
			auto off_end = off_state_in + state_num_log2;

			RTLIL::Const state_in, state_out, ctrl_in, ctrl_out;
			ctrl_out.bits.insert(state_in.bits.begin(), off_ctrl_out, off_state_out);
			state_out.bits.insert(state_out.bits.begin(), off_state_out, off_ctrl_in);
			ctrl_in.bits.insert(ctrl_in.bits.begin(), off_ctrl_in, off_state_in);
			state_in.bits.insert(state_in.bits.begin(), off_state_in, off_end);

			transition_t tr;
			tr.state_in = state_in.as_int();
			tr.state_out = state_out.as_int();
			tr.ctrl_in = ctrl_in;
			tr.ctrl_out = ctrl_out;

			if (tr.state_in < 0 || tr.state_in >= state_num)
				tr.state_in = -1;
			if (tr.state_out < 0 || tr.state_out >= state_num)
				tr.state_out = -1;

			transition_table.push_back(tr);
		}
	}

	void log_info(RTLIL::Cell *cell)
	{
		log("-------------------------------------\n");
		log("\n");
		log("  Information on FSM %s (%s):\n", cell->name.c_str(), cell->parameters[ID::NAME].decode_string().c_str());
		log("\n");
		log("  Number of input signals:  %3d\n", num_inputs);
		log("  Number of output signals: %3d\n", num_outputs);
		log("  Number of state bits:     %3d\n", state_bits);

		log("\n");
		log("  Input signals:\n");
		RTLIL::SigSpec sig_in = cell->getPort(ID::CTRL_IN);
		for (int i = 0; i < GetSize(sig_in); i++)
			log("  %3d: %s\n", i, log_signal(sig_in[i]));

		log("\n");
		log("  Output signals:\n");
		RTLIL::SigSpec sig_out = cell->getPort(ID::CTRL_OUT);
		for (int i = 0; i < GetSize(sig_out); i++)
			log("  %3d: %s\n", i, log_signal(sig_out[i]));

		log("\n");
		log("  State encoding:\n");
		for (int i = 0; i < GetSize(state_table); i++)
			log("  %3d: %10s%s\n", i, log_signal(state_table[i], false),
					int(i) == reset_state ? "  <RESET STATE>" : "");

		log("\n");
		log("  Transition Table (state_in, ctrl_in, state_out, ctrl_out):\n");
		for (int i = 0; i < GetSize(transition_table); i++) {
			transition_t &tr = transition_table[i];
			log("  %5d: %5d %s   -> %5d %s\n", i, tr.state_in, log_signal(tr.ctrl_in), tr.state_out, log_signal(tr.ctrl_out));
		}

		log("\n");
		log("-------------------------------------\n");
	}

	// implemented in fsm_opt.cc
	static void optimize_fsm(RTLIL::Cell *cell, RTLIL::Module *module);
};

YOSYS_NAMESPACE_END

#endif
