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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include <algorithm>

#include <stdio.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

SigMap assign_map;

// Helper class that to track whether a SigSpec is signed and whether it is
// connected to the \\B port of the $sub cell, which makes its sign prefix
// negative.
struct ExtSigSpec {
	RTLIL::SigSpec sig;
	bool sign;
	bool is_signed;

	ExtSigSpec() {}

	ExtSigSpec(RTLIL::SigSpec s, bool sign = false, bool is_signed = false) : sig(s), sign(sign), is_signed(is_signed) {}

	ExtSigSpec(RTLIL::Cell *cell, RTLIL::IdString port_name, SigMap *sigmap)
	{
		sign = (cell->type == "$sub") && (port_name == "\\B");
		sig = (*sigmap)(cell->getPort(port_name));

		is_signed = false;
		if (cell->hasParam(port_name.str() + "_SIGNED")) {
			is_signed = cell->getParam(port_name.str() + "_SIGNED").as_bool();
		}
	}

	bool empty() const { return sig.empty(); }

	bool operator<(const ExtSigSpec &other) const
	{
		if (sig != other.sig)
			return sig < other.sig;

		if (sign != other.sign)
			return sign < other.sign;

		return is_signed < other.is_signed;
	}

	bool operator==(const RTLIL::SigSpec &other) const { return sign ? false : sig == other; }
	bool operator==(const ExtSigSpec &other) const { return is_signed == other.is_signed && sign == other.sign && sig == other.sig; }
};

void merge_operators(RTLIL::Module *module, RTLIL::Cell *mux, const std::vector<RTLIL::Cell *> &operators, int offset, int width,
		     const ExtSigSpec &operand)
{

	std::vector<ExtSigSpec> muxed_operands;
	int max_width = 0;
	for (auto op : operators) {
		for (auto &conn : op->connections()) {
			if (op->output(conn.first))
				continue;

			if (conn.second != operand.sig) {
				auto operand = ExtSigSpec(op, conn.first, &assign_map);
				if (operand.sig.size() > max_width) {
					max_width = operand.sig.size();
				}

				muxed_operands.push_back(operand);
			}
		}
	}

	for (auto &operand : muxed_operands) {
		operand.sig.extend_u0(max_width, operand.is_signed);
	}

	auto shared_op = operators[0];

	for (auto op : operators) {
		if (op == shared_op)
			continue;
		module->remove(op);
	}

	RTLIL::SigSpec mux_out = mux->getPort("\\Y");

	if (muxed_operands[0].sign != muxed_operands[1].sign) {
		muxed_operands[1] = ExtSigSpec(module->Neg(NEW_ID, muxed_operands[1].sig, muxed_operands[1].is_signed));
	}

	auto mux_to_oper = module->Mux(NEW_ID, muxed_operands[0].sig, muxed_operands[1].sig, mux->getPort("\\S"));

	shared_op->setPort("\\Y", mux_out.extract(offset, width));
	shared_op->setParam("\\Y_WIDTH", width);

	auto dummy = module->addWire(NEW_ID, width);

	mux_out.replace(offset, dummy);
	mux->setPort("\\Y", mux_out);

	if (shared_op->getPort("\\A") == operand.sig) {
		shared_op->setPort("\\B", mux_to_oper);
		shared_op->setParam("\\B_WIDTH", max_width);
	} else {
		shared_op->setPort("\\A", mux_to_oper);
		shared_op->setParam("\\A_WIDTH", max_width);
	}
}

typedef struct {
	RTLIL::Cell *mux;
	std::vector<RTLIL::Cell *> operators;
	int offset;
	int width;
	ExtSigSpec shared_operand;
} shared_op_t;

bool find_op_res_width(int offset, int &width, RTLIL::SigSpec porta, RTLIL::SigSpec portb,
		       const dict<RTLIL::SigBit, RTLIL::SigSpec> &op_outbit_to_outsig, const dict<RTLIL::SigBit, int> &op_outbit_user_cnt)
{

	std::array<RTLIL::SigSpec, 2> op_outsigs{op_outbit_to_outsig.at(porta[offset]), op_outbit_to_outsig.at(portb[offset])};

	width = 0;
	bool multi_user = false;

	while (true) {
		for (const auto &op_outsig : op_outsigs)
			if (op_outbit_user_cnt.at(op_outsig[width]) > 1)
				multi_user = true;

		++offset;
		++width;

		if ((offset >= porta.size()) || (width >= op_outsigs[0].size()) || (width >= op_outsigs[1].size()))
			break;

		if ((porta[offset] != op_outsigs[0][width]) || (portb[offset] != op_outsigs[1][width]))
			break;
	}

	if (multi_user)
		return false;

	for (const auto &outsig : op_outsigs)
		for (int i = width; i < outsig.size(); i++)
			if (op_outbit_user_cnt.count(outsig[i]))
				return false;

	return true;
}

ExtSigSpec find_shared_operand(const std::vector<RTLIL::Cell *> &operators, const std::map<ExtSigSpec, std::set<RTLIL::Cell *>> &operand_to_users)
{

	std::set<RTLIL::Cell *> operators_set(operators.begin(), operators.end());
	ExtSigSpec oper;

	auto op_a = operators[0];
	for (auto &conn : op_a->connections()) {
		if (op_a->output(conn.first))
			continue;

		oper = ExtSigSpec(op_a, conn.first, &assign_map);
		auto bundle = operand_to_users.at(oper);

		if (std::includes(bundle.begin(), bundle.end(), operators_set.begin(), operators_set.end()))
			break;
	}

	return oper;
}

dict<RTLIL::SigBit, int> find_op_outbit_user_cnt(RTLIL::Module *module, const dict<RTLIL::SigBit, RTLIL::SigSpec> &op_outbit_to_outsig)
{
	dict<RTLIL::SigBit, int> op_outbit_user_cnt;

	std::function<void(SigSpec)> update_op_outbit_user_cnt = [&](SigSpec sig) {
		auto outsig = assign_map(sig);
		for (auto outbit : outsig)
			if (op_outbit_to_outsig.count(outbit))
				op_outbit_user_cnt[outbit]++;
	};

	for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->input(conn.first))
				update_op_outbit_user_cnt(conn.second);

	for (auto w : module->wires()) {
		if (!w->port_output)
			continue;

		update_op_outbit_user_cnt(w);
	}

	return op_outbit_user_cnt;
}

struct OptRmdffPass : public Pass {
	OptRmdffPass() : Pass("opt_share", "merge arithmetic operators that share an operand") {}
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_share [selection]\n");
		log("\n");
		log("This pass identifies arithmetic operators that share an operand and whose\n");
		log("results are used in mutually exclusive cases controlled by a multiplexer,\n");
		log("and merges them together by multiplexing the other operands.\n");
		log("\n");
	}
	void execute(std::vector<std::string>, RTLIL::Design *design) YS_OVERRIDE
	{

		log_header(design, "Executing OPT_SHARE pass.\n");

		for (auto module : design->selected_modules()) {
			assign_map.clear();
			assign_map.set(module);

			std::map<ExtSigSpec, std::set<RTLIL::Cell *>> operand_to_users;
			dict<RTLIL::SigSpec, RTLIL::Cell *> outsig_to_operator;
			dict<RTLIL::SigBit, RTLIL::SigSpec> op_outbit_to_outsig;
			bool any_shared_operands = false;

			for (auto cell : module->cells()) {
				if (!cell->type.in("$add", "$sub"))
					continue;

				for (auto &conn : cell->connections()) {
					if (cell->output(conn.first)) {
						auto outsig = assign_map(conn.second);
						for (auto outbit : outsig)
							op_outbit_to_outsig[outbit] = outsig;

						outsig_to_operator[outsig] = cell;
					} else {
						auto op_insig = ExtSigSpec(cell, conn.first, &assign_map);
						operand_to_users[op_insig].insert(cell);
						if (operand_to_users[op_insig].size() > 1)
							any_shared_operands = true;
					}
				}
			}

			if (!any_shared_operands)
				continue;

			// Operator outputs need to be exclusively connected to the $mux inputs in order to be mergeable. Hence we count to
			// how many points are operator output bits connected.
			dict<RTLIL::SigBit, int> op_outbit_user_cnt = find_op_outbit_user_cnt(module, op_outbit_to_outsig);
			std::vector<shared_op_t> shared_ops;
			for (auto cell : module->cells()) {
				if (!cell->type.in("$mux", "$_MUX_"))
					continue;

				auto porta = assign_map(cell->getPort("\\A"));
				auto portb = assign_map(cell->getPort("\\B"));

				// Look through the bits of the $mux inputs and see which of them are connected to the operator
				// results. Operator results can be concatenated with other signals before led to the $mux.
				for (int i = 0; i < porta.size(); ++i) {
					std::array<RTLIL::SigBit, 2> mux_inbits{porta[i], portb[i]};

					// Are the results of an $add or $sub operators connected to both of this $mux inputs?
					if (!op_outbit_to_outsig.count(mux_inbits[0]) or !op_outbit_to_outsig.count(mux_inbits[1]))
						continue;

					std::vector<RTLIL::Cell *> operators;
					for (const auto &b : mux_inbits)
						operators.push_back(outsig_to_operator.at(op_outbit_to_outsig.at(b)));

					// Do these operators share an operand?
					auto shared_operand = find_shared_operand(operators, operand_to_users);
					if (shared_operand.empty())
						continue;

					// Some bits of the operator results might be unconnected. Calculate the number of conneted
					// bits.
					int width;

					if (find_op_res_width(i, width, porta, portb, op_outbit_to_outsig, op_outbit_user_cnt))
						shared_ops.push_back(shared_op_t{cell, operators, i, width, shared_operand});

					i += width - 1;
				}
			}

			for (auto &shared : shared_ops) {
				log("    Found arithmetic cells that share an operand and can be merged by moving the %s %s in front "
				    "of "
				    "them:\n",
				    log_id(shared.mux->type), log_id(shared.mux));
				for (auto op : shared.operators)
					log("        %s\n", log_id(op));
				log("\n");

				merge_operators(module, shared.mux, shared.operators, shared.offset, shared.width, shared.shared_operand);
			}
		}
	}

} OptRmdffPass;

PRIVATE_NAMESPACE_END
