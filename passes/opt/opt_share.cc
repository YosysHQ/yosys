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

struct InPort {
	RTLIL::SigSpec sig;
	RTLIL::Cell *pmux;
	int port_id;
	RTLIL::Cell *alu;

	InPort(RTLIL::SigSpec s, RTLIL::Cell *c, int p, RTLIL::Cell *a = NULL) : sig(s), pmux(c), port_id(p), alu(a) {}
};

// Helper class that to track whether a SigSpec is signed and whether it is
// connected to the \\B port of the $sub cell, which makes its sign prefix
// negative.
struct ExtSigSpec {
	RTLIL::SigSpec sig;
	RTLIL::SigSpec sign;
	bool is_signed;

	ExtSigSpec() {}

	ExtSigSpec(RTLIL::SigSpec s, bool sign = false, bool is_signed = false) : sig(s), sign(sign), is_signed(is_signed) {}

	ExtSigSpec(RTLIL::Cell *cell, RTLIL::IdString port_name, SigMap *sigmap)
	{
		sign = (port_name == "\\B") ? cell->getPort("\\BI") : RTLIL::Const(0, 1);
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

	bool operator==(const RTLIL::SigSpec &other) const { return (sign != RTLIL::Const(0, 1)) ? false : sig == other; }
	bool operator==(const ExtSigSpec &other) const { return is_signed == other.is_signed && sign == other.sign && sig == other.sig; }
};

void merge_operators(RTLIL::Module *module, RTLIL::Cell *mux, const std::vector<InPort> &ports, int offset, int width,
		     const ExtSigSpec &operand)
{

	std::vector<ExtSigSpec> muxed_operands;
	int max_width = 0;
	for (const auto& p : ports) {
		auto op = p.alu;

		for (RTLIL::IdString port_name : {"\\A", "\\B"}) {
			if (op->getPort(port_name) != operand.sig) {
				auto operand = ExtSigSpec(op, port_name, &assign_map);
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

	auto shared_op = ports[0].alu;

	for (const auto& p : ports) {
		auto op = p.alu;
		if (op == shared_op)
			continue;
		module->remove(op);
	}

	for (auto &muxed_op : muxed_operands) {
		if (muxed_op.sign != muxed_operands[0].sign) {
			muxed_op = ExtSigSpec(module->Neg(NEW_ID, muxed_op.sig, muxed_op.is_signed));
		}
	}

	RTLIL::SigSpec mux_y = mux->getPort("\\Y");
	RTLIL::SigSpec mux_a = mux->getPort("\\A");
	RTLIL::SigSpec mux_b = mux->getPort("\\B");
	RTLIL::SigSpec mux_s = mux->getPort("\\S");

	RTLIL::SigSpec alu_x = shared_op->getPort("\\X");
	RTLIL::SigSpec alu_co = shared_op->getPort("\\CO");

	RTLIL::SigSpec shared_pmux_a = RTLIL::Const(RTLIL::State::Sx, max_width);
	RTLIL::SigSpec shared_pmux_b;
	RTLIL::SigSpec shared_pmux_s;

	shared_op->setPort("\\Y", shared_op->getPort("\\Y").extract(0, width));

	if (mux->type == "$pmux") {
		shared_pmux_s = RTLIL::SigSpec();

		for (const auto&p: ports) {
			shared_pmux_s.append(mux_s[p.port_id]);
			mux_b.replace(p.port_id * mux_a.size() + offset, shared_op->getPort("\\Y"));
		}
	} else {
		shared_pmux_s = RTLIL::SigSpec{mux_s, module->Not(NEW_ID, mux_s)};
		mux_a.replace(offset, shared_op->getPort("\\Y"));
		mux_b.replace(offset, shared_op->getPort("\\Y"));
	}

	mux->setPort("\\Y", mux_y);
	mux->setPort("\\S", mux_s);
	mux->setPort("\\B", mux_b);

	for (const auto &op : muxed_operands)
		shared_pmux_b.append(op.sig);

	auto mux_to_oper = module->Pmux(NEW_ID, shared_pmux_a, shared_pmux_b, shared_pmux_s);

	shared_op->setPort("\\X", alu_x.extract(0, width));
	shared_op->setPort("\\CO", alu_co.extract(0, width));
	shared_op->setParam("\\Y_WIDTH", width);

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
	std::vector<InPort> ports;
	int offset;
	int width;
	ExtSigSpec shared_operand;
} shared_op_t;


template <typename T> void remove_val(std::vector<T> &v, const std::vector<T> &vals)
{
	auto val_iter = vals.rbegin();
	for (auto i = v.rbegin(); i != v.rend(); ++i)
		if ((val_iter != vals.rend()) && (*i == *val_iter)) {
			v.erase(i.base() - 1);
			++val_iter;
		}
}

bool find_op_res_width(int offset, int &width, std::vector<InPort*>& ports, const dict<RTLIL::SigBit, RTLIL::SigSpec> &op_outbit_to_outsig)
{

	std::vector<RTLIL::SigSpec> op_outsigs;
	dict<int, std::set<InPort*>> op_outsig_span;

	std::transform(ports.begin(), ports.end(), std::back_inserter(op_outsigs), [&](InPort *p) { return op_outbit_to_outsig.at(p->sig[offset]); });

	std::vector<bool> finished(ports.size(), false);

	width = 0;

	std::function<bool()> all_finished = [&] { return std::find(std::begin(finished), std::end(finished), false) == end(finished);};

	while (!all_finished())
	{
		++offset;
		++width;

		if (offset >= ports[0]->sig.size()) {
			for (size_t i = 0; i < op_outsigs.size(); ++i) {
				if (finished[i])
					continue;

				op_outsig_span[width].insert(ports[i]);
				finished[i] = true;
			}

			break;
		}

		for (size_t i = 0; i < op_outsigs.size(); ++i) {
			if (finished[i])
				continue;

			if ((width >= op_outsigs[i].size()) || (ports[i]->sig[offset] != op_outsigs[i][width])) {
				op_outsig_span[width].insert(ports[i]);
				finished[i] = true;
			}
		}
	}

	for (auto w: op_outsig_span) {
		if (w.second.size() > 1) {
			width = w.first;

			ports.erase(std::remove_if(ports.begin(), ports.end(), [&](InPort *p) { return !w.second.count(p); }), ports.end());

			return true;
		}
	}

	return false;
}

ExtSigSpec find_shared_operand(InPort* seed, std::vector<InPort *> &ports, const std::map<ExtSigSpec, std::set<RTLIL::Cell *>> &operand_to_users)
{
	std::set<RTLIL::Cell *> alus_using_operand;
	std::set<RTLIL::Cell *> alus_set;
	for(const auto& p: ports)
		alus_set.insert(p->alu);

	ExtSigSpec oper;

	auto op_a = seed->alu;

	for (RTLIL::IdString port_name : {"\\A", "\\B"}) {
		oper = ExtSigSpec(op_a, port_name, &assign_map);
		auto operand_users = operand_to_users.at(oper);

		if (operand_users.size() == 1)
			continue;

		alus_using_operand.clear();
		std::set_intersection(operand_users.begin(), operand_users.end(), alus_set.begin(), alus_set.end(),
				      std::inserter(alus_using_operand, alus_using_operand.begin()));

		if (alus_using_operand.size() > 1) {
			ports.erase(std::remove_if(ports.begin(), ports.end(), [&](InPort *p) { return !alus_using_operand.count(p->alu); }),
				    ports.end());
			return oper;
		}
	}

	return ExtSigSpec();
}

void remove_multi_user_outbits(RTLIL::Module *module, dict<RTLIL::SigBit, RTLIL::SigSpec> &op_outbit_to_outsig)
{
	dict<RTLIL::SigBit, int> op_outbit_user_cnt;

	std::function<void(SigSpec)> update_op_outbit_user_cnt = [&](SigSpec sig) {
		auto outsig = assign_map(sig);
		for (auto outbit : outsig) {
			if (!op_outbit_to_outsig.count(outbit))
				continue;

			if (++op_outbit_user_cnt[outbit] > 1) {
				auto alu_outsig = op_outbit_to_outsig.at(outbit);

				for (auto outbit : alu_outsig)
					op_outbit_to_outsig.erase(outbit);
			}
		}
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
			std::vector<ExtSigSpec> op_insigs;

			for (auto cell : module->cells()) {
				if (!cell->type.in("$alu"))
					continue;

				RTLIL::SigSpec sig_bi = cell->getPort("\\BI");
				RTLIL::SigSpec sig_ci = cell->getPort("\\CI");

				if ((!sig_bi.is_fully_const()) || (!sig_ci.is_fully_const()) || (sig_bi != sig_ci))
					continue;

				RTLIL::SigSpec sig_y = cell->getPort("\\A");

				auto outsig = assign_map(cell->getPort("\\Y"));
				outsig_to_operator[outsig] = cell;
				for (auto outbit : outsig)
					op_outbit_to_outsig[outbit] = outsig;

				for (RTLIL::IdString port_name : {"\\A", "\\B"}) {
					auto op_insig = ExtSigSpec(cell, port_name, &assign_map);
					op_insigs.push_back(op_insig);
					operand_to_users[op_insig].insert(cell);
					if (operand_to_users[op_insig].size() > 1)
						any_shared_operands = true;
				}
			}

			if (!any_shared_operands)
				continue;

			// Operator outputs need to be exclusively connected to the $mux inputs in order to be mergeable. Hence we count to
			// how many points are operator output bits connected.
			remove_multi_user_outbits(module, op_outbit_to_outsig);

			std::vector<shared_op_t> shared_ops;
			for (auto cell : module->cells()) {
				if (!cell->type.in("$mux", "$_MUX_", "$pmux"))
					continue;

				RTLIL::SigSpec sig_a = cell->getPort("\\A");
				RTLIL::SigSpec sig_b = cell->getPort("\\B");
				RTLIL::SigSpec sig_s = cell->getPort("\\S");

				std::vector<InPort> ports;

				if (cell->type.in("$mux", "$_MUX_")) {
					ports.push_back(InPort(assign_map(sig_a), cell, 0));
					ports.push_back(InPort(assign_map(sig_b), cell, 1));
				} else {
					RTLIL::SigSpec sig_s = cell->getPort("\\S");
					for (int i = 0; i < sig_s.size(); i++) {
						auto inp = sig_b.extract(i * sig_a.size(), sig_a.size());
						ports.push_back(InPort(assign_map(inp), cell, i));
					}
				}

				// Look through the bits of the $mux inputs and see which of them are connected to the operator
				// results. Operator results can be concatenated with other signals before led to the $mux.
				for (int i = 0; i < sig_a.size(); ++i) {
					std::vector<InPort*> alu_ports;
					for (auto& p: ports)
						if (op_outbit_to_outsig.count(p.sig[i])) {
							p.alu = outsig_to_operator.at(op_outbit_to_outsig.at(p.sig[i]));
							alu_ports.push_back(&p);
						}

					int alu_port_width = 0;

					while (alu_ports.size() > 1) {
						std::vector<InPort*> shared_ports(alu_ports);

						auto seed = alu_ports[0];
						alu_ports.erase(alu_ports.begin());

						// Find ports whose $alu-s share an operand with $alu connected to the seed port
						auto shared_operand = find_shared_operand(seed, shared_ports, operand_to_users);

						if (shared_operand.empty())
							continue;

						// Some bits of the operator results might be unconnected. Calculate the number of conneted
						// bits.
						if (!find_op_res_width(i, alu_port_width, shared_ports, op_outbit_to_outsig))
							break;

						if (shared_ports.size() < 2)
							break;

						// Remember the combination for the merger
						std::vector<InPort> shared_p;
						for (auto p: shared_ports)
							shared_p.push_back(*p);

						shared_ops.push_back(shared_op_t{cell, shared_p, i, alu_port_width, shared_operand});

						// Remove merged ports from the list and try to find other mergers for the mux
						remove_val(alu_ports, shared_ports);
					}

					if (alu_port_width)
						i += alu_port_width - 1;
				}

			}

			for (auto &shared : shared_ops) {
				log("    Found arithmetic cells that share an operand and can be merged by moving the %s %s in front "
				    "of "
				    "them:\n",
				    log_id(shared.mux->type), log_id(shared.mux));
				for (const auto& op : shared.ports)
					log("        %s\n", log_id(op.alu));
				log("\n");

				merge_operators(module, shared.mux, shared.ports, shared.offset, shared.width, shared.shared_operand);
			}
		}
	}

} OptRmdffPass;

PRIVATE_NAMESPACE_END
