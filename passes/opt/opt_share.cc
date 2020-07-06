/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Bogdan Vukobratovic <bogdan.vukobratovic@gmail.com>
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

struct OpMuxConn {
	RTLIL::SigSpec sig;
	RTLIL::Cell *mux;
	RTLIL::Cell *op;
	int mux_port_id;
	int mux_port_offset;
	int op_outsig_offset;

	bool operator<(const OpMuxConn &other) const
	{
		if (mux != other.mux)
			return mux < other.mux;

		if (mux_port_id != other.mux_port_id)
			return mux_port_id < other.mux_port_id;

		return mux_port_offset < other.mux_port_offset;
	}
};

// Helper class to track additiona information about a SigSpec, like whether it is signed and the semantics of the port it is connected to
struct ExtSigSpec {
	RTLIL::SigSpec sig;
	RTLIL::SigSpec sign;
	bool is_signed;
	RTLIL::IdString semantics;

	ExtSigSpec() {}

	ExtSigSpec(RTLIL::SigSpec s, RTLIL::SigSpec sign = RTLIL::Const(0, 1), bool is_signed = false, RTLIL::IdString semantics = RTLIL::IdString()) : sig(s), sign(sign), is_signed(is_signed), semantics(semantics) {}

	bool empty() const { return sig.empty(); }

	bool operator<(const ExtSigSpec &other) const
	{
		if (sig != other.sig)
			return sig < other.sig;

		if (sign != other.sign)
			return sign < other.sign;

		if (is_signed != other.is_signed)
			return is_signed < other.is_signed;

		return semantics < other.semantics;
	}

	bool operator==(const RTLIL::SigSpec &other) const { return (sign != RTLIL::Const(0, 1)) ? false : sig == other; }
	bool operator==(const ExtSigSpec &other) const { return is_signed == other.is_signed && sign == other.sign && sig == other.sig && semantics == other.semantics; }
};

#define FINE_BITWISE_OPS ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_)

#define BITWISE_OPS FINE_BITWISE_OPS, ID($and), ID($or), ID($xor), ID($xnor)

#define REDUCTION_OPS ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($reduce_nand)

#define LOGICAL_OPS ID($logic_and), ID($logic_or)

#define SHIFT_OPS ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)

#define RELATIONAL_OPS ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt)

bool cell_supported(RTLIL::Cell *cell)
{
	if (cell->type.in(ID($alu))) {
		RTLIL::SigSpec sig_bi = cell->getPort(ID(BI));
		RTLIL::SigSpec sig_ci = cell->getPort(ID(CI));

		if (sig_bi.is_fully_const() && sig_ci.is_fully_const() && sig_bi == sig_ci)
			return true;
	} else if (cell->type.in(LOGICAL_OPS, SHIFT_OPS, BITWISE_OPS, RELATIONAL_OPS, ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($concat))) {
		return true;
	}

	return false;
}

std::map<IdString, IdString> mergeable_type_map;

bool mergeable(RTLIL::Cell *a, RTLIL::Cell *b)
{
	if (mergeable_type_map.empty()) {
		mergeable_type_map.insert({ID($sub), ID($add)});
	}
	auto a_type = a->type;
	if (mergeable_type_map.count(a_type))
		a_type = mergeable_type_map.at(a_type);

	auto b_type = b->type;
	if (mergeable_type_map.count(b_type))
		b_type = mergeable_type_map.at(b_type);

	return a_type == b_type;
}

RTLIL::IdString decode_port_semantics(RTLIL::Cell *cell, RTLIL::IdString port_name)
{
	if (cell->type.in(ID($lt), ID($le), ID($ge), ID($gt), ID($div), ID($mod), ID($concat), SHIFT_OPS) && port_name == ID::B)
		return port_name;

	return "";
}

RTLIL::SigSpec decode_port_sign(RTLIL::Cell *cell, RTLIL::IdString port_name) {

	if (cell->type == ID($alu) && port_name == ID::B)
		return cell->getPort(ID(BI));
	else if (cell->type == ID($sub) && port_name == ID::B)
		return RTLIL::Const(1, 1);

	return RTLIL::Const(0, 1);
}

bool decode_port_signed(RTLIL::Cell *cell, RTLIL::IdString port_name)
{
	if (cell->type.in(BITWISE_OPS, LOGICAL_OPS))
		return false;

	if (cell->hasParam(port_name.str() + "_SIGNED"))
		return cell->getParam(port_name.str() + "_SIGNED").as_bool();

	return false;
}

ExtSigSpec decode_port(RTLIL::Cell *cell, RTLIL::IdString port_name, SigMap *sigmap)
{
	auto sig = (*sigmap)(cell->getPort(port_name));

	RTLIL::SigSpec sign = decode_port_sign(cell, port_name);
	RTLIL::IdString semantics = decode_port_semantics(cell, port_name);

	bool is_signed = decode_port_signed(cell, port_name);

	return ExtSigSpec(sig, sign, is_signed, semantics);
}

void merge_operators(RTLIL::Module *module, RTLIL::Cell *mux, const std::vector<OpMuxConn> &ports, const ExtSigSpec &operand)
{
	std::vector<ExtSigSpec> muxed_operands;
	int max_width = 0;
	for (const auto& p : ports) {
		auto op = p.op;

		RTLIL::IdString muxed_port_name = ID::A;
		if (decode_port(op, ID::A, &assign_map) == operand)
			muxed_port_name = ID::B;

		auto operand = decode_port(op, muxed_port_name, &assign_map);
		if (operand.sig.size() > max_width)
			max_width = operand.sig.size();

		muxed_operands.push_back(operand);
	}

	auto shared_op = ports[0].op;

	if (std::any_of(muxed_operands.begin(), muxed_operands.end(), [&](ExtSigSpec &op) { return op.sign != muxed_operands[0].sign; }))
        max_width = std::max(max_width, shared_op->getParam(ID(Y_WIDTH)).as_int());


	for (auto &operand : muxed_operands)
		operand.sig.extend_u0(max_width, operand.is_signed);

	for (const auto& p : ports) {
		auto op = p.op;
		if (op == shared_op)
			continue;
		module->remove(op);
	}

	for (auto &muxed_op : muxed_operands)
		if (muxed_op.sign != muxed_operands[0].sign)
			muxed_op = ExtSigSpec(module->Neg(NEW_ID, muxed_op.sig, muxed_op.is_signed));

	RTLIL::SigSpec mux_y = mux->getPort(ID::Y);
	RTLIL::SigSpec mux_a = mux->getPort(ID::A);
	RTLIL::SigSpec mux_b = mux->getPort(ID::B);
	RTLIL::SigSpec mux_s = mux->getPort(ID(S));

	RTLIL::SigSpec shared_pmux_a = RTLIL::Const(RTLIL::State::Sx, max_width);
	RTLIL::SigSpec shared_pmux_b;
	RTLIL::SigSpec shared_pmux_s;

	int conn_width = ports[0].sig.size();
	int conn_offset = ports[0].mux_port_offset;

	shared_op->setPort(ID::Y, shared_op->getPort(ID::Y).extract(0, conn_width));

	if (mux->type == ID($pmux)) {
		shared_pmux_s = RTLIL::SigSpec();

		for (const auto &p : ports) {
			shared_pmux_s.append(mux_s[p.mux_port_id]);
			mux_b.replace(p.mux_port_id * mux_a.size() + conn_offset, shared_op->getPort(ID::Y));
		}
	} else {
		shared_pmux_s = RTLIL::SigSpec{mux_s, module->Not(NEW_ID, mux_s)};
		mux_a.replace(conn_offset, shared_op->getPort(ID::Y));
		mux_b.replace(conn_offset, shared_op->getPort(ID::Y));
	}

	mux->setPort(ID::A, mux_a);
	mux->setPort(ID::B, mux_b);
	mux->setPort(ID::Y, mux_y);
	mux->setPort(ID(S), mux_s);

	for (const auto &op : muxed_operands)
		shared_pmux_b.append(op.sig);

	auto mux_to_oper = module->Pmux(NEW_ID, shared_pmux_a, shared_pmux_b, shared_pmux_s);

	if (shared_op->type.in(ID($alu))) {
		RTLIL::SigSpec alu_x = shared_op->getPort(ID(X));
		RTLIL::SigSpec alu_co = shared_op->getPort(ID(CO));

		shared_op->setPort(ID(X), alu_x.extract(0, conn_width));
		shared_op->setPort(ID(CO), alu_co.extract(0, conn_width));
	}

	bool is_fine = shared_op->type.in(FINE_BITWISE_OPS);

	if (!is_fine)
		shared_op->setParam(ID(Y_WIDTH), conn_width);

	if (decode_port(shared_op, ID::A, &assign_map) == operand) {
		shared_op->setPort(ID::B, mux_to_oper);
		if (!is_fine)
			shared_op->setParam(ID(B_WIDTH), max_width);
	} else {
		shared_op->setPort(ID::A, mux_to_oper);
		if (!is_fine)
			shared_op->setParam(ID(A_WIDTH), max_width);
	}
}

typedef struct {
	RTLIL::Cell *mux;
	std::vector<OpMuxConn> ports;
	ExtSigSpec shared_operand;
} merged_op_t;


template <typename T> void remove_val(std::vector<T> &v, const std::vector<T> &vals)
{
	auto val_iter = vals.rbegin();
	for (auto i = v.rbegin(); i != v.rend(); ++i)
		if ((val_iter != vals.rend()) && (*i == *val_iter)) {
			v.erase(i.base() - 1);
			++val_iter;
		}
}

void check_muxed_operands(std::vector<const OpMuxConn *> &ports, const ExtSigSpec &shared_operand)
{
	auto it = ports.begin();
	ExtSigSpec seed;

	while (it != ports.end()) {
		auto p = *it;
		auto op = p->op;

		RTLIL::IdString muxed_port_name = ID::A;
		if (decode_port(op, ID::A, &assign_map) == shared_operand) {
			muxed_port_name = ID::B;
		}

		auto operand = decode_port(op, muxed_port_name, &assign_map);

		if (seed.empty())
			seed = operand;

		if (operand.is_signed != seed.is_signed) {
			ports.erase(it);
		} else {
			++it;
		}
	}
}

ExtSigSpec find_shared_operand(const OpMuxConn* seed, std::vector<const OpMuxConn *> &ports, const std::map<ExtSigSpec, std::set<RTLIL::Cell *>> &operand_to_users)
{
	std::set<RTLIL::Cell *> ops_using_operand;
	std::set<RTLIL::Cell *> ops_set;
	for(const auto& p: ports)
		ops_set.insert(p->op);

	ExtSigSpec oper;

	auto op_a = seed->op;

	for (RTLIL::IdString port_name : {ID::A, ID::B}) {
		oper = decode_port(op_a, port_name, &assign_map);
		auto operand_users = operand_to_users.at(oper);

		if (operand_users.size() == 1)
			continue;

		ops_using_operand.clear();
		for (auto mux_ops: ops_set)
			if (operand_users.count(mux_ops))
				ops_using_operand.insert(mux_ops);

		if (ops_using_operand.size() > 1) {
			ports.erase(std::remove_if(ports.begin(), ports.end(), [&](const OpMuxConn *p) { return !ops_using_operand.count(p->op); }),
						ports.end());
			return oper;
		}
	}

	return ExtSigSpec();
}

dict<RTLIL::SigSpec, OpMuxConn> find_valid_op_mux_conns(RTLIL::Module *module, dict<RTLIL::SigBit, RTLIL::SigSpec> &op_outbit_to_outsig,
							dict<RTLIL::SigSpec, RTLIL::Cell *> outsig_to_operator,
							dict<RTLIL::SigBit, RTLIL::SigSpec> &op_aux_to_outsig)
{
	dict<RTLIL::SigSpec, int> op_outsig_user_track;
	dict<RTLIL::SigSpec, OpMuxConn> op_mux_conn_map;

	std::function<void(RTLIL::SigSpec)> remove_outsig = [&](RTLIL::SigSpec outsig) {
		for (auto op_outbit : outsig)
			op_outbit_to_outsig.erase(op_outbit);

		if (op_mux_conn_map.count(outsig))
			op_mux_conn_map.erase(outsig);
	};

	std::function<void(RTLIL::SigBit)> remove_outsig_from_aux_bit = [&](RTLIL::SigBit auxbit) {
		auto aux_outsig = op_aux_to_outsig.at(auxbit);
		auto op = outsig_to_operator.at(aux_outsig);
		auto op_outsig = assign_map(op->getPort(ID::Y));
		remove_outsig(op_outsig);

		for (auto aux_outbit : aux_outsig)
			op_aux_to_outsig.erase(aux_outbit);
	};

	std::function<void(RTLIL::Cell *)> find_op_mux_conns = [&](RTLIL::Cell *mux) {
		RTLIL::SigSpec sig;
		int mux_port_size;

		if (mux->type.in(ID($mux), ID($_MUX_))) {
			mux_port_size = mux->getPort(ID::A).size();
			sig = RTLIL::SigSpec{mux->getPort(ID::B), mux->getPort(ID::A)};
		} else {
			mux_port_size = mux->getPort(ID::A).size();
			sig = mux->getPort(ID::B);
		}

		auto mux_insig = assign_map(sig);

		for (int i = 0; i < mux_insig.size(); ++i) {
			if (op_aux_to_outsig.count(mux_insig[i])) {
				remove_outsig_from_aux_bit(mux_insig[i]);
				continue;
			}

			if (!op_outbit_to_outsig.count(mux_insig[i]))
				continue;

			auto op_outsig = op_outbit_to_outsig.at(mux_insig[i]);

			if (op_mux_conn_map.count(op_outsig)) {
				remove_outsig(op_outsig);
				continue;
			}

			int mux_port_id = i / mux_port_size;
			int mux_port_offset = i % mux_port_size;

			int op_outsig_offset;
			for (op_outsig_offset = 0; op_outsig[op_outsig_offset] != mux_insig[i]; ++op_outsig_offset)
				;

			int j = op_outsig_offset;
			do {
				if (!op_outbit_to_outsig.count(mux_insig[i]))
					break;

				if (op_outbit_to_outsig.at(mux_insig[i]) != op_outsig)
					break;

				++i;
				++j;
			} while ((i / mux_port_size == mux_port_id) && (j < op_outsig.size()));

			int op_conn_width = j - op_outsig_offset;
			OpMuxConn inp = {
				op_outsig.extract(op_outsig_offset, op_conn_width),
				mux,
				outsig_to_operator.at(op_outsig),
				mux_port_id,
				mux_port_offset,
				op_outsig_offset,
			};

			op_mux_conn_map[op_outsig] = inp;

			--i;
		}
	};

	std::function<void(RTLIL::SigSpec)> remove_connected_ops = [&](RTLIL::SigSpec sig) {
		auto mux_insig = assign_map(sig);
		for (auto outbit : mux_insig) {
			if (op_aux_to_outsig.count(outbit)) {
				remove_outsig_from_aux_bit(outbit);
				continue;
			}

			if (!op_outbit_to_outsig.count(outbit))
				continue;

			remove_outsig(op_outbit_to_outsig.at(outbit));
		}
	};

	for (auto cell : module->cells()) {
		if (cell->type.in(ID($mux), ID($_MUX_), ID($pmux))) {
			remove_connected_ops(cell->getPort(ID(S)));
			find_op_mux_conns(cell);
		} else {
			for (auto &conn : cell->connections())
				if (cell->input(conn.first))
					remove_connected_ops(conn.second);
		}
	}

	for (auto w : module->wires()) {
		if (!w->port_output)
			continue;

		remove_connected_ops(w);
	}

	return op_mux_conn_map;
}

struct OptSharePass : public Pass {
	OptSharePass() : Pass("opt_share", "merge mutually exclusive cells of the same type that share an input signal") {}
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_share [selection]\n");
		log("\n");

		log("This pass identifies mutually exclusive cells of the same type that:\n");
		log("    (a) share an input signal,\n");
		log("    (b) drive the same $mux, $_MUX_, or $pmux multiplexing cell,\n");
		log("\n");
		log("allowing the cell to be merged and the multiplexer to be moved from\n");
		log("multiplexing its output to multiplexing the non-shared input signals.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{

		log_header(design, "Executing OPT_SHARE pass.\n");

		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			assign_map.clear();
			assign_map.set(module);

			std::map<ExtSigSpec, std::set<RTLIL::Cell *>> operand_to_users;
			dict<RTLIL::SigSpec, RTLIL::Cell *> outsig_to_operator;
			dict<RTLIL::SigBit, RTLIL::SigSpec> op_outbit_to_outsig;
			dict<RTLIL::SigBit, RTLIL::SigSpec> op_aux_to_outsig;
			bool any_shared_operands = false;
			std::vector<ExtSigSpec> op_insigs;

			for (auto cell : module->cells()) {
				if (!cell_supported(cell))
					continue;

				if (cell->type == ID($alu)) {
					for (RTLIL::IdString port_name : {ID(X), ID(CO)}) {
						auto mux_insig = assign_map(cell->getPort(port_name));
						outsig_to_operator[mux_insig] = cell;
						for (auto outbit : mux_insig)
							op_aux_to_outsig[outbit] = mux_insig;
					}
				}

				auto mux_insig = assign_map(cell->getPort(ID::Y));
				outsig_to_operator[mux_insig] = cell;
				for (auto outbit : mux_insig)
					op_outbit_to_outsig[outbit] = mux_insig;

				for (RTLIL::IdString port_name : {ID::A, ID::B}) {
					auto op_insig = decode_port(cell, port_name, &assign_map);
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
			dict<RTLIL::SigSpec, OpMuxConn> op_mux_conn_map =
			  find_valid_op_mux_conns(module, op_outbit_to_outsig, outsig_to_operator, op_aux_to_outsig);

			// Group op connections connected to same ports of the same $mux. Sort them in ascending order of their port offset
			dict<RTLIL::Cell*, std::vector<std::set<OpMuxConn>>> mux_port_op_conns;
			for (auto& val: op_mux_conn_map) {
				OpMuxConn p = val.second;
				auto& mux_port_conns = mux_port_op_conns[p.mux];

				if (mux_port_conns.size() == 0) {
					int mux_port_num;

					if (p.mux->type.in(ID($mux), ID($_MUX_)))
						mux_port_num = 2;
					else
						mux_port_num = p.mux->getPort(ID(S)).size();

					mux_port_conns.resize(mux_port_num);
				}

				mux_port_conns[p.mux_port_id].insert(p);
			}

			std::vector<merged_op_t> merged_ops;
			for (auto& val: mux_port_op_conns) {

				RTLIL::Cell* cell = val.first;
				auto &mux_port_conns = val.second;

				const OpMuxConn *seed = NULL;

				// Look through the bits of the $mux inputs and see which of them are connected to the operator
				// results. Operator results can be concatenated with other signals before led to the $mux.
				while (true) {

					// Remove either the merged ports from the last iteration or the seed that failed to yield a merger
					if (seed != NULL) {
						mux_port_conns[seed->mux_port_id].erase(*seed);
						seed = NULL;
					}

					// For a new merger, find the seed op connection that starts at lowest port offset among port connections
					for (auto &port_conns : mux_port_conns) {
						if (!port_conns.size())
							continue;

						const OpMuxConn *next_p = &(*port_conns.begin());

						if ((seed == NULL) || (seed->mux_port_offset > next_p->mux_port_offset))
							seed = next_p;
					}

					// Cannot find the seed -> nothing to do for this $mux anymore
					if (seed == NULL)
						break;

					// Find all other op connections that start from the same port offset, and whose ops can be merged with the seed op
					std::vector<const OpMuxConn *> mergeable_conns;
					for (auto &port_conns : mux_port_conns) {
						if (!port_conns.size())
							continue;

						const OpMuxConn *next_p = &(*port_conns.begin());

						if ((next_p->op_outsig_offset == seed->op_outsig_offset) &&
						    (next_p->mux_port_offset == seed->mux_port_offset) && mergeable(next_p->op, seed->op) &&
						    next_p->sig.size() == seed->sig.size())
							mergeable_conns.push_back(next_p);
					}

					// We need at least two mergeable connections for the merger
					if (mergeable_conns.size() < 2)
						continue;

					// Filter mergeable connections whose ops share an operand with seed connection's op
					auto shared_operand = find_shared_operand(seed, mergeable_conns, operand_to_users);

					if (shared_operand.empty())
						continue;

					check_muxed_operands(mergeable_conns, shared_operand);

					if (mergeable_conns.size() < 2)
						continue;

					// Remember the combination for the merger
					std::vector<OpMuxConn> merged_ports;
					for (auto p : mergeable_conns) {
						merged_ports.push_back(*p);
						mux_port_conns[p->mux_port_id].erase(*p);
					}

					seed = NULL;

					merged_ops.push_back(merged_op_t{cell, merged_ports, shared_operand});

					design->scratchpad_set_bool("opt.did_something", true);
				}

			}

			for (auto &shared : merged_ops) {
				log("    Found cells that share an operand and can be merged by moving the %s %s in front "
				    "of "
				    "them:\n",
				    log_id(shared.mux->type), log_id(shared.mux));
				for (const auto& op : shared.ports)
					log("        %s\n", log_id(op.op));
				log("\n");

				merge_operators(module, shared.mux, shared.ports, shared.shared_operand);
			}
		}
	}

} OptSharePass;

PRIVATE_NAMESPACE_END
