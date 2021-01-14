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
		RTLIL::SigSpec sig_bi = cell->getPort(ID::BI);
		RTLIL::SigSpec sig_ci = cell->getPort(ID::CI);

		if (sig_bi.is_fully_const() && sig_ci.is_fully_const() && sig_bi == sig_ci)
			return true;
	} else if (cell->type.in(LOGICAL_OPS, SHIFT_OPS, BITWISE_OPS, RELATIONAL_OPS, ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($concat))) {
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
	if (cell->type.in(ID($lt), ID($le), ID($ge), ID($gt), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($concat), SHIFT_OPS) && port_name == ID::B)
		return port_name;

	return "";
}

RTLIL::SigSpec decode_port_sign(RTLIL::Cell *cell, RTLIL::IdString port_name) {

	if (cell->type == ID($alu) && port_name == ID::B)
		return cell->getPort(ID::BI);
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

ExtSigSpec decode_port(RTLIL::Cell *cell, RTLIL::IdString port_name, const SigMap &sigmap)
{
	auto sig = sigmap(cell->getPort(port_name));

	RTLIL::SigSpec sign = decode_port_sign(cell, port_name);
	RTLIL::IdString semantics = decode_port_semantics(cell, port_name);

	bool is_signed = decode_port_signed(cell, port_name);

	return ExtSigSpec(sig, sign, is_signed, semantics);
}

void merge_operators(RTLIL::Module *module, RTLIL::Cell *mux, const std::vector<OpMuxConn> &ports, const ExtSigSpec &operand, const SigMap &sigmap)
{
	std::vector<ExtSigSpec> muxed_operands;
	int max_width = 0;
	for (const auto& p : ports) {
		auto op = p.op;

		RTLIL::IdString muxed_port_name = ID::A;
		if (decode_port(op, ID::A, sigmap) == operand)
			muxed_port_name = ID::B;

		auto operand = decode_port(op, muxed_port_name, sigmap);
		if (operand.sig.size() > max_width)
			max_width = operand.sig.size();

		muxed_operands.push_back(operand);
	}

	auto shared_op = ports[0].op;

	if (std::any_of(muxed_operands.begin(), muxed_operands.end(), [&](ExtSigSpec &op) { return op.sign != muxed_operands[0].sign; }))
		max_width = std::max(max_width, shared_op->getParam(ID::Y_WIDTH).as_int());

	for (auto &operand : muxed_operands) {
		operand.sig.extend_u0(max_width, operand.is_signed);
		if (operand.sign != muxed_operands[0].sign)
			operand = ExtSigSpec(module->Neg(NEW_ID, operand.sig, operand.is_signed));
	}

	for (const auto& p : ports) {
		auto op = p.op;
		if (op == shared_op)
			continue;
		module->remove(op);
	}

	RTLIL::SigSpec mux_a = mux->getPort(ID::A);
	RTLIL::SigSpec mux_b = mux->getPort(ID::B);
	RTLIL::SigSpec mux_s = mux->getPort(ID::S);

	int conn_width = ports[0].sig.size();
	int conn_mux_offset = ports[0].mux_port_offset;
	int conn_op_offset = ports[0].op_outsig_offset;

	RTLIL::SigSpec shared_pmux_a = RTLIL::Const(RTLIL::State::Sx, max_width);
	RTLIL::SigSpec shared_pmux_b;
	RTLIL::SigSpec shared_pmux_s;

	// Make a new wire to avoid false equivalence with whatever the former shared output was connected to.
	Wire *new_out = module->addWire(NEW_ID, conn_op_offset + conn_width);
	SigSpec new_sig_out = SigSpec(new_out, conn_op_offset, conn_width);

	for (int i = 0; i < GetSize(ports); i++) {
		auto &p = ports[i];
		auto &op = muxed_operands[i];
		if (p.mux_port_id == GetSize(mux_s)) {
			shared_pmux_a = op.sig;
			mux_a.replace(conn_mux_offset, new_sig_out);
		} else {
			shared_pmux_s.append(mux_s[p.mux_port_id]);
			shared_pmux_b.append(op.sig);
			mux_b.replace(p.mux_port_id * mux_a.size() + conn_mux_offset, new_sig_out);
		}
	}

	mux->setPort(ID::A, mux_a);
	mux->setPort(ID::B, mux_b);
	mux->setPort(ID::S, mux_s);

	SigSpec mux_to_oper;
	if (GetSize(shared_pmux_s) == 1) {
		mux_to_oper = module->Mux(NEW_ID, shared_pmux_a, shared_pmux_b, shared_pmux_s);
	} else {
		mux_to_oper = module->Pmux(NEW_ID, shared_pmux_a, shared_pmux_b, shared_pmux_s);
	}

	if (shared_op->type.in(ID($alu))) {
		shared_op->setPort(ID::X, module->addWire(NEW_ID, GetSize(new_out)));
		shared_op->setPort(ID::CO, module->addWire(NEW_ID, GetSize(new_out)));
	}

	bool is_fine = shared_op->type.in(FINE_BITWISE_OPS);

	shared_op->setPort(ID::Y, new_out);
	if (!is_fine)
		shared_op->setParam(ID::Y_WIDTH, GetSize(new_out));

	if (decode_port(shared_op, ID::A, sigmap) == operand) {
		shared_op->setPort(ID::B, mux_to_oper);
		if (!is_fine)
			shared_op->setParam(ID::B_WIDTH, max_width);
	} else {
		shared_op->setPort(ID::A, mux_to_oper);
		if (!is_fine)
			shared_op->setParam(ID::A_WIDTH, max_width);
	}
}

typedef struct {
	RTLIL::Cell *mux;
	std::vector<OpMuxConn> ports;
	ExtSigSpec shared_operand;
} merged_op_t;


void check_muxed_operands(std::vector<const OpMuxConn *> &ports, const ExtSigSpec &shared_operand, const SigMap &sigmap)
{
	auto it = ports.begin();
	ExtSigSpec seed;

	while (it != ports.end()) {
		auto p = *it;
		auto op = p->op;

		RTLIL::IdString muxed_port_name = ID::A;
		if (decode_port(op, ID::A, sigmap) == shared_operand) {
			muxed_port_name = ID::B;
		}

		auto operand = decode_port(op, muxed_port_name, sigmap);

		if (seed.empty())
			seed = operand;

		if (operand.is_signed != seed.is_signed) {
			ports.erase(it);
		} else {
			++it;
		}
	}
}

ExtSigSpec find_shared_operand(const OpMuxConn* seed, std::vector<const OpMuxConn *> &ports, const std::map<ExtSigSpec, std::set<RTLIL::Cell *>> &operand_to_users, const SigMap &sigmap)
{
	std::set<RTLIL::Cell *> ops_using_operand;
	std::set<RTLIL::Cell *> ops_set;
	for(const auto& p: ports)
		ops_set.insert(p->op);

	ExtSigSpec oper;

	auto op_a = seed->op;

	for (RTLIL::IdString port_name : {ID::A, ID::B}) {
		oper = decode_port(op_a, port_name, sigmap);
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

struct OptSharePass : public Pass {
	OptSharePass() : Pass("opt_share", "merge mutually exclusive cells of the same type that share an input signal") {}
	void help() override
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{

		log_header(design, "Executing OPT_SHARE pass.\n");

		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);

			dict<RTLIL::SigBit, int> bit_users;

			for (auto cell : module->cells())
				for (auto conn : cell->connections())
					for (auto bit : conn.second)
						bit_users[sigmap(bit)]++;

			for (auto wire : module->wires())
				if (wire->port_id != 0)
					for (auto bit : SigSpec(wire))
						bit_users[sigmap(bit)]++;

			std::map<ExtSigSpec, std::set<RTLIL::Cell *>> operand_to_users;
			dict<RTLIL::SigBit, std::pair<RTLIL::Cell *, int>> op_outbit_to_outsig;
			bool any_shared_operands = false;

			for (auto cell : module->selected_cells()) {
				if (!cell_supported(cell))
					continue;

				bool skip = false;
				if (cell->type == ID($alu)) {
					for (RTLIL::IdString port_name : {ID::X, ID::CO}) {
						for (auto outbit : sigmap(cell->getPort(port_name)))
							if (bit_users[outbit] > 1)
								skip = true;
					}
				}

				if (skip)
					continue;

				auto mux_insig = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(mux_insig); i++)
					op_outbit_to_outsig[mux_insig[i]] = std::make_pair(cell, i);

				for (RTLIL::IdString port_name : {ID::A, ID::B}) {
					auto op_insig = decode_port(cell, port_name, sigmap);
					operand_to_users[op_insig].insert(cell);
					if (operand_to_users[op_insig].size() > 1)
						any_shared_operands = true;
				}
			}

			if (!any_shared_operands)
				continue;

			// Operator outputs need to be exclusively connected to the $mux inputs in order to be mergeable. Hence we count to
			// how many points are operator output bits connected.
			std::vector<merged_op_t> merged_ops;

			for (auto mux : module->selected_cells()) {
				if (!mux->type.in(ID($mux), ID($_MUX_), ID($pmux)))
					continue;

				int mux_port_size = GetSize(mux->getPort(ID::A));
				int mux_port_num = GetSize(mux->getPort(ID::S)) + 1;

				RTLIL::SigSpec mux_insig = sigmap(RTLIL::SigSpec{mux->getPort(ID::B), mux->getPort(ID::A)});
				std::vector<std::set<OpMuxConn>> mux_port_conns(mux_port_num);
				int found = 0;

				for (int mux_port_id = 0; mux_port_id < mux_port_num; mux_port_id++) {
					SigSpec mux_insig;
					if (mux_port_id == mux_port_num - 1) {
						mux_insig = sigmap(mux->getPort(ID::A));
					} else {
						mux_insig = sigmap(mux->getPort(ID::B).extract(mux_port_id * mux_port_size, mux_port_size));
					}

					for (int mux_port_offset = 0; mux_port_offset < mux_port_size; ++mux_port_offset) {
						if (!op_outbit_to_outsig.count(mux_insig[mux_port_offset]))
							continue;

						RTLIL::Cell *cell;
						int op_outsig_offset;
						std::tie(cell, op_outsig_offset) = op_outbit_to_outsig.at(mux_insig[mux_port_offset]);
						SigSpec op_outsig = sigmap(cell->getPort(ID::Y));
						int op_outsig_size = GetSize(op_outsig);
						int op_conn_width = 0;

						while (mux_port_offset + op_conn_width < mux_port_size &&
								op_outsig_offset + op_conn_width < op_outsig_size &&
								mux_insig[mux_port_offset + op_conn_width] == op_outsig[op_outsig_offset + op_conn_width])
							op_conn_width++; 

						log_assert(op_conn_width >= 1);

						bool skip = false;
						for (int i = 0; i < op_outsig_size; i++) {
							int expected = 1;
							if (i >= op_outsig_offset && i < op_outsig_offset + op_conn_width)
								expected = 2;
							if (bit_users[op_outsig[i]] != expected)
								skip = true;
						}
						if (skip) {
							mux_port_offset += op_conn_width;
							mux_port_offset--;
							continue;
						}

						OpMuxConn inp = {
							op_outsig.extract(op_outsig_offset, op_conn_width),
							mux,
							cell,
							mux_port_id,
							mux_port_offset,
							op_outsig_offset,
						};

						mux_port_conns[mux_port_id].insert(inp);

						mux_port_offset += op_conn_width;
						mux_port_offset--;

						found++;
					}
				}

				if (found < 2)
					continue;

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
					auto shared_operand = find_shared_operand(seed, mergeable_conns, operand_to_users, sigmap);

					if (shared_operand.empty())
						continue;

					check_muxed_operands(mergeable_conns, shared_operand, sigmap);

					if (mergeable_conns.size() < 2)
						continue;

					// Remember the combination for the merger
					std::vector<OpMuxConn> merged_ports;
					for (auto p : mergeable_conns) {
						merged_ports.push_back(*p);
						mux_port_conns[p->mux_port_id].erase(*p);
					}

					seed = NULL;

					merged_ops.push_back(merged_op_t{mux, merged_ports, shared_operand});

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

				merge_operators(module, shared.mux, shared.ports, shared.shared_operand, sigmap);
			}
		}
	}

} OptSharePass;

PRIVATE_NAMESPACE_END
