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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct proc_dlatch_db_t
{
	Module *module;
	SigMap sigmap;

	dict<SigBit, pair<Cell*, int>> mux_drivers;
	dict<SigBit, int> sigusers;

	proc_dlatch_db_t(Module *module) : module(module), sigmap(module)
	{
		for (auto cell : module->cells())
		{
			if (cell->type.in("$mux", "$pmux")) {
				auto sig_y = sigmap(cell->getPort("\\Y"));
				for (int i = 0; i < GetSize(sig_y); i++)
					mux_drivers[sig_y[i]] = pair<Cell*, int>(cell, i);
			}

			for (auto &conn : cell->connections())
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigusers[bit]++;
		}

		for (auto wire : module->wires())
			if (wire->port_input)
				for (auto bit : sigmap(wire))
					sigusers[bit]++;
	}

	struct rule_node_t
	{
		// a node is true if "signal" equals "match" and [any
		// of the child nodes is true or "children" is empty]
		SigBit signal, match;
		vector<int> children;

		bool operator==(const rule_node_t &other) const {
			return signal == other.signal && match == other.match && children == other.children;
		}

		unsigned int hash() const {
			unsigned int h = mkhash_init;
			mkhash(h, signal.hash());
			mkhash(h, match.hash());
			for (auto i : children) mkhash(h, i);
			return h;
		}
	};

	enum tf_node_types_t : int {
		true_node = 1,
		false_node = 2
	};

	idict<rule_node_t, 3> rules_db;
	dict<int, SigBit> rules_sig;

	int make_leaf(SigBit signal, SigBit match)
	{
		rule_node_t node;
		node.signal = signal;
		node.match = match;
		return rules_db(node);
	}

	int make_inner(SigBit signal, SigBit match, int child)
	{
		rule_node_t node;
		node.signal = signal;
		node.match = match;
		node.children.push_back(child);
		return rules_db(node);
	}

	int make_inner(const pool<int> &children)
	{
		rule_node_t node;
		node.signal = State::S0;
		node.match = State::S0;
		node.children = vector<int>(children.begin(), children.end());
		std::sort(node.children.begin(), node.children.end());
		return rules_db(node);
	}

	int find_mux_feedback(SigBit haystack, SigBit needle, bool set_undef)
	{
		if (sigusers[haystack] > 1)
			set_undef = false;

		if (haystack == needle)
			return true_node;

		auto it = mux_drivers.find(haystack);
		if (it == mux_drivers.end())
			return false_node;

		Cell *cell = it->second.first;
		int index = it->second.second;

		SigSpec sig_a = sigmap(cell->getPort("\\A"));
		SigSpec sig_b = sigmap(cell->getPort("\\B"));
		SigSpec sig_s = sigmap(cell->getPort("\\S"));
		int width = GetSize(sig_a);

		pool<int> children;

		int n = find_mux_feedback(sig_a[index], needle, set_undef);
		if (n != false_node) {
			if (set_undef && sig_a[index] == needle) {
				SigSpec sig = cell->getPort("\\A");
				sig[index] = State::Sx;
				cell->setPort("\\A", sig);
			}
			for (int i = 0; i < GetSize(sig_s); i++)
				n = make_inner(sig_s[i], State::S0, n);
			children.insert(n);
		}

		for (int i = 0; i < GetSize(sig_s); i++) {
			n = find_mux_feedback(sig_b[i*width + index], needle, set_undef);
			if (n != false_node) {
				if (set_undef && sig_b[i*width + index] == needle) {
					SigSpec sig = cell->getPort("\\B");
					sig[i*width + index] = State::Sx;
					cell->setPort("\\B", sig);
				}
				children.insert(make_inner(sig_s[i], State::S1, n));
			}
		}

		if (children.empty())
			return false_node;

		return make_inner(children);
	}

	SigBit make_hold(int n)
	{
		if (n == true_node)
			return State::S1;

		if (n == false_node)
			return State::S0;

		if (rules_sig.count(n))
			return rules_sig.at(n);

		const rule_node_t &rule = rules_db[n];
		SigSpec and_bits;

		if (rule.signal != rule.match) {
			if (rule.match == State::S1)
				and_bits.append(rule.signal);
			else if (rule.match == State::S0)
				and_bits.append(module->Not(NEW_ID, rule.signal));
			else
				and_bits.append(module->Eq(NEW_ID, rule.signal, rule.match));
		}

		if (!rule.children.empty()) {
			SigSpec or_bits;
			for (int k : rule.children)
				or_bits.append(make_hold(k));
			and_bits.append(module->ReduceOr(NEW_ID, or_bits));
		}

		if (GetSize(and_bits) == 2)
			and_bits = module->And(NEW_ID, and_bits[0], and_bits[1]);
		log_assert(GetSize(and_bits) == 1);

		rules_sig[n] = and_bits[0];
		return and_bits[0];
	}
};

void proc_dlatch(proc_dlatch_db_t &db, RTLIL::Process *proc)
{
	std::vector<RTLIL::SyncRule*> new_syncs;
	RTLIL::SigSig latches_bits, nolatches_bits;
	dict<SigBit, SigBit> latches_out_in;
	dict<SigBit, int> latches_hold;

	for (auto sr : proc->syncs)
	{
		if (sr->type != RTLIL::SyncType::STa) {
			new_syncs.push_back(sr);
			continue;
		}

		for (auto ss : sr->actions) {
			db.sigmap.apply(ss.first);
			db.sigmap.apply(ss.second);
			for (int i = 0; i < GetSize(ss.first); i++)
				latches_out_in[ss.first[i]] = ss.second[i];
		}

		delete sr;
	}

	latches_out_in.sort();
	for (auto &it : latches_out_in) {
		int n = db.find_mux_feedback(it.second, it.first, true);
		if (n == db.false_node) {
			nolatches_bits.first.append(it.first);
			nolatches_bits.second.append(it.second);
		} else {
			latches_bits.first.append(it.first);
			latches_bits.second.append(it.second);
			latches_hold[it.first] = n;
		}
	}

	int offset = 0;
	for (auto chunk : nolatches_bits.first.chunks()) {
		SigSpec lhs = chunk, rhs = nolatches_bits.second.extract(offset, chunk.width);
		log("No latch inferred for signal `%s.%s' from process `%s.%s'.\n",
				db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str());
		db.module->connect(lhs, rhs);
		offset += chunk.width;
	}

	offset = 0;
	while (offset < GetSize(latches_bits.first))
	{
		int width = 1;
		int n = latches_hold[latches_bits.first[offset]];
		Wire *w = latches_bits.first[offset].wire;

		if (w != nullptr)
		{
			while (offset+width < GetSize(latches_bits.first) &&
					n == latches_hold[latches_bits.first[offset+width]] &&
					w == latches_bits.first[offset+width].wire)
				width++;

			SigSpec lhs = latches_bits.first.extract(offset, width);
			SigSpec rhs = latches_bits.second.extract(offset, width);

			Cell *cell = db.module->addDlatch(NEW_ID, db.module->Not(NEW_ID, db.make_hold(n)), rhs, lhs);
			log("Latch inferred for signal `%s.%s' from process `%s.%s': %s\n",
					db.module->name.c_str(), log_signal(lhs), db.module->name.c_str(), proc->name.c_str(), log_id(cell));
		}

		offset += width;
	}

	new_syncs.swap(proc->syncs);
}

struct ProcDlatchPass : public Pass {
	ProcDlatchPass() : Pass("proc_dlatch", "extract latches from processes") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_dlatch [selection]\n");
		log("\n");
		log("This pass identifies latches in the processes and converts them to\n");
		log("d-type latches.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing PROC_DLATCH pass (convert process syncs to latches).\n");

		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			proc_dlatch_db_t db(module);
			for (auto &proc_it : module->processes)
				if (design->selected(module, proc_it.second))
					proc_dlatch(db, proc_it.second);
		}
	}
} ProcDlatchPass;

PRIVATE_NAMESPACE_END
