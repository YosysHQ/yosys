/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/bitpattern.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SigSnippets
{
	idict<SigSpec> sigidx;
	dict<SigBit, int> bit2snippet;
	pool<int> snippets;

	void insert(SigSpec sig)
	{
		if (sig.empty())
			return;

		int key = sigidx(sig);
		if (snippets.count(key))
			return;

		SigSpec new_sig;

		for (int i = 0; i < GetSize(sig); i++)
		{
			int other_key = bit2snippet.at(sig[i], -1);

			if (other_key < 0) {
				new_sig.append(sig[i]);
				continue;
			}

			if (!new_sig.empty()) {
				int new_key = sigidx(new_sig);
				snippets.insert(new_key);
				for (auto bit : new_sig)
					bit2snippet[bit] = new_key;
				new_sig = SigSpec();
			}

			SigSpec other_sig = sigidx[other_key];
			int k = 0, n = 1;

			while (other_sig[k] != sig[i]) {
				k++;
				log_assert(k < GetSize(other_sig));
			}

			while (i+n < GetSize(sig) && k+n < GetSize(other_sig) && sig[i+n] == other_sig[k+n])
				n++;

			SigSpec sig1 = other_sig.extract(0, k);
			SigSpec sig2 = other_sig.extract(k, n);
			SigSpec sig3 = other_sig.extract(k+n, GetSize(other_sig)-k-n);

			for (auto bit : other_sig)
				bit2snippet.erase(bit);
			snippets.erase(other_key);

			insert(sig1);
			insert(sig2);
			insert(sig3);

			i += n-1;
		}

		if (!new_sig.empty()) {
			int new_key = sigidx(new_sig);
			snippets.insert(new_key);
			for (auto bit : new_sig)
				bit2snippet[bit] = new_key;
		}
	}

	void insert(const RTLIL::CaseRule *cs)
	{
		for (auto &action : cs->actions)
			insert(action.first);

		for (auto sw : cs->switches)
		for (auto cs2 : sw->cases)
			insert(cs2);
	}
};

struct SnippetSwCache
{
	dict<RTLIL::SwitchRule*, pool<RTLIL::SigBit>> full_case_bits_cache;
	dict<RTLIL::SwitchRule*, pool<int>> cache;
	const SigSnippets *snippets;
	int current_snippet;

	bool check(RTLIL::SwitchRule *sw) const
	{
		auto it = cache.find(sw);
		return it != cache.end() && it->second.count(current_snippet) != 0;
	}

	void insert(const RTLIL::CaseRule *cs, vector<RTLIL::SwitchRule*> &sw_stack)
	{
		for (auto &action : cs->actions)
		for (auto bit : action.first) {
			int sn = snippets->bit2snippet.at(bit, -1);
			if (sn < 0)
				continue;
			for (auto sw : sw_stack)
				cache[sw].insert(sn);
		}

		for (auto sw : cs->switches) {
			sw_stack.push_back(sw);
			for (auto cs2 : sw->cases)
				insert(cs2, sw_stack);
			sw_stack.pop_back();
		}
	}

	void insert(const RTLIL::CaseRule *cs)
	{
		vector<RTLIL::SwitchRule*> sw_stack;
		insert(cs, sw_stack);
	}
};

void apply_attrs(RTLIL::Cell *cell, const RTLIL::SwitchRule *sw, const RTLIL::CaseRule *cs)
{
	cell->attributes = sw->attributes;
	cell->add_strpool_attribute(ID::src, cs->get_strpool_attribute(ID::src));
}

RTLIL::SigSpec gen_cmp(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	std::stringstream sstr;
	sstr << "$procmux$" << (autoidx++);

	RTLIL::Wire *cmp_wire = mod->addWire(sstr.str() + "_CMP", 0);

	for (auto comp : compare)
	{
		RTLIL::SigSpec sig = signal;

		// get rid of don't-care bits
		log_assert(sig.size() == comp.size());
		for (int i = 0; i < comp.size(); i++)
			if (comp[i] == RTLIL::State::Sa) {
				sig.remove(i);
				comp.remove(i--);
			}
		if (comp.size() == 0)
			return RTLIL::SigSpec();

		if (sig.size() == 1 && comp == RTLIL::SigSpec(1,1) && !ifxmode)
		{
			mod->connect(RTLIL::SigSig(RTLIL::SigSpec(cmp_wire, cmp_wire->width++), sig));
		}
		else
		{
			// create compare cell
			RTLIL::Cell *eq_cell = mod->addCell(stringf("%s_CMP%d", sstr.str(), cmp_wire->width), ifxmode ? ID($eqx) : ID($eq));
			apply_attrs(eq_cell, sw, cs);

			eq_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
			eq_cell->parameters[ID::B_SIGNED] = RTLIL::Const(0);

			eq_cell->parameters[ID::A_WIDTH] = RTLIL::Const(sig.size());
			eq_cell->parameters[ID::B_WIDTH] = RTLIL::Const(comp.size());
			eq_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);

			eq_cell->setPort(ID::A, sig);
			eq_cell->setPort(ID::B, comp);
			eq_cell->setPort(ID::Y, RTLIL::SigSpec(cmp_wire, cmp_wire->width++));
		}
	}

	RTLIL::Wire *ctrl_wire;
	if (cmp_wire->width == 1)
	{
		ctrl_wire = cmp_wire;
	}
	else
	{
		ctrl_wire = mod->addWire(sstr.str() + "_CTRL");

		// reduce cmp vector to one logic signal
		RTLIL::Cell *any_cell = mod->addCell(sstr.str() + "_ANY", ID($reduce_or));
		apply_attrs(any_cell, sw, cs);

		any_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
		any_cell->parameters[ID::A_WIDTH] = RTLIL::Const(cmp_wire->width);
		any_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);

		any_cell->setPort(ID::A, cmp_wire);
		any_cell->setPort(ID::Y, RTLIL::SigSpec(ctrl_wire));
	}

	return RTLIL::SigSpec(ctrl_wire);
}

RTLIL::SigSpec gen_mux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::SigSpec else_signal, RTLIL::Cell *&last_mux_cell, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	log_assert(when_signal.size() == else_signal.size());

	std::stringstream sstr;
	sstr << "$procmux$" << (autoidx++);

	// the trivial cases
	if (compare.size() == 0 || when_signal == else_signal)
		return when_signal;

	// compare results
	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw, cs, ifxmode);
	if (ctrl_sig.size() == 0)
		return when_signal;
	log_assert(ctrl_sig.size() == 1);

	// prepare multiplexer output signal
	RTLIL::Wire *result_wire = mod->addWire(sstr.str() + "_Y", when_signal.size());

	// create the multiplexer itself
	RTLIL::Cell *mux_cell = mod->addCell(sstr.str(), ID($mux));
	apply_attrs(mux_cell, sw, cs);

	mux_cell->parameters[ID::WIDTH] = RTLIL::Const(when_signal.size());
	mux_cell->setPort(ID::A, else_signal);
	mux_cell->setPort(ID::B, when_signal);
	mux_cell->setPort(ID::S, ctrl_sig);
	mux_cell->setPort(ID::Y, RTLIL::SigSpec(result_wire));

	last_mux_cell = mux_cell;
	return RTLIL::SigSpec(result_wire);
}

void append_pmux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::Cell *last_mux_cell, RTLIL::SwitchRule *sw, RTLIL::CaseRule *cs, bool ifxmode)
{
	log_assert(last_mux_cell != NULL);
	log_assert(when_signal.size() == last_mux_cell->getPort(ID::A).size());

	if (when_signal == last_mux_cell->getPort(ID::A))
		return;

	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw, cs, ifxmode);
	log_assert(ctrl_sig.size() == 1);
	last_mux_cell->type = ID($pmux);

	RTLIL::SigSpec new_s = last_mux_cell->getPort(ID::S);
	new_s.append(ctrl_sig);
	last_mux_cell->setPort(ID::S, new_s);

	RTLIL::SigSpec new_b = last_mux_cell->getPort(ID::B);
	new_b.append(when_signal);
	last_mux_cell->setPort(ID::B, new_b);

	last_mux_cell->parameters[ID::S_WIDTH] = last_mux_cell->getPort(ID::S).size();
}

const pool<SigBit> &get_full_case_bits(SnippetSwCache &swcache, RTLIL::SwitchRule *sw)
{
	if (!swcache.full_case_bits_cache.count(sw))
	{
		pool<SigBit> bits;

		if (sw->get_bool_attribute(ID::full_case))
		{
			bool first_case = true;

			for (auto cs : sw->cases)
			{
				pool<SigBit> case_bits;

				for (auto it : cs->actions) {
					for (auto bit : it.first)
						case_bits.insert(bit);
				}

				for (auto it : cs->switches) {
					for (auto bit : get_full_case_bits(swcache, it))
						case_bits.insert(bit);
				}

				if (first_case) {
					first_case = false;
					bits = case_bits;
				} else {
					pool<SigBit> new_bits;
					for (auto bit : bits)
						if (case_bits.count(bit))
							new_bits.insert(bit);
					bits.swap(new_bits);
				}
			}
		}

		bits.swap(swcache.full_case_bits_cache[sw]);
	}

	return swcache.full_case_bits_cache.at(sw);
}

bool maybe_touches_sig_wires(const RTLIL::SigSpec &signal, const pool<RTLIL::Wire*> &sig_wires)
{
	for (auto &chunk : signal.chunks())
		if (chunk.wire != NULL && sig_wires.count(chunk.wire))
			return true;
	return false;
}

static bool is_simple_parallel_case(RTLIL::SwitchRule *sw)
{
	if (sw->get_bool_attribute(ID::parallel_case))
		return true;

	pool<Const> case_values;
	for (auto cs : sw->cases) {
		for (const auto &pat : cs->compare) {
			if (!pat.is_fully_def())
				return false;
			Const cpat = pat.as_const();
			if (case_values.count(cpat))
				return false;
			case_values.insert(cpat);
		}
	}

	return true;
}

static const std::vector<int> &get_parallel_case_groups(RTLIL::SwitchRule *sw,
		dict<RTLIL::SwitchRule*, std::vector<int>> &swgroups, bool ifxmode)
{
	if (!swgroups.count(sw)) {
		std::vector<int> pgroups(sw->cases.size());

		// Case grouping only depends on the switch patterns, not on the output
		// snippet currently being lowered. Cache it once per switch.
		if (!is_simple_parallel_case(sw)) {
			BitPatternPool pool(sw->signal.size());
			bool extra_group_for_next_case = false;
			for (size_t i = 0; i < sw->cases.size(); i++) {
				RTLIL::CaseRule *cs = sw->cases[i];
				if (i != 0) {
					pgroups[i] = pgroups[i-1];
					if (extra_group_for_next_case) {
						pgroups[i] = pgroups[i-1]+1;
						extra_group_for_next_case = false;
					}
					for (const auto &pat : cs->compare)
						if (!pat.is_fully_const() || !pool.has_all(pat))
							pgroups[i] = pgroups[i-1]+1;
					if (cs->compare.empty())
						pgroups[i] = pgroups[i-1]+1;
					if (pgroups[i] != pgroups[i-1])
						pool = BitPatternPool(sw->signal.size());
				}
				for (const auto &pat : cs->compare)
					if (!pat.is_fully_const())
						extra_group_for_next_case = true;
					else if (!ifxmode)
						pool.take(pat);
			}
		}

		swgroups[sw] = std::move(pgroups);
	}

	return swgroups.at(sw);
}

RTLIL::SigSpec signal_to_mux_tree_worker(RTLIL::Module *mod, SnippetSwCache &swcache,
		dict<RTLIL::SwitchRule*, std::vector<int>> &swgroups,
		RTLIL::CaseRule *cs, const RTLIL::SigSpec &sig, const pool<RTLIL::Wire*> &sig_wires,
		const RTLIL::SigSpec &defval, bool ifxmode, bool wire_prefilter)
{
	RTLIL::SigSpec result = defval;

	for (auto &action : cs->actions) {
		if (action.first.empty())
			continue;
		// Fast prefilter: avoid replace/remove2 when this action can not touch `sig`.
		if (wire_prefilter && !maybe_touches_sig_wires(action.first, sig_wires))
			continue;
		sig.replace(action.first, action.second, &result);
		action.first.remove2(sig, &action.second);
	}

	for (auto sw : cs->switches)
	{
		if (!swcache.check(sw))
			continue;

		// swgroups reserves enough storage before this walk, so recursive cache
		// insertions cannot invalidate this reference.
		const auto &pgroups = get_parallel_case_groups(sw, swgroups, ifxmode);

		// mask default bits that are irrelevant because the output is driven by a full case
		const pool<SigBit> &full_case_bits = get_full_case_bits(swcache, sw);
		for (int i = 0; i < GetSize(sig); i++)
			if (full_case_bits.count(sig[i]))
				result[i] = State::Sx;

		// evaluate in reverse order to give the first entry the top priority
		RTLIL::SigSpec initial_val = result;
		RTLIL::Cell *last_mux_cell = NULL;
		for (size_t i = 0; i < sw->cases.size(); i++) {
			int case_idx = sw->cases.size() - i - 1;
			RTLIL::CaseRule *cs2 = sw->cases[case_idx];
			RTLIL::SigSpec value = signal_to_mux_tree_worker(mod, swcache, swgroups, cs2, sig,
					sig_wires, initial_val, ifxmode, wire_prefilter);
			if (last_mux_cell && pgroups[case_idx] == pgroups[case_idx+1])
				append_pmux(mod, sw->signal, cs2->compare, value, last_mux_cell, sw, cs2, ifxmode);
			else
				result = gen_mux(mod, sw->signal, cs2->compare, value, result, last_mux_cell, sw, cs2, ifxmode);
		}
	}

	return result;
}

RTLIL::SigSpec signal_to_mux_tree(RTLIL::Module *mod, SnippetSwCache &swcache,
		dict<RTLIL::SwitchRule*, std::vector<int>> &swgroups,
		RTLIL::CaseRule *cs, const RTLIL::SigSpec &sig, const RTLIL::SigSpec &defval,
		bool ifxmode, bool wire_prefilter)
{
	pool<RTLIL::Wire*> sig_wires;
	if (wire_prefilter)
		for (auto &chunk : sig.chunks())
			if (chunk.wire != NULL)
				sig_wires.insert(chunk.wire);
	return signal_to_mux_tree_worker(mod, swcache, swgroups, cs, sig, sig_wires,
			defval, ifxmode, wire_prefilter);
}

void proc_mux(RTLIL::Module *mod, RTLIL::Process *proc, bool ifxmode, bool wire_prefilter)
{
	log("Creating decoders for process `%s.%s'.\n", mod->name, proc->name);

	SigSnippets sigsnip;
	sigsnip.insert(&proc->root_case);

	SnippetSwCache swcache;
	swcache.snippets = &sigsnip;
	swcache.insert(&proc->root_case);

	dict<RTLIL::SwitchRule*, std::vector<int>> swgroups;
	swgroups.reserve(swcache.cache.size());

	int cnt = 0;
	for (int idx : sigsnip.snippets)
	{
		swcache.current_snippet = idx;
		RTLIL::SigSpec sig = sigsnip.sigidx[idx];

		log("%6d/%d: %s\n", ++cnt, GetSize(sigsnip.snippets), log_signal(sig));

		RTLIL::SigSpec value = signal_to_mux_tree(mod, swcache, swgroups, &proc->root_case, sig,
				RTLIL::SigSpec(RTLIL::State::Sx, sig.size()), ifxmode, wire_prefilter);
		mod->connect(RTLIL::SigSig(sig, value));
	}
}

struct ProcMuxPass : public Pass {
	ProcMuxPass() : Pass("proc_mux", "convert decision trees to multiplexers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_mux [options] [selection]\n");
		log("\n");
		log("This pass converts the decision trees in processes (originating from if-else\n");
		log("and case statements) to trees of multiplexer cells.\n");
		log("\n");
		log("    -ifx\n");
		log("        Use Verilog simulation behavior with respect to undef values in\n");
		log("        'case' expressions and 'if' conditions.\n");
		log("\n");
		log("    -no-wire-prefilter\n");
		log("        Disable the fast action-wire prefilter. This is useful for\n");
		log("        debugging and equivalence testing against the legacy behavior.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool ifxmode = false;
		bool wire_prefilter = true;
		log_header(design, "Executing PROC_MUX pass (convert decision trees to multiplexers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-ifx") {
				ifxmode = true;
				continue;
			}
			if (args[argidx] == "-no-wire-prefilter") {
				wire_prefilter = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->all_selected_modules())
			for (auto proc : mod->selected_processes())
				proc_mux(mod, proc, ifxmode, wire_prefilter);
	}
} ProcMuxPass;

PRIVATE_NAMESPACE_END
