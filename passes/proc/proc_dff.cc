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

#include "backends/rtlil/rtlil_backend.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/log.h"
#include "kernel/yosys_common.h"
#include <optional>
#include <sstream>
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE

struct BitRule {
	SigBit trig;
	bool trig_polarity; // true = active high, false = active low
	bool effect; // true = set, false = reset

	bool operator==(const BitRule& other) const { return trig == other.trig && trig_polarity == other.trig_polarity && effect == other.effect; }
	[[nodiscard]] Hasher hash_into(Hasher h) const { // No, this fluff doesn't deserve more lines. It's not meant to be read.
		h.eat(trig); h.eat(trig_polarity); h.eat(effect); return h; }
};
template<> struct std::hash<std::vector<BitRule>> {std::size_t operator()(const std::vector<BitRule>& r) const noexcept { Hasher h; for (auto& rr : r) h.eat(rr); return (size_t)h.yield(); } };

PRIVATE_NAMESPACE_BEGIN

RTLIL::SigSpec find_any_lvalue(const RTLIL::Process *proc)
{
	RTLIL::SigSpec lvalue;

	for (auto sync : proc->syncs)
	for (auto &action : sync->actions)
		if (action.first.size() > 0) {
			lvalue = action.first;
			lvalue.sort_and_unify();
			break;
		}

	for (auto sync : proc->syncs) {
		RTLIL::SigSpec this_lvalue;
		for (auto &action : sync->actions)
			this_lvalue.append(action.first);
		this_lvalue.sort_and_unify();
		RTLIL::SigSpec common_sig = this_lvalue.extract(lvalue);
		if (common_sig.size() > 0)
			lvalue = common_sig;
	}

	return lvalue;
}

struct DSigs {
	RTLIL::SigSpec d;
	RTLIL::SigSpec q;
	RTLIL::SigSpec clk;
};
using Rules = std::vector<std::pair<RTLIL::SigSpec, RTLIL::SyncRule*>>;

/**
 * Generates odd $dffsr wirh priority and ALOAD implemented with muxes
 */
void gen_dffsr_complex(RTLIL::Module *mod, DSigs sigs, bool clk_polarity,
		Rules &async_rules, RTLIL::Process *proc)
{
	// A signal should be set/cleared if there is a load trigger that is enabled
	// such that the load value is 1/0 and it is the highest priority trigger
	RTLIL::SigSpec sig_sr_set = RTLIL::SigSpec(0, sigs.d.size());
	RTLIL::SigSpec sig_sr_clr = RTLIL::SigSpec(0, sigs.d.size());

	// Reverse iterate through the rules as the first ones are the highest priority
	// so need to be at the top of the mux trees
	for (auto it = async_rules.crbegin(); it != async_rules.crend(); it++)
	{
		const auto& [sync_value, rule] = *it;
		const auto pos_trig = rule->type == RTLIL::SyncType::ST1 ? rule->signal : mod->Not(NEW_ID, rule->signal);

		// If pos_trig is true, we have priority at this point in the tree so
		// set a bit if sync_value has a set bit. Otherwise, defer to the rest
		// of the priority tree
		sig_sr_set = mod->Mux(NEW_ID, sig_sr_set, sync_value, pos_trig);

		// Same deal with clear bit
		const auto sync_value_inv = mod->Not(NEW_ID, sync_value);
		sig_sr_clr = mod->Mux(NEW_ID, sig_sr_clr, sync_value_inv, pos_trig);
	}

	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addDffsr(sstr.str(), sigs.clk, sig_sr_set, sig_sr_clr, sigs.d, sigs.q, clk_polarity);
	cell->attributes = proc->attributes;

	log("  created %s cell `%s' with %s edge clock and multiple level-sensitive resets.\n",
			cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
}

/**
 * Generates $dffsr wirh $priority cells
 */
void gen_dffsr(RTLIL::Module *mod, DSigs sigs, bool clk_polarity,
		Rules &async_rules, ConstEval& ce, RTLIL::Process *proc)
{
	RTLIL::SigSpec sig_sr_set;
	RTLIL::SigSpec sig_sr_clr;
	// nullopt rule = "this bit is not assigned to in this rule"
	std::vector<std::vector<std::optional<BitRule>>> bit_rules(sigs.d.size());
	// For checking consistent per-bit set/reset edges and bailing out on inconsistent
	std::optional<bool> set_pol;
	std::optional<bool> reset_pol;

	for (auto it = async_rules.cbegin(); it != async_rules.cend(); it++)
	{
		const auto& [sync_value, rule] = *it;
		for (int i = 0; i < sigs.d.size(); i++) {
			log_assert(rule->signal.size() == 1);
			SigSpec value_bit = sync_value[i];
			if (sync_value[i] == sigs.q[i]) {
				log_debug("%s is %s\n", log_signal(sync_value[i]), log_signal(sigs.q[i]));
				while (bit_rules.size() <= (size_t) i)
					bit_rules.push_back({});
				bit_rules[i].push_back(std::nullopt);
				continue;
			}
			if (!ce.eval(value_bit)) {
				// ALOAD, mux tree time
				log_debug("non-const %s\n", log_signal(sync_value[i]));
				gen_dffsr_complex(mod, sigs, clk_polarity, async_rules, proc);
				return;
			}
			bool effect = ce.values_map(value_bit).as_const().as_bool();
			bool trig_pol = rule->type == RTLIL::SyncType::ST1;
			while (bit_rules.size() <= (size_t) i)
				bit_rules.push_back({});
			BitRule bit_rule {rule->signal[0], trig_pol, effect};
			bit_rules[i].push_back(bit_rule);

			bool set_inconsistent = effect && set_pol && (*set_pol != trig_pol);
			bool reset_inconsistent = !effect && reset_pol && (*reset_pol != trig_pol);
			if (set_inconsistent || reset_inconsistent) {
				// Mixed polarities, mux tree time
				gen_dffsr_complex(mod, sigs, clk_polarity, async_rules, proc);
				return;
			}
			if (effect) {
				set_pol = trig_pol;
			} else {
				reset_pol = trig_pol;
			}
		}
	}

	if (set_pol == std::nullopt || reset_pol == std::nullopt) {
		// set or reset never used, falling back to mux tree
		gen_dffsr_complex(mod, sigs, clk_polarity, async_rules, proc);
		return;
	}


	struct Builder {
		using MaybeBitControl = std::pair<std::optional<SigBit>, std::optional<SigBit>>;
		std::unordered_map<std::vector<BitRule>, MaybeBitControl> map = {};
		RTLIL::Module* mod;
		RTLIL::Process* proc;
		bool set_pol, reset_pol;
		RTLIL::SigBit const_if_none(std::optional<SigBit> maybe, bool polarity) {
			if (maybe)
				return *maybe;
			// Set the control signal to be constantly inactive
			if (polarity)
				return set_pol ? RTLIL::State::S0 : RTLIL::State::S1;
			else
				return reset_pol ? RTLIL::State::S0 : RTLIL::State::S1;
		}
		Builder(RTLIL::Module* mod, RTLIL::Process* proc, bool s, bool r) : mod(mod), proc(proc), set_pol(s), reset_pol(r) {}
		std::pair<RTLIL::SigSpec, RTLIL::SigSpec> priority(const std::vector<BitRule>& applicable) {
			RTLIL::SigSpec bit_sets {};
			RTLIL::SigSpec bit_resets {};
			if (!applicable.size()) {
				return std::make_pair(bit_sets, bit_resets);
			} else if (applicable.size() == 1) {
				auto rule = applicable[0];
				if (rule.effect)
					bit_sets.append(rule.trig);
				else
					bit_resets.append(rule.trig);
				return std::make_pair(bit_sets, bit_resets);
			}
			RTLIL::Wire* prioritized = mod->addWire(NEW_ID, applicable.size());
			prioritized->attributes = proc->attributes;
			RTLIL::Cell* priority = mod->addPriority(NEW_ID, SigSpec(), prioritized);
			priority->attributes = proc->attributes;
			priority->setParam(ID::WIDTH, applicable.size());

			RTLIL::SigSpec priority_in;
			std::vector<RTLIL::State> priority_pol;

			// Construct applicable rules
			for (auto rule : applicable) {
				log_debug("if %s == %d then set %d\n", log_signal(rule.trig), rule.trig_polarity, rule.effect);
				priority_in.append(rule.trig);
				priority_pol.push_back(RTLIL::State(rule.trig_polarity));
				if (rule.effect)
					bit_sets.append(SigBit(prioritized, priority_in.size() - 1));
				else
					bit_resets.append(SigBit(prioritized, priority_in.size() - 1));
			}

			priority->setPort(ID::A, priority_in);
			priority->setPort(ID::Y, prioritized); // fixup (previously zero-width)
			priority->setParam(ID::POLARITY, priority_pol);
			return std::make_pair(bit_sets, bit_resets);
		}
		std::pair<RTLIL::SigBit, RTLIL::SigBit> reduce(const std::pair<RTLIL::SigSpec, RTLIL::SigSpec>& unreduced) {
			const auto& [bit_sets, bit_resets] = unreduced;
			std::optional<SigBit> set, reset;
			if (bit_sets.size()) {
				if (bit_sets.size() == 1) {
					set = bit_sets[0];
				} else {
					set = mod->addWire(NEW_ID);
					set->wire->attributes = proc->attributes;
					// Polarities are required to be consistent, as guaranteed by check above buildere
					(set_pol ? mod->addReduceOr(NEW_ID, bit_sets, *set) : mod->addReduceAnd(NEW_ID, bit_sets, *set))->attributes = proc->attributes;
				}
			}
			if (bit_resets.size()) {
				if (bit_resets.size() == 1) {
					reset = bit_resets[0];
				} else {
					reset = mod->addWire(NEW_ID);
					reset->wire->attributes = proc->attributes;
					(reset_pol ? mod->addReduceOr(NEW_ID, bit_resets, *reset) : mod->addReduceAnd(NEW_ID, bit_resets, *reset))->attributes = proc->attributes;
				}
			}
			return std::make_pair(const_if_none(set, true), const_if_none(reset, false));
		}
		MaybeBitControl build(std::vector<std::optional<BitRule>>& rules) {
			std::vector<BitRule> applicable;
			for (auto rule : rules) {
				if (rule) {
					applicable.push_back(*rule);
				} else {
					log_debug("Unused bit due to no assignment to this bit from this rule\n");
				}
			}
			if (map.count(applicable)) {
				return map[applicable];
			}

			auto priority_controls = priority(applicable);
			auto ret = reduce(priority_controls);
			map[applicable] = ret;
			return ret;
		}
	};
	Builder builder(mod, proc, *set_pol, *reset_pol);
	for (int i = 0; i < sigs.d.size(); i++) {
		auto [set, reset] = builder.build(bit_rules[i]);
		sig_sr_set.append(*set);
		sig_sr_clr.append(*reset);
	}

	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);
	RTLIL::Cell *cell = mod->addDffsr(sstr.str(), sigs.clk, sig_sr_set, sig_sr_clr, sigs.d, sigs.q, clk_polarity);
	cell->attributes = proc->attributes;
	cell->setParam(ID::SET_POLARITY, Const(*set_pol, 1));
	cell->setParam(ID::CLR_POLARITY, Const(*reset_pol, 1));
	log("  created %s cell `%s' with %s edge clock and multiple level-sensitive resets.\n",
			cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
}

void gen_aldff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool set_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec set, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), ID($aldff));
	cell->attributes = proc->attributes;

	cell->parameters[ID::WIDTH] = RTLIL::Const(sig_in.size());
	cell->parameters[ID::ALOAD_POLARITY] = RTLIL::Const(set_polarity, 1);
	cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity, 1);
	cell->setPort(ID::D, sig_in);
	cell->setPort(ID::Q, sig_out);
	cell->setPort(ID::AD, sig_set);
	cell->setPort(ID::CLK, clk);
	cell->setPort(ID::ALOAD, set);

	log("  created %s cell `%s' with %s edge clock and %s level non-const reset.\n", cell->type, cell->name,
			clk_polarity ? "positive" : "negative", set_polarity ? "positive" : "negative");
}

void gen_dff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::Const val_rst, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool arst_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec *arst, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), clk.empty() ? ID($ff) : arst ? ID($adff) : ID($dff));
	cell->attributes = proc->attributes;

	cell->parameters[ID::WIDTH] = RTLIL::Const(sig_in.size());
	if (arst) {
		cell->parameters[ID::ARST_POLARITY] = RTLIL::Const(arst_polarity, 1);
		cell->parameters[ID::ARST_VALUE] = val_rst;
	}
	if (!clk.empty()) {
		cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity, 1);
	}

	cell->setPort(ID::D, sig_in);
	cell->setPort(ID::Q, sig_out);
	if (arst)
		cell->setPort(ID::ARST, *arst);
	if (!clk.empty())
		cell->setPort(ID::CLK, clk);

	if (!clk.empty())
		log("  created %s cell `%s' with %s edge clock", cell->type, cell->name, clk_polarity ? "positive" : "negative");
	else
		log("  created %s cell `%s' with global clock", cell->type, cell->name);
	if (arst)
		log(" and %s level reset", arst_polarity ? "positive" : "negative");
	log(".\n");
}

void proc_dff(RTLIL::Module *mod, RTLIL::Process *proc, ConstEval &ce)
{
	while (1)
	{
		RTLIL::SigSpec sig = find_any_lvalue(proc);

		if (sig.size() == 0)
			break;

		log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
				mod->name.c_str(), log_signal(sig), mod->name.c_str(), proc->name.c_str());

		RTLIL::SigSpec insig = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
		RTLIL::SyncRule *sync_edge = NULL;
		RTLIL::SyncRule *sync_always = NULL;
		bool global_clock = false;

		// A priority ordered set of rules, pairing the value to be assigned for
		// that rule to the rule
		std::vector<std::pair<RTLIL::SigSpec, RTLIL::SyncRule*>> async_rules;

		// Needed when the async rules are collapsed into one as async_rules
		// works with pointers to SyncRule
		RTLIL::SyncRule single_async_rule;

		for (auto sync : proc->syncs)
		for (auto &action : sync->actions)
		{
			if (action.first.extract(sig).size() == 0)
				continue;

			if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
				RTLIL::SigSpec rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				sig.replace(action.first, action.second, &rstval);
				async_rules.emplace_back(rstval, sync);
			}
			else if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
				if (sync_edge != NULL && sync_edge != sync)
					log_error("Multiple edge sensitive events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_edge = sync;
			}
			else if (sync->type == RTLIL::SyncType::STa) {
				if (sync_always != NULL && sync_always != sync)
					log_error("Multiple always events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_always = sync;
			}
			else if (sync->type == RTLIL::SyncType::STg) {
				sig.replace(action.first, action.second, &insig);
				global_clock = true;
			}
			else {
				log_error("Event with any-edge sensitivity found for this signal!\n");
			}

			action.first.remove2(sig, &action.second);
		}

		// If all async rules assign the same value, priority ordering between
		// them doesn't matter so they can be collapsed together into one rule
		// with the disjunction of triggers
		if (!async_rules.empty() &&
		    std::all_of(async_rules.begin(), async_rules.end(), [&](auto& p) {
		        return p.first == async_rules.front().first;
		    }))
		{
			const auto rstval = async_rules.front().first;

			// The trigger is the disjunction of existing triggers
			// (with appropriate negation)
			RTLIL::SigSpec triggers;
			for (const auto &[_, it] : async_rules)
				triggers.append(it->type == RTLIL::SyncType::ST1 ? it->signal : mod->Not(NEW_ID, it->signal));

			// Put this into the dummy sync rule so it can be treated the same
			// as ones coming from the module
			single_async_rule.type = RTLIL::SyncType::ST1;
			single_async_rule.signal = mod->ReduceOr(NEW_ID, triggers);
			single_async_rule.actions.push_back(RTLIL::SigSig(sig, rstval));

			// Replace existing rules with this new rule
			async_rules.clear();
			async_rules.emplace_back(rstval, &single_async_rule);
		}

		SigSpec sig_q = sig;
		ce.assign_map.apply(insig);
		ce.assign_map.apply(sig);

		// If the reset value assigns the reg to itself, add this as part of
		// the input signal and delete the rule
		if (async_rules.size() == 1 && async_rules.front().first == sig) {
			const auto& [_, rule] = async_rules.front();
			if (rule->type == RTLIL::SyncType::ST1)
				insig = mod->Mux(NEW_ID, insig, sig, rule->signal);
			else
				insig = mod->Mux(NEW_ID, sig, insig, rule->signal);

			async_rules.clear();
		}

		if (sync_always) {
			if (sync_edge || !async_rules.empty())
				log_error("Mixed always event with edge and/or level sensitive events!\n");
			log("  created direct connection (no actual register cell created).\n");
			mod->connect(RTLIL::SigSig(sig, insig));
			continue;
		}

		if (!sync_edge && !global_clock)
			log_error("Missing edge-sensitive event for this signal!\n");

		// More than one reset value so we derive a dffsr formulation
		if (async_rules.size() > 1)
		{
			log_warning("Complex async reset for dff `%s'.\n", log_signal(sig));
			DSigs sigs {insig, sig, sync_edge->signal};
			bool clk_pol = sync_edge->type == RTLIL::SyncType::STp;
			gen_dffsr(mod, sigs, clk_pol, async_rules, ce, proc);
			continue;
		}

		// If there is a reset condition in the async rules, use it
		SigSpec rstval = async_rules.empty() ? RTLIL::SigSpec(RTLIL::State::Sz, sig.size()) : async_rules.front().first;
		RTLIL::SyncRule* sync_level = async_rules.empty() ? nullptr : async_rules.front().second;
		ce.assign_map.apply(rstval);

		if (!rstval.is_fully_const() && !ce.eval(rstval))
		{
			log_warning("Async reset value `%s' is not constant!\n", log_signal(rstval));
			gen_aldff(mod, insig, rstval, sig_q,
					sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge->signal, sync_level->signal, proc);
			continue;
		}

		gen_dff(mod, insig, rstval.as_const(), sig_q,
				sync_edge && sync_edge->type == RTLIL::SyncType::STp,
				sync_level && sync_level->type == RTLIL::SyncType::ST1,
				sync_edge ? sync_edge->signal : SigSpec(),
				sync_level ? &sync_level->signal : NULL, proc);
	}
}

struct ProcDffPass : public Pass {
	ProcDffPass() : Pass("proc_dff", "extract flip-flops from processes") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_dff [selection]\n");
		log("\n");
		log("This pass identifies flip-flops in the processes and converts them to\n");
		log("d-type flip-flop cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PROC_DFF pass (convert process syncs to FFs).\n");

		extra_args(args, 1, design);
		Pass::call(design, "dump");

		for (auto mod : design->all_selected_modules()) {
			ConstEval ce(mod);
			for (auto proc : mod->selected_processes())
				proc_dff(mod, proc, ce);
		}
	}
} ProcDffPass;

PRIVATE_NAMESPACE_END
