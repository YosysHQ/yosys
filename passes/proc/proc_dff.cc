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
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <type_traits>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

RTLIL::SigSpec find_any_lvalue(const RTLIL::Process& proc)
{
	RTLIL::SigSpec lvalue;

	for (const auto* sync : proc.syncs)
	for (const auto& action : sync->actions)
		if (action.first.size() > 0) {
			lvalue = action.first;
			lvalue.sort_and_unify();
			break;
		}

	for (const auto* sync : proc.syncs) {
		RTLIL::SigSpec this_lvalue;
		for (const auto& action : sync->actions)
			this_lvalue.append(action.first);
		this_lvalue.sort_and_unify();
		RTLIL::SigSpec common_sig = this_lvalue.extract(lvalue);
		if (common_sig.size() > 0)
			lvalue = common_sig;
	}

	return lvalue;
}

std::string new_dff_name() {
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);
	return sstr.str();
}

class Dff {
public:
	// Extract the relevant signals from a process that drives sig as a DFF
	Dff(RTLIL::Module& mod, const SigSpec& sig_out, RTLIL::Process& proc) :
		proc{proc}, mod{mod}, sig_in(RTLIL::State::Sz, sig_out.size()), sig_out{sig_out}
	{
		// We gather sync rules corresponding to always/edge first to check
		// whether they are conflicting before actually updating clk
		const RTLIL::SyncRule* sync_edge = nullptr;
		const RTLIL::SyncRule* sync_always = nullptr;
		bool global_clock = false;

		for (const auto* sync : proc.syncs)
		for (const auto& action : sync->actions) {
			if (action.first.extract(sig_out).empty())
				continue;

			// Level sensitive assignments (set/reset/aload)
			if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
				RTLIL::SigSpec rstval(RTLIL::State::Sz, sig_out.size());
				sig_out.replace(action.first, action.second, &rstval);
				async_rules.emplace_back(rstval, *sync);
				continue;
			}

			// Edge sensitive assignments (clock)
			if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
				if (sync_edge != NULL && sync_edge != sync)
					log_error("Multiple edge sensitive events found for this signal!\n");
				sig_out.replace(action.first, action.second, &sig_in);
				sync_edge = sync;
				continue;
			}

			// Always assignments
			if (sync->type == RTLIL::SyncType::STa) {
				if (sync_always != NULL && sync_always != sync)
					log_error("Multiple always events found for this signal!\n");
				sig_out.replace(action.first, action.second, &sig_in);
				sync_always = sync;
				continue;
			}

			// Global clock assignments
			if (sync->type == RTLIL::SyncType::STg) {
				sig_out.replace(action.first, action.second, &sig_in);
				global_clock = true;
				continue;
			}

			log_error("Event with any-edge sensitivity found for this signal!\n");
		}

		if (sync_always && (sync_edge || !async_rules.empty()))
			log_error("Mixed always event with edge and/or level sensitive events!\n");

		if (!sync_edge && !global_clock && !sync_always)
			log_error("Missing edge-sensitive event for this signal!\n");

		// Update our internal versions of these signals to track whether things
		// are edge sensitive
		if (sync_edge)
			clk = *sync_edge;
		always = sync_always != nullptr;
	}

	void optimize(ConstEval& ce) {
		optimize_const_eval(ce);
		optimize_same_value(ce);
		optimize_self_assign(ce);
		optimize_single_rule_consts();
	}

	// Const evaluate async rule values and triggers, and remove those that
	// have triggers that are always false
	void optimize_const_eval(ConstEval& ce) {
		ce.eval(sig_in);
		ce.eval(clk.sig);

		for (auto& [value, trigger] : async_rules) {
			ce.eval(value);
			ce.eval(trigger.sig);
		}

		async_rules.erase(
			std::remove_if(async_rules.begin(), async_rules.end(),
				[](const auto& rule) { return rule.trigger.is_never_triggered(); }
			),
			async_rules.end()
		);
	}

	// Combine adjacent async rules that assign the same value into one rule
	// with a disjunction of triggers. The resulting trigger is optimized by
	// constant evaluation. We apply all of these optimizations that can be
	// done to the LSB and shrink the size of the signal we are considering if
	// higher bits cannot be optimized in the same way.
	void optimize_same_value(ConstEval& ce) {
		for (size_t i = 0; i + 1 < async_rules.size();) {
			const bool lsb_optimizable = shrink_while_matching_values([&](const size_t bit) {
				return async_rules[i].value[bit] == async_rules[i + 1].value[bit];
			});

			if (!lsb_optimizable) {
				i++;
				continue;
			}

			// i and i + 1 assign the same value so can be merged by taking
			// the disjunction of triggers and deleting the second
			async_rules[i].trigger = mod.ReduceOr(
				NEW_ID,
				SigSpec{
					async_rules[i].trigger.positive_trigger(mod),
					async_rules[i + 1].trigger.positive_trigger(mod)
				}
			);
			async_rules.erase(async_rules.begin() + i + 1);

			ce.eval(async_rules[i].trigger.sig);
		}
	}

	// If the lowest priority async rule assigns the output value to itself,
	// remove the rule and fold this into the input signal. If the LSB assigns
	// the output to itself but higher bits don't, we resize down to just the
	// LSBs that assign to themselves, allowing more optimized representations
	// for those bits.
	void optimize_self_assign(ConstEval& ce) {
		SigSpec sig_out_mapped = sig_out;
		ce.assign_map.apply(sig_out_mapped);

		// Calculate the number of low priority rules that can be folded into
		// the input signal for a given bit position
		const size_t lsb_foldable_rules = shrink_while_matching_values([&](const size_t i) {
			size_t foldable = 0;
			for (auto it = async_rules.crbegin(); it != async_rules.crend(); it++, foldable++) {
				const auto& [value, trigger] = *it;
				if (value[i] != sig_out_mapped[i])
					break;
			}
			return foldable;
		});

		if (lsb_foldable_rules == 0)
			return;

		// Calculate the disjunction of triggers
		SigSpec triggers;
		for (size_t i = 0; i < lsb_foldable_rules; i++)
			triggers.append(async_rules.crbegin()[i].trigger.positive_trigger(mod));

		const auto trigger = mod.ReduceOr(NEW_ID, triggers);
		sig_in = mod.Mux(NEW_ID, sig_in, sig_out, trigger);
		ce.eval(sig_in);

		async_rules.resize(async_rules.size() - lsb_foldable_rules);
	}

	// If we have only a single rule, this means we will generate either an $aldff
	// or an $adff if the reset value is constant or non-constant respectively.
	// If there are any non-constant bits in the rule value, an $aldff will be
	// used for all bits, but we would like to use an $adff for as many
	// bits as possible. This optimization therefore calculates the longest run
	// of bits starting at the LSB of the value with the same constness and
	// removes the rest from consideration in this pass. This means that const
	// and non-const sections can be separately mapped to $adff and $aldff.
	void optimize_single_rule_consts() {
		if (async_rules.size() != 1)
			return;

		shrink_while_matching_values([&](const size_t i) {
			return async_rules.front().value[i].is_wire();
		});
	}

	void generate() {
		// Progressively attempt more complex formulations, preferring the
		// simpler ones. These rules should be able to cover all representable
		// DFF patterns.
		if (try_generate_always())
			return;

		if (try_generate_dff())
			return;

		if (try_generate_single_async_dff())
			return;

		if (try_generate_dffsr())
			return;

		log_error("unable to match a dff type to this signal's rules.\n");
	}

	// Generates a connection if this dff is an always connection
	// Returns true if successful
	bool try_generate_always() {
		if (!always)
			return false;

		log_assert(async_rules.empty());
		log_assert(clk.empty());

		log("  created direct connection (no actual register cell created).\n");
		mod.connect(sig_out, sig_in);
		return true;
	}

	// Generates a $dff if this dff has no async rules and a clock of a $ff
	// if this dff has no async rules and is globally clocked
	// Returns true if succesful
	bool try_generate_dff() {
		if (always || !async_rules.empty())
			return false;

		RTLIL::Cell* cell;
		const char* edge;
		if (clk.empty()) {
			edge = "global";
			cell = mod.addFf(new_dff_name(), sig_in, sig_out);
		} else {
			edge = clk.polarity_str();
			cell = mod.addDff(
				/*         name */ new_dff_name(),
				/*      sig_clk */ clk.sig,
				/*        sig_d */ sig_in,
				/*        sig_q */ sig_out,
				/* clk_polarity */ clk.polarity()
			);
		}
		cell->attributes = proc.attributes;

		log("  created %s cell `%s' with %s edge clock.", cell->type.c_str(), cell->name.c_str(), edge);
		return true;
	}

	// Generates an $adff or $aldff if this dff has a single async rule that
	// is constant or non-constant respectively
	// Returns true if successful
	bool try_generate_single_async_dff() {
		if (!explicitly_clocked() || async_rules.size() != 1)
			return false;

		const auto& aload = async_rules.front();
		const bool is_const = aload.value.is_fully_const();

		RTLIL::Cell* cell;
		if (is_const) {
			cell = mod.addAdff(
				/*           name */ new_dff_name(),
				/*        sig_clk */ clk.sig,
				/*       sig_arst */ aload.trigger.sig,
				/*          sig_d */ sig_in,
				/*          sig_q */ sig_out,
				/*     arst_value */ aload.value.as_const(),
				/*   clk_polarity */ clk.polarity(),
				/*  arst_polarity */ aload.trigger.polarity()
			);
		} else {
			log_warning("Async reset value `%s' is not constant!\n", log_signal(aload.value));
			cell = mod.addAldff(
				/*           name */ new_dff_name(),
				/*        sig_clk */ clk.sig,
				/*      sig_aload */ aload.trigger.sig,
				/*          sig_d */ sig_in,
				/*          sig_q */ sig_out,
				/*         sig_ad */ aload.value,
				/*   clk_polarity */ clk.polarity(),
				/* aload_polarity */ aload.trigger.polarity()
			);
		}
		cell->attributes = proc.attributes;

		log(
			"  created %s cell `%s' with %s edge clock and %s level %sconst reset.\n",
			cell->type.c_str(), cell->name.c_str(), clk.polarity_str(), aload.trigger.polarity_str(),
			is_const ? "" : "non-"
		);

		return true;
	}

	// Generates a $dffsr cell from a complex set of async rules that are converted
	// into driving conditions for set and reset signals
	// Returns true if successful
	bool try_generate_dffsr() {
		if (!explicitly_clocked())
			return false;

		// A signal should be set/cleared if there is a load trigger that is enabled
		// such that the load value is 1/0 and it is the highest priority trigger
		RTLIL::SigSpec sig_set(0, size()), sig_clr(0, size());

		// Reverse iterate through the rules as the first ones are the highest priority
		// so need to be at the top of the mux trees
		for (auto it = async_rules.crbegin(); it != async_rules.crend(); it++) {
			const auto& [sync_value, trigger] = *it;
			const auto pos_trig = trigger.positive_trigger(mod);

			// If pos_trig is true, we have priority at this point in the tree so
			// set a bit if value has a set bit. Otherwise, defer to the rest
			// of the priority tree
			sig_set = mod.Mux(NEW_ID, sig_set, sync_value, pos_trig);

			// Same deal with clear bit
			const auto sync_value_inv = mod.Not(NEW_ID, sync_value);
			sig_clr = mod.Mux(NEW_ID, sig_clr, sync_value_inv, pos_trig);
		}

		auto* cell = mod.addDffsr(
			/*           name */ new_dff_name(),
			/*        sig_clk */ clk.sig,
			/*        sig_set */ sig_set,
			/*        sig_clr */ sig_clr,
			/*          sig_d */ sig_in,
			/*          sig_q */ sig_out,
			/*   clk_polarity */ clk.polarity()
		);
		cell->attributes = proc.attributes;

		log("  created %s cell `%s' with %s edge clock and multiple level-sensitive resets.\n",
			cell->type.c_str(), cell->name.c_str(), clk.polarity_str());
		return true;
	}

	bool empty() const { return sig_out.empty(); }
	size_t size() const { return sig_out.size(); }
	const SigSpec& output() const { return sig_out; }

	// True if there is an explicit clock signal, false if driven by an always
	// or global clock
	bool explicitly_clocked() const { return !always && !clk.empty(); }

private:
	void resize(const size_t new_size) {
		if (new_size >= size())
			return;

		sig_in = sig_in.extract(0, new_size);
		sig_out = sig_out.extract(0, new_size);
		for (auto& [value, _] : async_rules)
			value = value.extract(0, new_size);
	}

	// Given some function that maps from an index to a value, this resizes
	// the dff to a range starting at the LSB that all return the same value
	// from the function as the LSB. This function also returns the value
	// calculated for the LSB.
	template <typename F>
	typename std::invoke_result_t<F, size_t> shrink_while_matching_values(F f) {
		const auto base_val = f(0);

		size_t new_size;
		for (new_size = 1; new_size < size(); new_size++)
			if (f(new_size) != base_val)
				break;

		resize(new_size);
		return base_val;
	}

	RTLIL::Process& proc;
	RTLIL::Module& mod;

	// A clock or reset trigger that is active when sig goes high (low) when
	// inverted is false (true)
	struct TriggerSig {
		SigSpec sig;
		bool inverted = false;

		TriggerSig() = default;
		TriggerSig(const RTLIL::SyncRule& sync) : sig{sync.signal},
			inverted{sync.type == RTLIL::SyncType::ST0 || sync.type == RTLIL::SyncType::STn} {}

		TriggerSig(const RTLIL::SigSpec& signal) : sig{signal} {}

		bool empty() const { return sig.empty(); }
		bool polarity() const { return !inverted; }
		const char* polarity_str() const { return polarity() ? "positive" : "negative"; }

		bool is_never_triggered() const {
			return inverted ? sig.is_fully_ones() : sig.is_fully_zero();
		}

		SigSpec positive_trigger(RTLIL::Module& mod) const {
			if (!inverted)
				return sig;
			return mod.Not(NEW_ID, sig);
		}
	};

	// An update rule to update sig_q to value when trigger is triggered
	struct AsyncRule {
		SigSpec value;
		TriggerSig trigger;

		AsyncRule() = default;
		AsyncRule(const SigSpec& value, const RTLIL::SyncRule& sync) : value{value}, trigger{sync} {}
	};

	// The d input (used when no async rules apply) and q output
	SigSpec sig_in, sig_out;

	// A priority ordered list of asynchronous rules used for set/reset/aload.
	// A rule that comes earlier in this vector has higher priority than a later
	// one (if both of their trigger conditions are met the higher priority
	// value is taken)
	std::vector<AsyncRule> async_rules;

	// The clock signal with its polarity. If clk is empty, the DFF is driven
	// by a global clock (and should have no async rules)
	TriggerSig clk;

	// If this is true, this isn't really a DFF but instead an always assignment
	// that can be made with a connection. clk and async_rules should be empty
	// in this case
	bool always = false;
};

void proc_dff(RTLIL::Module& mod, RTLIL::Process& proc, ConstEval &ce) {
	while (1) {
		// Find a new signal assigned by this process
		const auto sig = find_any_lvalue(proc);
		if (sig.empty())
			break;

		log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
			mod.name.c_str(), log_signal(sig), mod.name.c_str(), proc.name.c_str());

		Dff dff{mod, sig, proc};
		dff.optimize(ce);
		dff.generate();

		// Now that we are done with the signal remove it from the process
		// We must do this after optimizing the dff as to emit an optimal dff
		// type we might not actually use all bits of sig in this iteration
		for (auto* sync : proc.syncs)
		for (auto& action : sync->actions)
			action.first.remove2(dff.output(), &action.second);
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

		for (auto mod : design->modules())
			if (design->selected(mod)) {
				ConstEval ce(mod);
				for (auto &proc_it : mod->processes)
					if (design->selected(mod, proc_it.second))
						proc_dff(*mod, *proc_it.second, ce);
			}
	}
} ProcDffPass;

PRIVATE_NAMESPACE_END
