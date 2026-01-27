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

std::vector<std::vector<RTLIL::SigBit>> compute_disjoint_lvalues(const RTLIL::Process& proc) {
	// We want to partition the bits that appear in the lvalues of sync actions
	// in this process such that two bits are in the same partition (equivalence
	// class) iff they appear in the same set of actions. To do this we maintain
	// a vector of e-classes for bits we have seen thus far, and iteratively
	// process the sync rules, splitting e-classes if only some of their bits
	// appear in the rule. e-class vectors are kept in sorted order to make
	// merging linear.
	std::vector<std::vector<RTLIL::SigBit>> eclasses;

	// For each bit we store the index of its e-class so that we can quickly
	// see which e-classes might be split by a bit appearing in a rule
	dict<RTLIL::SigBit, size_t> eclass_idx;

	// Creates a new e-class, (re)assigning the e-class index of each bit
	// to the new e-class' index
	const auto to_new_eclass = [&](const std::vector<RTLIL::SigBit>&& sig) {
		if (sig.empty())
			return;

		const auto new_idx = eclasses.size();
		for (const auto& bit : sig)
			eclass_idx.emplace(bit, new_idx);

		eclasses.emplace_back(std::move(sig));
	};

	for (const auto* sync : proc.syncs)
	for (const auto& action : sync->actions) {
		if (action.first.empty())
			continue;

		auto lvalue = action.first.to_sigbit_vector();
		std::sort(lvalue.begin(), lvalue.end());
		lvalue.erase(std::unique(lvalue.begin(), lvalue.end()), lvalue.end());

		// We wish to split the existing e-class and lvalue such that the
		// e-class now contains elements in both the original e-class and lvalue,
		// lvalue contains elements that were only in lvalue and the residual
		// contains elements that were only in the e-class
		for (size_t i = 0; i < lvalue.size(); i++) {
			const auto& bit = lvalue[i];
			const auto eclass_it = eclass_idx.find(bit);

			if (eclass_it == eclass_idx.end())
				continue;

			auto& eclass = eclasses.at(eclass_it->second);

			std::vector<RTLIL::SigBit> residual;

			size_t ec_read = 0, ec_write = 0;
			size_t lv_read = i, lv_write = i;
			while (ec_read < eclass.size() && lv_read < lvalue.size()) {
				const auto& ec_bit = eclass[ec_read];
				const auto& lv_bit = lvalue[lv_read];

				// If bit appears in both, it should stay in e-class but not lvalue
				if (ec_bit == lv_bit) {
					if (ec_write != ec_read)
						eclass[ec_write] = ec_bit;
					ec_write++;
					ec_read++;
					lv_read++;
				}
				// If e-class bit is less than lvalue bit, it appears only in e-class
				else if (ec_bit < lv_bit) {
					residual.emplace_back(ec_bit);
					ec_read++;
				}
				// If lvalue bit is less than e-class bit, it appears only in lvalue
				else {
					if (lv_write != lv_read)
						lvalue[lv_write] = lv_bit;
					lv_write++;
					lv_read++;
				}
			}

			// Any remaining e-class elems are not in lvalue so go in residual
			for (; ec_read < eclass.size(); ec_read++)
				residual.emplace_back(eclass[ec_read]);
			eclass.resize(ec_write);

			// Any remaining lvalue elems are not in e-class so stay in lvalue
			// (moved down). We only need to bother doing this if there were
			// gaps and thus lv_write != lv_read
			if (lv_write != lv_read)
				for (; lv_read < eclass.size(); lv_read++)
					lvalue[lv_write++] = lvalue[lv_read];
			lvalue.resize(lv_write);

			to_new_eclass(std::move(residual));
		}

		to_new_eclass(std::move(lvalue));
	}

	return eclasses;
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
				if (sync_edge != nullptr && sync_edge != sync)
					log_error("Multiple edge sensitive events found for this signal!\n");
				sig_out.replace(action.first, action.second, &sig_in);
				sync_edge = sync;
				continue;
			}

			// Always assignments
			if (sync->type == RTLIL::SyncType::STa) {
				if (sync_always != nullptr && sync_always != sync)
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

		log("  created %s cell `%s' with %s edge clock.", cell->type, cell->name, edge);
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
			cell->type, cell->name, clk.polarity_str(), aload.trigger.polarity_str(),
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
			cell->type, cell->name, clk.polarity_str());
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
	for (auto lvalue : compute_disjoint_lvalues(proc)) {
		while (!lvalue.empty()) {
			Dff dff{mod, lvalue, proc};
			dff.optimize(ce);

			const auto& output = dff.output();
			log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
				mod.name, log_signal(output), mod.name, proc.name);

			dff.generate();

			size_t low = 0, high = 0, output_idx = 0;
			while (high < lvalue.size() && output_idx < static_cast<size_t>(output.size())) {
				const auto& lv = lvalue[high];
				const auto& out = output[output_idx];
				if (lv == out) {
					high++;
					output_idx++;
				}
				else if (lv < out) {
					lvalue[low++] = lvalue[high];
				} else {
					log_abort();
				}
			}

			if (high != low) {
				for (; high < lvalue.size(); high++)
					lvalue[low++] = lvalue[high];

				lvalue.resize(low);
			}

		}
	}

	for (auto* sync : proc.syncs)
		sync->actions.clear();
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

		for (auto mod : design->all_selected_modules()) {
			ConstEval ce(mod);
			for (auto proc : mod->selected_processes())
				proc_dff(*mod, *proc, ce);
		}
	}
} ProcDffPass;

PRIVATE_NAMESPACE_END
