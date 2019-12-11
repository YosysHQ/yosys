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

// [[CITE]] Temporal Induction by Incremental SAT Solving
// Niklas Een and Niklas Sörensson (2003)
// http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.4.8161

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/satgen.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <errno.h>
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SatHelper
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	SigMap sigmap;
	CellTypes ct;

	ezSatPtr ez;
	SatGen satgen;

	// additional constraints
	std::vector<std::pair<std::string, std::string>> sets, prove, prove_x, sets_init;
	std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
	std::map<int, std::vector<std::string>> unsets_at;
	bool prove_asserts, set_assumes;

	// undef constraints
	bool enable_undef, set_init_def, set_init_undef, set_init_zero, ignore_unknown_cells;
	std::vector<std::string> sets_def, sets_any_undef, sets_all_undef;
	std::map<int, std::vector<std::string>> sets_def_at, sets_any_undef_at, sets_all_undef_at;

	// model variables
	std::vector<std::string> shows;
	SigPool show_signal_pool;
	SigSet<RTLIL::Cell*> show_drivers;
	int max_timestep, timeout;
	bool gotTimeout;

	SatHelper(RTLIL::Design *design, RTLIL::Module *module, bool enable_undef) :
		design(design), module(module), sigmap(module), ct(design), satgen(ez.get(), &sigmap)
	{
		this->enable_undef = enable_undef;
		satgen.model_undef = enable_undef;
		set_init_def = false;
		set_init_undef = false;
		set_init_zero = false;
		ignore_unknown_cells = false;
		max_timestep = -1;
		timeout = 0;
		gotTimeout = false;
	}

	void check_undef_enabled(const RTLIL::SigSpec &sig)
	{
		if (enable_undef)
			return;

		std::vector<RTLIL::SigBit> sigbits = sig.to_sigbit_vector();
		for (size_t i = 0; i < sigbits.size(); i++)
			if (sigbits[i].wire == NULL && sigbits[i].data == RTLIL::State::Sx)
				log_cmd_error("Bit %d of %s is undef but option -enable_undef is missing!\n", int(i), log_signal(sig));
	}

	void setup(int timestep = -1, bool initstate = false)
	{
		if (timestep > 0)
			log ("\nSetting up time step %d:\n", timestep);
		else
			log ("\nSetting up SAT problem:\n");

		if (initstate)
			satgen.setInitState(timestep);

		if (timestep > max_timestep)
			max_timestep = timestep;

		RTLIL::SigSpec big_lhs, big_rhs;

		for (auto &s : sets)
		{
			RTLIL::SigSpec lhs, rhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.size() != rhs.size())
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

			log("Import set-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : sets_at[timestep])
		{
			RTLIL::SigSpec lhs, rhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.size() != rhs.size())
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

			log("Import set-constraint for this timestep: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : unsets_at[timestep])
		{
			RTLIL::SigSpec lhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.c_str());
			show_signal_pool.add(sigmap(lhs));

			log("Import unset-constraint for this timestep: %s\n", log_signal(lhs));
			big_lhs.remove2(lhs, &big_rhs);
		}

		log("Final constraint equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
		check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
		ez->assume(satgen.signals_eq(big_lhs, big_rhs, timestep));

		// 0 = sets_def
		// 1 = sets_any_undef
		// 2 = sets_all_undef
		std::set<RTLIL::SigSpec> sets_def_undef[3];

		for (auto &s : sets_def) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].insert(sig);
		}

		for (auto &s : sets_any_undef) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[1].insert(sig);
		}

		for (auto &s : sets_all_undef) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[2].insert(sig);
		}

		for (auto &s : sets_def_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].insert(sig);
			sets_def_undef[1].erase(sig);
			sets_def_undef[2].erase(sig);
		}

		for (auto &s : sets_any_undef_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].erase(sig);
			sets_def_undef[1].insert(sig);
			sets_def_undef[2].erase(sig);
		}

		for (auto &s : sets_all_undef_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].erase(sig);
			sets_def_undef[1].erase(sig);
			sets_def_undef[2].insert(sig);
		}

		for (int t = 0; t < 3; t++)
		for (auto &sig : sets_def_undef[t]) {
			log("Import %s constraint for this timestep: %s\n", t == 0 ? "def" : t == 1 ? "any_undef" : "all_undef", log_signal(sig));
			std::vector<int> undef_sig = satgen.importUndefSigSpec(sig, timestep);
			if (t == 0)
				ez->assume(ez->NOT(ez->expression(ezSAT::OpOr, undef_sig)));
			if (t == 1)
				ez->assume(ez->expression(ezSAT::OpOr, undef_sig));
			if (t == 2)
				ez->assume(ez->expression(ezSAT::OpAnd, undef_sig));
		}

		int import_cell_counter = 0;
		for (auto cell : module->cells())
			if (design->selected(module, cell)) {
				// log("Import cell: %s\n", RTLIL::id2cstr(cell->name));
				if (satgen.importCell(cell, timestep)) {
					for (auto &p : cell->connections())
						if (ct.cell_output(cell->type, p.first))
							show_drivers.insert(sigmap(p.second), cell);
					import_cell_counter++;
				} else if (ignore_unknown_cells)
					log_warning("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
				else
					log_error("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
		}
		log("Imported %d cells to SAT database.\n", import_cell_counter);

		if (set_assumes) {
			RTLIL::SigSpec assumes_a, assumes_en;
			satgen.getAssumes(assumes_a, assumes_en, timestep);
			for (int i = 0; i < GetSize(assumes_a); i++)
				log("Import constraint from assume cell: %s when %s.\n", log_signal(assumes_a[i]), log_signal(assumes_en[i]));
			ez->assume(satgen.importAssumes(timestep));
		}

		if (initstate)
		{
			RTLIL::SigSpec big_lhs, big_rhs;

			for (auto &it : module->wires_)
			{
				if (it.second->attributes.count("\\init") == 0)
					continue;

				RTLIL::SigSpec lhs = sigmap(it.second);
				RTLIL::SigSpec rhs = it.second->attributes.at("\\init");
				log_assert(lhs.size() == rhs.size());

				RTLIL::SigSpec removed_bits;
				for (int i = 0; i < lhs.size(); i++) {
					RTLIL::SigSpec bit = lhs.extract(i, 1);
					if (rhs[i] == State::Sx || !satgen.initial_state.check_all(bit)) {
						if (rhs[i] != State::Sx)
							removed_bits.append(bit);
						lhs.remove(i, 1);
						rhs.remove(i, 1);
						i--;
					}
				}

				if (removed_bits.size())
					log_warning("ignoring initial value on non-register: %s\n", log_signal(removed_bits));

				if (lhs.size()) {
					log("Import set-constraint from init attribute: %s = %s\n", log_signal(lhs), log_signal(rhs));
					big_lhs.remove2(lhs, &big_rhs);
					big_lhs.append(lhs);
					big_rhs.append(rhs);
				}
			}

			for (auto &s : sets_init)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import init set-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			if (!satgen.initial_state.check_all(big_lhs)) {
				RTLIL::SigSpec rem = satgen.initial_state.remove(big_lhs);
				log_cmd_error("Found -set-init bits that are not part of the initial_state: %s\n", log_signal(rem));
			}

			if (set_init_def) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				std::vector<int> undef_rem = satgen.importUndefSigSpec(rem, 1);
				ez->assume(ez->NOT(ez->expression(ezSAT::OpOr, undef_rem)));
			}

			if (set_init_undef) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				rem.remove(big_lhs);
				big_lhs.append(rem);
				big_rhs.append(RTLIL::SigSpec(RTLIL::State::Sx, rem.size()));
			}

			if (set_init_zero) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				rem.remove(big_lhs);
				big_lhs.append(rem);
				big_rhs.append(RTLIL::SigSpec(RTLIL::State::S0, rem.size()));
			}

			if (big_lhs.size() == 0) {
				log("No constraints for initial state found.\n\n");
				return;
			}

			log("Final init constraint equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
			check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
			ez->assume(satgen.signals_eq(big_lhs, big_rhs, timestep));
		}
	}

	int setup_proof(int timestep = -1)
	{
		log_assert(prove.size() || prove_x.size() || prove_asserts);

		RTLIL::SigSpec big_lhs, big_rhs;
		std::vector<int> prove_bits;

		if (prove.size() > 0)
		{
			for (auto &s : prove)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs proof expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs proof expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Proof expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import proof-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			log("Final proof equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
			check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
			prove_bits.push_back(satgen.signals_eq(big_lhs, big_rhs, timestep));
		}

		if (prove_x.size() > 0)
		{
			for (auto &s : prove_x)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs proof-x expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs proof-x expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Proof-x expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import proof-x-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			log("Final proof-x equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));

			std::vector<int> value_lhs = satgen.importDefSigSpec(big_lhs, timestep);
			std::vector<int> value_rhs = satgen.importDefSigSpec(big_rhs, timestep);

			std::vector<int> undef_lhs = satgen.importUndefSigSpec(big_lhs, timestep);
			std::vector<int> undef_rhs = satgen.importUndefSigSpec(big_rhs, timestep);

			for (size_t i = 0; i < value_lhs.size(); i++)
				prove_bits.push_back(ez->OR(undef_lhs.at(i), ez->AND(ez->NOT(undef_rhs.at(i)), ez->NOT(ez->XOR(value_lhs.at(i), value_rhs.at(i))))));
		}

		if (prove_asserts) {
			RTLIL::SigSpec asserts_a, asserts_en;
			satgen.getAsserts(asserts_a, asserts_en, timestep);
			for (int i = 0; i < GetSize(asserts_a); i++)
				log("Import proof for assert: %s when %s.\n", log_signal(asserts_a[i]), log_signal(asserts_en[i]));
			prove_bits.push_back(satgen.importAsserts(timestep));
		}

		return ez->expression(ezSAT::OpAnd, prove_bits);
	}

	void force_unique_state(int timestep_from, int timestep_to)
	{
		RTLIL::SigSpec state_signals = satgen.initial_state.export_all();
		for (int i = timestep_from; i < timestep_to; i++)
			ez->assume(ez->NOT(satgen.signals_eq(state_signals, state_signals, i, timestep_to)));
	}

	bool solve(const std::vector<int> &assumptions)
	{
		log_assert(gotTimeout == false);
		ez->setSolverTimeout(timeout);
		bool success = ez->solve(modelExpressions, modelValues, assumptions);
		if (ez->getSolverTimoutStatus())
			gotTimeout = true;
		return success;
	}

	bool solve(int a = 0, int b = 0, int c = 0, int d = 0, int e = 0, int f = 0)
	{
		log_assert(gotTimeout == false);
		ez->setSolverTimeout(timeout);
		bool success = ez->solve(modelExpressions, modelValues, a, b, c, d, e, f);
		if (ez->getSolverTimoutStatus())
			gotTimeout = true;
		return success;
	}

	struct ModelBlockInfo {
		int timestep, offset, width;
		std::string description;
		bool operator < (const ModelBlockInfo &other) const {
			if (timestep != other.timestep)
				return timestep < other.timestep;
			if (description != other.description)
				return description < other.description;
			if (offset != other.offset)
				return offset < other.offset;
			if (width != other.width)
				return width < other.width;
			return false;
		}
	};

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;
	std::set<ModelBlockInfo> modelInfo;

	void maximize_undefs()
	{
		log_assert(enable_undef);
		std::vector<bool> backupValues;

		while (1)
		{
			std::vector<int> must_undef, maybe_undef;

			for (size_t i = 0; i < modelExpressions.size()/2; i++)
				if (modelValues.at(modelExpressions.size()/2 + i))
					must_undef.push_back(modelExpressions.at(modelExpressions.size()/2 + i));
				else
					maybe_undef.push_back(modelExpressions.at(modelExpressions.size()/2 + i));

			backupValues.swap(modelValues);
			if (!solve(ez->expression(ezSAT::OpAnd, must_undef), ez->expression(ezSAT::OpOr, maybe_undef)))
				break;
		}

		backupValues.swap(modelValues);
	}

	void generate_model()
	{
		RTLIL::SigSpec modelSig;
		modelExpressions.clear();
		modelInfo.clear();

		// Add "show" signals or alternatively the leaves on the input cone on all set and prove signals

		if (shows.size() == 0)
		{
			SigPool queued_signals, handled_signals, final_signals;
			queued_signals = show_signal_pool;
			while (queued_signals.size() > 0) {
				RTLIL::SigSpec sig = queued_signals.export_one();
				queued_signals.del(sig);
				handled_signals.add(sig);
				std::set<RTLIL::Cell*> drivers = show_drivers.find(sig);
				if (drivers.size() == 0) {
					final_signals.add(sig);
				} else {
					for (auto &d : drivers)
					for (auto &p : d->connections()) {
						if (d->type == "$dff" && p.first == "\\CLK")
							continue;
						if (d->type.begins_with("$_DFF_") && p.first == "\\C")
							continue;
						queued_signals.add(handled_signals.remove(sigmap(p.second)));
					}
				}
			}
			modelSig = final_signals.export_all();

			// additionally add all set and prove signals directly
			// (it improves user confidence if we write the constraints back ;-)
			modelSig.append(show_signal_pool.export_all());
		}
		else
		{
			for (auto &s : shows) {
				RTLIL::SigSpec sig;
				if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
					log_cmd_error("Failed to parse show expression `%s'.\n", s.c_str());
				log("Import show expression: %s\n", log_signal(sig));
				modelSig.append(sig);
			}
		}

		modelSig.sort_and_unify();
		// log("Model signals: %s\n", log_signal(modelSig));

		std::vector<int> modelUndefExpressions;

		for (auto &c : modelSig.chunks())
			if (c.wire != NULL)
			{
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;
				info.width = chunksig.size();
				info.description = log_signal(chunksig);

				for (int timestep = -1; timestep <= max_timestep; timestep++)
				{
					if ((timestep == -1 && max_timestep > 0) || timestep == 0)
						continue;

					info.timestep = timestep;
					info.offset = modelExpressions.size();
					modelInfo.insert(info);

					std::vector<int> vec = satgen.importSigSpec(chunksig, timestep);
					modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());

					if (enable_undef) {
						std::vector<int> undef_vec = satgen.importUndefSigSpec(chunksig, timestep);
						modelUndefExpressions.insert(modelUndefExpressions.end(), undef_vec.begin(), undef_vec.end());
					}
				}
			}

		// Add initial state signals as collected by satgen
		//
		modelSig = satgen.initial_state.export_all();
		for (auto &c : modelSig.chunks())
			if (c.wire != NULL)
			{
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;

				info.timestep = 0;
				info.offset = modelExpressions.size();
				info.width = chunksig.size();
				info.description = log_signal(chunksig);
				modelInfo.insert(info);

				std::vector<int> vec = satgen.importSigSpec(chunksig, 1);
				modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());

				if (enable_undef) {
					std::vector<int> undef_vec = satgen.importUndefSigSpec(chunksig, 1);
					modelUndefExpressions.insert(modelUndefExpressions.end(), undef_vec.begin(), undef_vec.end());
				}
			}

		modelExpressions.insert(modelExpressions.end(), modelUndefExpressions.begin(), modelUndefExpressions.end());
	}

	void print_model()
	{
		int maxModelName = 10;
		int maxModelWidth = 10;

		for (auto &info : modelInfo) {
			maxModelName = max(maxModelName, int(info.description.size()));
			maxModelWidth = max(maxModelWidth, info.width);
		}

		log("\n");

		int last_timestep = -2;
		for (auto &info : modelInfo)
		{
			RTLIL::Const value;
			bool found_undef = false;

			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx, found_undef = true;
			}

			if (info.timestep != last_timestep) {
				const char *hline = "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------";
				if (last_timestep == -2) {
					log(max_timestep > 0 ? "  Time " : "  ");
					log("%-*s %11s %9s %*s\n", maxModelName+5, "Signal Name", "Dec", "Hex", maxModelWidth+3, "Bin");
				}
				log(max_timestep > 0 ? "  ---- " : "  ");
				log("%*.*s %11.11s %9.9s %*.*s\n", maxModelName+5, maxModelName+5,
						hline, hline, hline, maxModelWidth+3, maxModelWidth+3, hline);
				last_timestep = info.timestep;
			}

			if (max_timestep > 0) {
				if (info.timestep > 0)
					log("  %4d ", info.timestep);
				else
					log("  init ");
			} else
				log("  ");

			if (info.width <= 32 && !found_undef)
				log("%-*s %11d %9x %*s\n", maxModelName+5, info.description.c_str(), value.as_int(), value.as_int(), maxModelWidth+3, value.as_string().c_str());
			else
				log("%-*s %11s %9s %*s\n", maxModelName+5, info.description.c_str(), "--", "--", maxModelWidth+3, value.as_string().c_str());
		}

		if (last_timestep == -2)
			log("  no model variables selected for display.\n");
	}

	void dump_model_to_vcd(std::string vcd_file_name)
	{
		rewrite_filename(vcd_file_name);
		FILE *f = fopen(vcd_file_name.c_str(), "w");
		if (!f)
			log_cmd_error("Can't open output file `%s' for writing: %s\n", vcd_file_name.c_str(), strerror(errno));

		log("Dumping SAT model to VCD file %s\n", vcd_file_name.c_str());

		time_t timestamp;
		struct tm* now;
		char stime[128] = {};
		time(&timestamp);
		now = localtime(&timestamp);
		strftime(stime, sizeof(stime), "%c", now);

		std::string module_fname = "unknown";
		auto apos = module->attributes.find("\\src");
		if(apos != module->attributes.end())
			module_fname = module->attributes["\\src"].decode_string();

		fprintf(f, "$date\n");
		fprintf(f, "    %s\n", stime);
		fprintf(f, "$end\n");
		fprintf(f, "$version\n");
		fprintf(f, "    Generated by %s\n", yosys_version_str);
		fprintf(f, "$end\n");
		fprintf(f, "$comment\n");
		fprintf(f, "    Generated from SAT problem in module %s (declared at %s)\n",
			module->name.c_str(), module_fname.c_str());
		fprintf(f, "$end\n");

		// VCD has some limits on internal (non-display) identifier names, so make legal ones
		std::map<std::string, std::string> vcdnames;

		fprintf(f, "$scope module %s $end\n", module->name.c_str());
		for (auto &info : modelInfo)
		{
			if (vcdnames.find(info.description) != vcdnames.end())
				continue;

			char namebuf[16];
			snprintf(namebuf, sizeof(namebuf), "v%d", static_cast<int>(vcdnames.size()));
			vcdnames[info.description] = namebuf;

			// Even display identifiers can't use some special characters
			std::string legal_desc = info.description.c_str();
			for (auto &c : legal_desc) {
				if(c == '$')
					c = '_';
				if(c == ':')
					c = '_';
			}

			fprintf(f, "$var wire %d %s %s $end\n", info.width, namebuf, legal_desc.c_str());

			// Need to look at first *two* cycles!
			// We need to put a name on all variables but those without an initialization clause
			// have no value at timestep 0
			if(info.timestep > 1)
				break;
		}
		fprintf(f, "$upscope $end\n");
		fprintf(f, "$enddefinitions $end\n");
		fprintf(f, "$dumpvars\n");

		static const char bitvals[] = "01xzxx";

		int last_timestep = -2;
		for (auto &info : modelInfo)
		{
			RTLIL::Const value;

			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx;
			}

			if (info.timestep != last_timestep) {
				if(last_timestep == 0)
					fprintf(f, "$end\n");
				else
					fprintf(f, "#%d\n", info.timestep);
				last_timestep = info.timestep;
			}

			if(info.width == 1) {
				fprintf(f, "%c%s\n", bitvals[value.bits[0]], vcdnames[info.description].c_str());
			} else {
				fprintf(f, "b");
				for(int k=info.width-1; k >= 0; k --)	//need to flip bit ordering for VCD
					fprintf(f, "%c", bitvals[value.bits[k]]);
				fprintf(f, " %s\n", vcdnames[info.description].c_str());
			}
		}

		if (last_timestep == -2)
			log("  no model variables selected for display.\n");

		fclose(f);
	}

	void dump_model_to_json(std::string json_file_name)
	{
		rewrite_filename(json_file_name);
		FILE *f = fopen(json_file_name.c_str(), "w");
		if (!f)
			log_cmd_error("Can't open output file `%s' for writing: %s\n", json_file_name.c_str(), strerror(errno));

		log("Dumping SAT model to WaveJSON file '%s'.\n", json_file_name.c_str());

		int mintime = 1, maxtime = 0, maxwidth = 0;;
		dict<string, pair<int, dict<int, Const>>> wavedata;

		for (auto &info : modelInfo)
		{
			Const value;
			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx;
			}

			wavedata[info.description].first = info.width;
			wavedata[info.description].second[info.timestep] = value;
			mintime = min(mintime, info.timestep);
			maxtime = max(maxtime, info.timestep);
			maxwidth = max(maxwidth, info.width);
		}

		fprintf(f, "{ \"signal\": [");
		bool fist_wavedata = true;
		for (auto &wd : wavedata)
		{
			fprintf(f, "%s", fist_wavedata ? "\n" : ",\n");
			fist_wavedata = false;

			vector<string> data;
			string name = wd.first.c_str();
			while (name.compare(0, 1, "\\") == 0)
				name = name.substr(1);

			fprintf(f, "    { \"name\": \"%s\", \"wave\": \"", name.c_str());
			for (int i = mintime; i <= maxtime; i++) {
				if (wd.second.second.count(i)) {
					string this_data = wd.second.second[i].as_string();
					char ch = '=';
					if (wd.second.first == 1)
						ch = this_data[0];
					if (!data.empty() && data.back() == this_data) {
						fprintf(f, ".");
					} else {
						data.push_back(this_data);
						fprintf(f, "%c", ch);
					}
				} else {
					data.push_back("");
					fprintf(f, "4");
				}
			}
			if (wd.second.first != 1) {
				fprintf(f, "\", \"data\": [");
				for (int i = 0; i < GetSize(data); i++)
					 fprintf(f, "%s\"%s\"", i ? ", " : "", data[i].c_str());
				fprintf(f, "] }");
			} else {
				fprintf(f, "\" }");
			}
		}
		fprintf(f, "\n  ],\n");
		fprintf(f, "  \"config\": {\n");
		fprintf(f, "    \"hscale\": %.2f\n", maxwidth / 4.0);
		fprintf(f, "  }\n");
		fprintf(f, "}\n");
		fclose(f);
	}

	void invalidate_model(bool max_undef)
	{
		std::vector<int> clause;
		if (enable_undef) {
			for (size_t i = 0; i < modelExpressions.size()/2; i++) {
				int bit = modelExpressions.at(i), bit_undef = modelExpressions.at(modelExpressions.size()/2 + i);
				bool val = modelValues.at(i), val_undef = modelValues.at(modelExpressions.size()/2 + i);
				if (!max_undef || !val_undef)
					clause.push_back(val_undef ? ez->NOT(bit_undef) : val ? ez->NOT(bit) : bit);
			}
		} else
			for (size_t i = 0; i < modelExpressions.size(); i++)
				clause.push_back(modelValues.at(i) ? ez->NOT(modelExpressions.at(i)) : modelExpressions.at(i));
		ez->assume(ez->expression(ezSAT::OpOr, clause));
	}
};

void print_proof_failed()
{
	log("\n");
	log("   ______                   ___       ___       _ _            _ _ \n");
	log("  (_____ \\                 / __)     / __)     (_) |          | | |\n");
	log("   _____) )___ ___   ___ _| |__    _| |__ _____ _| | _____  __| | |\n");
	log("  |  ____/ ___) _ \\ / _ (_   __)  (_   __|____ | | || ___ |/ _  |_|\n");
	log("  | |   | |  | |_| | |_| || |       | |  / ___ | | || ____( (_| |_ \n");
	log("  |_|   |_|   \\___/ \\___/ |_|       |_|  \\_____|_|\\_)_____)\\____|_|\n");
	log("\n");
}

void print_timeout()
{
	log("\n");
	log("        _____  _  _      _____ ____  _     _____\n");
	log("       /__ __\\/ \\/ \\__/|/  __//  _ \\/ \\ /\\/__ __\\\n");
	log("         / \\  | || |\\/|||  \\  | / \\|| | ||  / \\\n");
	log("         | |  | || |  |||  /_ | \\_/|| \\_/|  | |\n");
	log("         \\_/  \\_/\\_/  \\|\\____\\\\____/\\____/  \\_/\n");
	log("\n");
}

void print_qed()
{
	log("\n");
	log("                  /$$$$$$      /$$$$$$$$     /$$$$$$$    \n");
	log("                 /$$__  $$    | $$_____/    | $$__  $$   \n");
	log("                | $$  \\ $$    | $$          | $$  \\ $$   \n");
	log("                | $$  | $$    | $$$$$       | $$  | $$   \n");
	log("                | $$  | $$    | $$__/       | $$  | $$   \n");
	log("                | $$/$$ $$    | $$          | $$  | $$   \n");
	log("                |  $$$$$$/ /$$| $$$$$$$$ /$$| $$$$$$$//$$\n");
	log("                 \\____ $$$|__/|________/|__/|_______/|__/\n");
	log("                       \\__/                              \n");
	log("\n");
}

struct SatPass : public Pass {
	SatPass() : Pass("sat", "solve a SAT problem in the circuit") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sat [options] [selection]\n");
		log("\n");
		log("This command solves a SAT problem defined over the currently selected circuit\n");
		log("and additional constraints passed as parameters.\n");
		log("\n");
		log("    -all\n");
		log("        show all solutions to the problem (this can grow exponentially, use\n");
		log("        -max <N> instead to get <N> solutions)\n");
		log("\n");
		log("    -max <N>\n");
		log("        like -all, but limit number of solutions to <N>\n");
		log("\n");
		log("    -enable_undef\n");
		log("        enable modeling of undef value (aka 'x-bits')\n");
		log("        this option is implied by -set-def, -set-undef et. cetera\n");
		log("\n");
		log("    -max_undef\n");
		log("        maximize the number of undef bits in solutions, giving a better\n");
		log("        picture of which input bits are actually vital to the solution.\n");
		log("\n");
		log("    -set <signal> <value>\n");
		log("        set the specified signal to the specified value.\n");
		log("\n");
		log("    -set-def <signal>\n");
		log("        add a constraint that all bits of the given signal must be defined\n");
		log("\n");
		log("    -set-any-undef <signal>\n");
		log("        add a constraint that at least one bit of the given signal is undefined\n");
		log("\n");
		log("    -set-all-undef <signal>\n");
		log("        add a constraint that all bits of the given signal are undefined\n");
		log("\n");
		log("    -set-def-inputs\n");
		log("        add -set-def constraints for all module inputs\n");
		log("\n");
		log("    -show <signal>\n");
		log("        show the model for the specified signal. if no -show option is\n");
		log("        passed then a set of signals to be shown is automatically selected.\n");
		log("\n");
		log("    -show-inputs, -show-outputs, -show-ports\n");
		log("        add all module (input/output) ports to the list of shown signals\n");
		log("\n");
		log("    -show-regs, -show-public, -show-all\n");
		log("        show all registers, show signals with 'public' names, show all signals\n");
		log("\n");
		log("    -ignore_div_by_zero\n");
		log("        ignore all solutions that involve a division by zero\n");
		log("\n");
		log("    -ignore_unknown_cells\n");
		log("        ignore all cells that can not be matched to a SAT model\n");
		log("\n");
		log("The following options can be used to set up a sequential problem:\n");
		log("\n");
		log("    -seq <N>\n");
		log("        set up a sequential problem with <N> time steps. The steps will\n");
		log("        be numbered from 1 to N.\n");
		log("\n");
		log("        note: for large <N> it can be significantly faster to use\n");
		log("        -tempinduct-baseonly -maxsteps <N> instead of -seq <N>.\n");
		log("\n");
		log("    -set-at <N> <signal> <value>\n");
		log("    -unset-at <N> <signal>\n");
		log("        set or unset the specified signal to the specified value in the\n");
		log("        given timestep. this has priority over a -set for the same signal.\n");
		log("\n");
		log("    -set-assumes\n");
		log("        set all assumptions provided via $assume cells\n");
		log("\n");
		log("    -set-def-at <N> <signal>\n");
		log("    -set-any-undef-at <N> <signal>\n");
		log("    -set-all-undef-at <N> <signal>\n");
		log("        add undef constraints in the given timestep.\n");
		log("\n");
		log("    -set-init <signal> <value>\n");
		log("        set the initial value for the register driving the signal to the value\n");
		log("\n");
		log("    -set-init-undef\n");
		log("        set all initial states (not set using -set-init) to undef\n");
		log("\n");
		log("    -set-init-def\n");
		log("        do not force a value for the initial state but do not allow undef\n");
		log("\n");
		log("    -set-init-zero\n");
		log("        set all initial states (not set using -set-init) to zero\n");
		log("\n");
		log("    -dump_vcd <vcd-file-name>\n");
		log("        dump SAT model (counter example in proof) to VCD file\n");
		log("\n");
		log("    -dump_json <json-file-name>\n");
		log("        dump SAT model (counter example in proof) to a WaveJSON file.\n");
		log("\n");
		log("    -dump_cnf <cnf-file-name>\n");
		log("        dump CNF of SAT problem (in DIMACS format). in temporal induction\n");
		log("        proofs this is the CNF of the first induction step.\n");
		log("\n");
		log("The following additional options can be used to set up a proof. If also -seq\n");
		log("is passed, a temporal induction proof is performed.\n");
		log("\n");
		log("    -tempinduct\n");
		log("        Perform a temporal induction proof. In a temporal induction proof it is\n");
		log("        proven that the condition holds forever after the number of time steps\n");
		log("        specified using -seq.\n");
		log("\n");
		log("    -tempinduct-def\n");
		log("        Perform a temporal induction proof. Assume an initial state with all\n");
		log("        registers set to defined values for the induction step.\n");
		log("\n");
		log("    -tempinduct-baseonly\n");
		log("        Run only the basecase half of temporal induction (requires -maxsteps)\n");
		log("\n");
		log("    -tempinduct-inductonly\n");
		log("        Run only the induction half of temporal induction\n");
		log("\n");
		log("    -tempinduct-skip <N>\n");
		log("        Skip the first <N> steps of the induction proof.\n");
		log("\n");
		log("        note: this will assume that the base case holds for <N> steps.\n");
		log("        this must be proven independently with \"-tempinduct-baseonly\n");
		log("        -maxsteps <N>\". Use -initsteps if you just want to set a\n");
		log("        minimal induction length.\n");
		log("\n");
		log("    -prove <signal> <value>\n");
		log("        Attempt to proof that <signal> is always <value>.\n");
		log("\n");
		log("    -prove-x <signal> <value>\n");
		log("        Like -prove, but an undef (x) bit in the lhs matches any value on\n");
		log("        the right hand side. Useful for equivalence checking.\n");
		log("\n");
		log("    -prove-asserts\n");
		log("        Prove that all asserts in the design hold.\n");
		log("\n");
		log("    -prove-skip <N>\n");
		log("        Do not enforce the prove-condition for the first <N> time steps.\n");
		log("\n");
		log("    -maxsteps <N>\n");
		log("        Set a maximum length for the induction.\n");
		log("\n");
		log("    -initsteps <N>\n");
		log("        Set initial length for the induction.\n");
		log("        This will speed up the search of the right induction length\n");
		log("        for deep induction proofs.\n");
		log("\n");
		log("    -stepsize <N>\n");
		log("        Increase the size of the induction proof in steps of <N>.\n");
		log("        This will speed up the search of the right induction length\n");
		log("        for deep induction proofs.\n");
		log("\n");
		log("    -timeout <N>\n");
		log("        Maximum number of seconds a single SAT instance may take.\n");
		log("\n");
		log("    -verify\n");
		log("        Return an error and stop the synthesis script if the proof fails.\n");
		log("\n");
		log("    -verify-no-timeout\n");
		log("        Like -verify but do not return an error for timeouts.\n");
		log("\n");
		log("    -falsify\n");
		log("        Return an error and stop the synthesis script if the proof succeeds.\n");
		log("\n");
		log("    -falsify-no-timeout\n");
		log("        Like -falsify but do not return an error for timeouts.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::vector<std::pair<std::string, std::string>> sets, sets_init, prove, prove_x;
		std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
		std::map<int, std::vector<std::string>> unsets_at, sets_def_at, sets_any_undef_at, sets_all_undef_at;
		std::vector<std::string> shows, sets_def, sets_any_undef, sets_all_undef;
		int loopcount = 0, seq_len = 0, maxsteps = 0, initsteps = 0, timeout = 0, prove_skip = 0;
		bool verify = false, fail_on_timeout = false, enable_undef = false, set_def_inputs = false;
		bool ignore_div_by_zero = false, set_init_undef = false, set_init_zero = false, max_undef = false;
		bool tempinduct = false, prove_asserts = false, show_inputs = false, show_outputs = false;
		bool show_regs = false, show_public = false, show_all = false;
		bool ignore_unknown_cells = false, falsify = false, tempinduct_def = false, set_init_def = false;
		bool tempinduct_baseonly = false, tempinduct_inductonly = false, set_assumes = false;
		int tempinduct_skip = 0, stepsize = 1;
		std::string vcd_file_name, json_file_name, cnf_file_name;

		log_header(design, "Executing SAT pass (solving SAT problems in the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all") {
				loopcount = -1;
				continue;
			}
			if (args[argidx] == "-verify") {
				fail_on_timeout = true;
				verify = true;
				continue;
			}
			if (args[argidx] == "-verify-no-timeout") {
				verify = true;
				continue;
			}
			if (args[argidx] == "-falsify") {
				fail_on_timeout = true;
				falsify = true;
				continue;
			}
			if (args[argidx] == "-falsify-no-timeout") {
				falsify = true;
				continue;
			}
			if (args[argidx] == "-timeout" && argidx+1 < args.size()) {
				timeout = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max" && argidx+1 < args.size()) {
				loopcount = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-maxsteps" && argidx+1 < args.size()) {
				maxsteps = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-initsteps" && argidx+1 < args.size()) {
				initsteps = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-stepsize" && argidx+1 < args.size()) {
				stepsize = max(1, atoi(args[++argidx].c_str()));
				continue;
			}
			if (args[argidx] == "-ignore_div_by_zero") {
				ignore_div_by_zero = true;
				continue;
			}
			if (args[argidx] == "-enable_undef") {
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-max_undef") {
				enable_undef = true;
				max_undef = true;
				continue;
			}
			if (args[argidx] == "-set-def-inputs") {
				enable_undef = true;
				set_def_inputs = true;
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-def" && argidx+1 < args.size()) {
				sets_def.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-any-undef" && argidx+1 < args.size()) {
				sets_any_undef.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-all-undef" && argidx+1 < args.size()) {
				sets_all_undef.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-assumes") {
				set_assumes = true;
				continue;
			}
			if (args[argidx] == "-tempinduct") {
				tempinduct = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-def") {
				tempinduct = true;
				tempinduct_def = true;
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-baseonly") {
				tempinduct = true;
				tempinduct_baseonly = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-inductonly") {
				tempinduct = true;
				tempinduct_inductonly = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-skip" && argidx+1 < args.size()) {
				tempinduct_skip = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-prove" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				prove.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-prove-x" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				prove_x.push_back(std::pair<std::string, std::string>(lhs, rhs));
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-prove-asserts") {
				prove_asserts = true;
				continue;
			}
			if (args[argidx] == "-prove-skip" && argidx+1 < args.size()) {
				prove_skip = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-seq" && argidx+1 < args.size()) {
				seq_len = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-set-at" && argidx+3 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets_at[timestep].push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-unset-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				unsets_at[timestep].push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-set-def-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_def_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-any-undef-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_any_undef_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-all-undef-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_all_undef_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-init" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets_init.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-init-undef") {
				set_init_undef = true;
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-init-def") {
				set_init_def = true;
				continue;
			}
			if (args[argidx] == "-set-init-zero") {
				set_init_zero = true;
				continue;
			}
			if (args[argidx] == "-show" && argidx+1 < args.size()) {
				shows.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-show-inputs") {
				show_inputs = true;
				continue;
			}
			if (args[argidx] == "-show-outputs") {
				show_outputs = true;
				continue;
			}
			if (args[argidx] == "-show-ports") {
				show_inputs = true;
				show_outputs = true;
				continue;
			}
			if (args[argidx] == "-show-regs") {
				show_regs = true;
				continue;
			}
			if (args[argidx] == "-show-public") {
				show_public = true;
				continue;
			}
			if (args[argidx] == "-show-all") {
				show_all = true;
				continue;
			}
			if (args[argidx] == "-ignore_unknown_cells") {
				ignore_unknown_cells = true;
				continue;
			}
			if (args[argidx] == "-dump_vcd" && argidx+1 < args.size()) {
				vcd_file_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dump_json" && argidx+1 < args.size()) {
				json_file_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dump_cnf" && argidx+1 < args.size()) {
				cnf_file_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = NULL;
		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module must be selected for the SAT pass! (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == NULL)
			log_cmd_error("Can't perform SAT on an empty selection!\n");

		if (!prove.size() && !prove_x.size() && !prove_asserts && tempinduct)
			log_cmd_error("Got -tempinduct but nothing to prove!\n");

		if (prove_skip && tempinduct)
			log_cmd_error("Options -prove-skip and -tempinduct don't work with each other. Use -seq instead of -prove-skip.\n");

		if (prove_skip >= seq_len && prove_skip > 0)
			log_cmd_error("The value of -prove-skip must be smaller than the one of -seq.\n");

		if (set_init_undef + set_init_zero + set_init_def > 1)
			log_cmd_error("The options -set-init-undef, -set-init-def, and -set-init-zero are exclusive!\n");

		if (set_def_inputs) {
			for (auto &it : module->wires_)
				if (it.second->port_input)
					sets_def.push_back(it.second->name.str());
		}

		if (show_inputs) {
			for (auto &it : module->wires_)
				if (it.second->port_input)
					shows.push_back(it.second->name.str());
		}

		if (show_outputs) {
			for (auto &it : module->wires_)
				if (it.second->port_output)
					shows.push_back(it.second->name.str());
		}

		if (show_regs) {
			pool<Wire*> reg_wires;
			for (auto cell : module->cells()) {
				if (cell->type == "$dff" || cell->type.begins_with("$_DFF_"))
					for (auto bit : cell->getPort("\\Q"))
						if (bit.wire)
							reg_wires.insert(bit.wire);
			}
			for (auto wire : reg_wires)
				shows.push_back(wire->name.str());
		}

		if (show_public) {
			for (auto wire : module->wires())
				if (wire->name[0] == '\\')
					shows.push_back(wire->name.str());
		}

		if (show_all) {
			for (auto wire : module->wires())
				shows.push_back(wire->name.str());
		}

		if (tempinduct)
		{
			if (loopcount > 0 || max_undef)
				log_cmd_error("The options -max, -all, and -max_undef are not supported for temporal induction proofs!\n");

			SatHelper basecase(design, module, enable_undef);
			SatHelper inductstep(design, module, enable_undef);

			basecase.sets = sets;
			basecase.set_assumes = set_assumes;
			basecase.prove = prove;
			basecase.prove_x = prove_x;
			basecase.prove_asserts = prove_asserts;
			basecase.sets_at = sets_at;
			basecase.unsets_at = unsets_at;
			basecase.shows = shows;
			basecase.timeout = timeout;
			basecase.sets_def = sets_def;
			basecase.sets_any_undef = sets_any_undef;
			basecase.sets_all_undef = sets_all_undef;
			basecase.sets_def_at = sets_def_at;
			basecase.sets_any_undef_at = sets_any_undef_at;
			basecase.sets_all_undef_at = sets_all_undef_at;
			basecase.sets_init = sets_init;
			basecase.set_init_def = set_init_def;
			basecase.set_init_undef = set_init_undef;
			basecase.set_init_zero = set_init_zero;
			basecase.satgen.ignore_div_by_zero = ignore_div_by_zero;
			basecase.ignore_unknown_cells = ignore_unknown_cells;

			for (int timestep = 1; timestep <= seq_len; timestep++)
				if (!tempinduct_inductonly)
					basecase.setup(timestep, timestep == 1);

			inductstep.sets = sets;
			inductstep.set_assumes = set_assumes;
			inductstep.prove = prove;
			inductstep.prove_x = prove_x;
			inductstep.prove_asserts = prove_asserts;
			inductstep.shows = shows;
			inductstep.timeout = timeout;
			inductstep.sets_def = sets_def;
			inductstep.sets_any_undef = sets_any_undef;
			inductstep.sets_all_undef = sets_all_undef;
			inductstep.satgen.ignore_div_by_zero = ignore_div_by_zero;
			inductstep.ignore_unknown_cells = ignore_unknown_cells;

			if (!tempinduct_baseonly) {
				inductstep.setup(1);
				inductstep.ez->assume(inductstep.setup_proof(1));
			}

			if (tempinduct_def) {
				std::vector<int> undef_state = inductstep.satgen.importUndefSigSpec(inductstep.satgen.initial_state.export_all(), 1);
				inductstep.ez->assume(inductstep.ez->NOT(inductstep.ez->expression(ezSAT::OpOr, undef_state)));
			}

			for (int inductlen = 1; inductlen <= maxsteps || maxsteps == 0; inductlen++)
			{
				log("\n** Trying induction with length %d **\n", inductlen);

				// phase 1: proving base case

				if (!tempinduct_inductonly)
				{
					basecase.setup(seq_len + inductlen, seq_len + inductlen == 1);
					int property = basecase.setup_proof(seq_len + inductlen);
					basecase.generate_model();

					if (inductlen > 1)
						basecase.force_unique_state(seq_len + 1, seq_len + inductlen);

					if (tempinduct_skip < inductlen)
					{
						log("\n[base case %d] Solving problem with %d variables and %d clauses..\n",
								inductlen, basecase.ez->numCnfVariables(), basecase.ez->numCnfClauses());
						log_flush();

						if (basecase.solve(basecase.ez->NOT(property))) {
							log("SAT temporal induction proof finished - model found for base case: FAIL!\n");
							print_proof_failed();
							basecase.print_model();
							if(!vcd_file_name.empty())
								basecase.dump_model_to_vcd(vcd_file_name);
							if(!json_file_name.empty())
								basecase.dump_model_to_json(json_file_name);
							goto tip_failed;
						}

						if (basecase.gotTimeout)
							goto timeout;

						log("Base case for induction length %d proven.\n", inductlen);
					}
					else
					{
						log("\n[base case %d] Skipping prove for this step (-tempinduct-skip %d).",
								inductlen, tempinduct_skip);
						log("\n[base case %d] Problem size so far: %d variables and %d clauses.\n",
								inductlen, basecase.ez->numCnfVariables(), basecase.ez->numCnfClauses());
					}
					basecase.ez->assume(property);
				}

				// phase 2: proving induction step

				if (!tempinduct_baseonly)
				{
					inductstep.setup(inductlen + 1);
					int property = inductstep.setup_proof(inductlen + 1);
					inductstep.generate_model();

					if (inductlen > 1)
						inductstep.force_unique_state(1, inductlen + 1);

					if (inductlen <= tempinduct_skip || inductlen <= initsteps || inductlen % stepsize != 0)
					{
						if (inductlen < tempinduct_skip)
							log("\n[induction step %d] Skipping prove for this step (-tempinduct-skip %d).",
									inductlen, tempinduct_skip);
						if (inductlen < initsteps)
							log("\n[induction step %d] Skipping prove for this step (-initsteps %d).",
									inductlen, tempinduct_skip);
						if (inductlen % stepsize != 0)
							log("\n[induction step %d] Skipping prove for this step (-stepsize %d).",
									inductlen, stepsize);
						log("\n[induction step %d] Problem size so far: %d variables and %d clauses.\n",
								inductlen, inductstep.ez->numCnfVariables(), inductstep.ez->numCnfClauses());
						inductstep.ez->assume(property);
					}
					else
					{
						if (!cnf_file_name.empty())
						{
							rewrite_filename(cnf_file_name);
							FILE *f = fopen(cnf_file_name.c_str(), "w");
							if (!f)
								log_cmd_error("Can't open output file `%s' for writing: %s\n", cnf_file_name.c_str(), strerror(errno));

							log("Dumping CNF to file `%s'.\n", cnf_file_name.c_str());
							cnf_file_name.clear();

							inductstep.ez->printDIMACS(f, false);
							fclose(f);
						}

						log("\n[induction step %d] Solving problem with %d variables and %d clauses..\n",
								inductlen, inductstep.ez->numCnfVariables(), inductstep.ez->numCnfClauses());
						log_flush();

						if (!inductstep.solve(inductstep.ez->NOT(property))) {
							if (inductstep.gotTimeout)
								goto timeout;
							log("Induction step proven: SUCCESS!\n");
							print_qed();
							goto tip_success;
						}

						log("Induction step failed. Incrementing induction length.\n");
						inductstep.ez->assume(property);
						inductstep.print_model();
					}
				}
			}

			if (tempinduct_baseonly) {
				log("\nReached maximum number of time steps -> proved base case for %d steps: SUCCESS!\n", maxsteps);
				goto tip_success;
			}

			log("\nReached maximum number of time steps -> proof failed.\n");
			if(!vcd_file_name.empty())
				inductstep.dump_model_to_vcd(vcd_file_name);
			if(!json_file_name.empty())
				inductstep.dump_model_to_json(json_file_name);
			print_proof_failed();

		tip_failed:
			if (verify) {
				log("\n");
				log_error("Called with -verify and proof did fail!\n");
			}

			if (0)
		tip_success:
			if (falsify) {
				log("\n");
				log_error("Called with -falsify and proof did succeed!\n");
			}
		}
		else
		{
			if (maxsteps > 0)
				log_cmd_error("The options -maxsteps is only supported for temporal induction proofs!\n");

			SatHelper sathelper(design, module, enable_undef);

			sathelper.sets = sets;
			sathelper.set_assumes = set_assumes;
			sathelper.prove = prove;
			sathelper.prove_x = prove_x;
			sathelper.prove_asserts = prove_asserts;
			sathelper.sets_at = sets_at;
			sathelper.unsets_at = unsets_at;
			sathelper.shows = shows;
			sathelper.timeout = timeout;
			sathelper.sets_def = sets_def;
			sathelper.sets_any_undef = sets_any_undef;
			sathelper.sets_all_undef = sets_all_undef;
			sathelper.sets_def_at = sets_def_at;
			sathelper.sets_any_undef_at = sets_any_undef_at;
			sathelper.sets_all_undef_at = sets_all_undef_at;
			sathelper.sets_init = sets_init;
			sathelper.set_init_def = set_init_def;
			sathelper.set_init_undef = set_init_undef;
			sathelper.set_init_zero = set_init_zero;
			sathelper.satgen.ignore_div_by_zero = ignore_div_by_zero;
			sathelper.ignore_unknown_cells = ignore_unknown_cells;

			if (seq_len == 0) {
				sathelper.setup();
				if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
					sathelper.ez->assume(sathelper.ez->NOT(sathelper.setup_proof()));
			} else {
				std::vector<int> prove_bits;
				for (int timestep = 1; timestep <= seq_len; timestep++) {
					sathelper.setup(timestep, timestep == 1);
					if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
						if (timestep > prove_skip)
							prove_bits.push_back(sathelper.setup_proof(timestep));
				}
				if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
					sathelper.ez->assume(sathelper.ez->NOT(sathelper.ez->expression(ezSAT::OpAnd, prove_bits)));
			}
			sathelper.generate_model();

			if (!cnf_file_name.empty())
			{
				rewrite_filename(cnf_file_name);
				FILE *f = fopen(cnf_file_name.c_str(), "w");
				if (!f)
					log_cmd_error("Can't open output file `%s' for writing: %s\n", cnf_file_name.c_str(), strerror(errno));

				log("Dumping CNF to file `%s'.\n", cnf_file_name.c_str());
				cnf_file_name.clear();

				sathelper.ez->printDIMACS(f, false);
				fclose(f);
			}

			int rerun_counter = 0;

		rerun_solver:
			log("\nSolving problem with %d variables and %d clauses..\n",
					sathelper.ez->numCnfVariables(), sathelper.ez->numCnfClauses());
			log_flush();

			if (sathelper.solve())
			{
				if (max_undef) {
					log("SAT model found. maximizing number of undefs.\n");
					sathelper.maximize_undefs();
				}

				if (!prove.size() && !prove_x.size() && !prove_asserts) {
					log("SAT solving finished - model found:\n");
				} else {
					log("SAT proof finished - model found: FAIL!\n");
					print_proof_failed();
				}

				sathelper.print_model();

				if(!vcd_file_name.empty())
					sathelper.dump_model_to_vcd(vcd_file_name);
				if(!json_file_name.empty())
					sathelper.dump_model_to_json(json_file_name);

				if (loopcount != 0) {
					loopcount--, rerun_counter++;
					sathelper.invalidate_model(max_undef);
					goto rerun_solver;
				}

				if (!prove.size() && !prove_x.size() && !prove_asserts) {
					if (falsify) {
						log("\n");
						log_error("Called with -falsify and found a model!\n");
					}
				} else {
					if (verify) {
						log("\n");
						log_error("Called with -verify and proof did fail!\n");
					}
				}
			}
			else
			{
				if (sathelper.gotTimeout)
					goto timeout;
				if (rerun_counter)
					log("SAT solving finished - no more models found (after %d distinct solutions).\n", rerun_counter);
				else if (!prove.size() && !prove_x.size() && !prove_asserts) {
					log("SAT solving finished - no model found.\n");
					if (verify) {
						log("\n");
						log_error("Called with -verify and found no model!\n");
					}
				} else {
					log("SAT proof finished - no model found: SUCCESS!\n");
					print_qed();
					if (falsify) {
						log("\n");
						log_error("Called with -falsify and proof did succeed!\n");
					}
				}
			}

			if (!prove.size() && !prove_x.size() && !prove_asserts) {
				if (falsify && rerun_counter) {
					log("\n");
					log_error("Called with -falsify and found a model!\n");
				}
			} else {
				if (verify && rerun_counter) {
					log("\n");
					log_error("Called with -verify and proof did fail!\n");
				}
			}
		}

		if (0) {
	timeout:
			log("Interrupted SAT solver: TIMEOUT!\n");
			print_timeout();
			if (fail_on_timeout)
				log_error("Called with -verify and proof did time out!\n");
		}
	}
} SatPass;

PRIVATE_NAMESPACE_END
