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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Describes found feedback path.
struct FeedbackPath {
	// Which write port it is.
	int wrport_idx;
	// Which data bit of that write port it is.
	int data_bit_idx;
	// Values of all mux select signals that need to be set to select this path.
	dict<RTLIL::SigBit, bool> condition;
	// The exact feedback bit used (used to match read port).
	SigBit feedback_bit;

	FeedbackPath(int wrport_idx, int data_bit_idx, dict<RTLIL::SigBit, bool> condition, SigBit feedback_bit) : wrport_idx(wrport_idx), data_bit_idx(data_bit_idx), condition(condition), feedback_bit(feedback_bit) {}
};

struct OptMemFeedbackWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap, sigmap_xmux;
	FfInitVals initvals;

	dict<RTLIL::SigBit, std::pair<RTLIL::Cell*, int>> sig_to_mux;
	dict<RTLIL::SigBit, int> sig_users_count;
	dict<pair<pool<dict<SigBit, bool>>, SigBit>, SigBit> conditions_logic_cache;


	// -----------------------------------------------------------------
	// Converting feedbacks to async read ports to proper enable signals
	// -----------------------------------------------------------------

	void find_data_feedback(const pool<RTLIL::SigBit> &async_rd_bits, RTLIL::SigBit sig,
			const dict<RTLIL::SigBit, bool> &state,
			int wrport_idx, int data_bit_idx,
			std::vector<FeedbackPath> &paths)
	{
		if (async_rd_bits.count(sig)) {
			paths.push_back(FeedbackPath(wrport_idx, data_bit_idx, state, sig));
			return;
		}

		if (sig_users_count[sig] != 1) {
			// Only descend into muxes if we're the only user.
			return;
		}

		if (sig_to_mux.count(sig) == 0)
			return;

		RTLIL::Cell *cell = sig_to_mux.at(sig).first;
		int bit_idx = sig_to_mux.at(sig).second;

		std::vector<RTLIL::SigBit> sig_a = sigmap(cell->getPort(ID::A));
		std::vector<RTLIL::SigBit> sig_b = sigmap(cell->getPort(ID::B));
		std::vector<RTLIL::SigBit> sig_s = sigmap(cell->getPort(ID::S));
		std::vector<RTLIL::SigBit> sig_y = sigmap(cell->getPort(ID::Y));
		log_assert(sig_y.at(bit_idx) == sig);

		for (int i = 0; i < GetSize(sig_s); i++)
			if (state.count(sig_s[i]) && state.at(sig_s[i]) == true) {
				find_data_feedback(async_rd_bits, sig_b.at(bit_idx + i*sig_y.size()), state, wrport_idx, data_bit_idx, paths);
				return;
			}


		for (int i = 0; i < GetSize(sig_s); i++)
		{
			if (state.count(sig_s[i]) && state.at(sig_s[i]) == false)
				continue;

			dict<RTLIL::SigBit, bool> new_state = state;
			new_state[sig_s[i]] = true;

			find_data_feedback(async_rd_bits, sig_b.at(bit_idx + i*sig_y.size()), new_state, wrport_idx, data_bit_idx, paths);
		}

		dict<RTLIL::SigBit, bool> new_state = state;
		for (auto bit : sig_s)
			new_state[bit] = false;

		find_data_feedback(async_rd_bits, sig_a.at(bit_idx), new_state, wrport_idx, data_bit_idx, paths);
	}

	RTLIL::SigBit conditions_to_logic(pool<dict<RTLIL::SigBit, bool>> &conditions, SigBit olden)
	{
		auto key = make_pair(conditions, olden);

		if (conditions_logic_cache.count(key))
			return conditions_logic_cache.at(key);

		RTLIL::SigSpec terms;
		for (auto &cond : conditions) {
			RTLIL::SigSpec sig1, sig2;
			for (auto &it : cond) {
				sig1.append(it.first);
				sig2.append(it.second ? RTLIL::State::S1 : RTLIL::State::S0);
			}
			terms.append(module->Ne(NEW_ID, sig1, sig2));
		}

		if (olden != State::S1)
			terms.append(olden);

		if (GetSize(terms) == 0)
			terms = State::S1;

		if (GetSize(terms) > 1)
			terms = module->ReduceAnd(NEW_ID, terms);

		return conditions_logic_cache[key] = terms;
	}

	void translate_rd_feedback_to_en(Mem &mem)
	{
		// Look for async read ports that may be suitable for feedback paths.
		dict<RTLIL::SigSpec, std::vector<pool<RTLIL::SigBit>>> async_rd_bits;

		for (auto &port : mem.rd_ports)
		{
			if (port.clk_enable)
				continue;

			for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
				SigSpec addr = sigmap_xmux(port.sub_addr(sub));
				async_rd_bits[addr].resize(mem.width);
				for (int i = 0; i < mem.width; i++)
					async_rd_bits[addr][i].insert(sigmap(port.data[i + sub * mem.width]));
			}
		}

		if (async_rd_bits.empty())
			return;

		// Look for actual feedback paths.
		std::vector<FeedbackPath> paths;

		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			auto &port = mem.wr_ports[i];

			log("  Analyzing %s.%s write port %d.\n", log_id(module), log_id(mem.memid), i);

			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				SigSpec addr = sigmap_xmux(port.sub_addr(sub));

				if (!async_rd_bits.count(addr))
					continue;

				for (int j = 0; j < mem.width; j++)
				{
					int bit_idx = sub * mem.width + j;

					if (port.en[bit_idx] == State::S0)
						continue;

					dict<RTLIL::SigBit, bool> state;

					find_data_feedback(async_rd_bits.at(addr).at(j), sigmap(port.data[bit_idx]), state, i, bit_idx, paths);
				}
			}
		}

		if (paths.empty())
			return;

		// Now determine which read ports are actually used only for
		// feedback paths, and can be removed.

		dict<SigBit, int> feedback_users_count;
		for (auto &path : paths)
			feedback_users_count[path.feedback_bit]++;

		pool<SigBit> feedback_ok;
		for (auto &port : mem.rd_ports)
		{
			if (port.clk_enable)
				continue;

			bool ok = true;
			for (auto bit : sigmap(port.data))
				if (sig_users_count[bit] != feedback_users_count[bit])
					ok = false;

			if (ok)
			{
				// This port is going bye-bye.
				for (auto bit : sigmap(port.data))
					feedback_ok.insert(bit);

				port.removed = true;
			}
		}

		if (feedback_ok.empty())
			return;

		// Prepare a feedback condition list grouped by port bits.

		dict<std::pair<int, int>, pool<dict<SigBit, bool>>> portbit_conds;
		for (auto &path : paths)
			if (feedback_ok.count(path.feedback_bit))
				portbit_conds[std::make_pair(path.wrport_idx, path.data_bit_idx)].insert(path.condition);

		if (portbit_conds.empty())
			return;

		// Okay, let's do it.

		log("Populating enable bits on write ports of memory %s.%s with async read feedback:\n", log_id(module), log_id(mem.memid));

		// If a write port has a feedback path that we're about to bypass,
		// but also has priority over some other write port, the feedback
		// path is not necessarily a NOP — it may overwrite the other port.
		// Emulate this effect by converting the priority to soft logic
		// (this will affect the other port's enable signal).
		for (auto &it : portbit_conds)
		{
			int wrport_idx = it.first.first;
			auto &port = mem.wr_ports[wrport_idx];

			for (int i = 0; i < wrport_idx; i++)
				if (port.priority_mask[i])
					mem.emulate_priority(i, wrport_idx, &initvals);
		}

		for (auto &it : portbit_conds)
		{
			int wrport_idx = it.first.first;
			int bit = it.first.second;
			auto &port = mem.wr_ports[wrport_idx];

			port.en[bit] = conditions_to_logic(it.second, port.en[bit]);
			log("    Port %d bit %d: added enable logic for %d different cases.\n", wrport_idx, bit, GetSize(it.second));
		}

		mem.emit();

		for (auto bit : feedback_ok)
			module->connect(bit, State::Sx);

		design->scratchpad_set_bool("opt.did_something", true);
	}

	// -------------
	// Setup and run
	// -------------

	OptMemFeedbackWorker(RTLIL::Design *design) : design(design) {}

	void operator()(RTLIL::Module* module)
	{
		std::vector<Mem> memories = Mem::get_selected_memories(module);

		this->module = module;
		sigmap.set(module);
		initvals.set(&sigmap, module);
		sig_to_mux.clear();
		conditions_logic_cache.clear();

		sigmap_xmux = sigmap;

		for (auto wire : module->wires()) {
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					sig_users_count[bit]++;
		}

		for (auto cell : module->cells())
		{
			if (cell->type == ID($mux))
			{
				RTLIL::SigSpec sig_a = sigmap_xmux(cell->getPort(ID::A));
				RTLIL::SigSpec sig_b = sigmap_xmux(cell->getPort(ID::B));

				if (sig_a.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_b);
				else if (sig_b.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_a);
			}

			if (cell->type.in(ID($mux), ID($pmux)))
			{
				std::vector<RTLIL::SigBit> sig_y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < int(sig_y.size()); i++)
					sig_to_mux[sig_y[i]] = std::pair<RTLIL::Cell*, int>(cell, i);
			}

			for (auto &conn : cell->connections())
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sig_users_count[bit]++;
		}

		for (auto &mem : memories)
			translate_rd_feedback_to_en(mem);
	}
};

struct OptMemFeedbackPass : public Pass {
	OptMemFeedbackPass() : Pass("opt_mem_feedback", "convert memory read-to-write port feedback paths to write enables") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem_feedback [selection]\n");
		log("\n");
		log("This pass detects cases where an asynchronous read port is only connected via\n");
		log("a mux tree to a write port with the same address.  When such a connection is\n");
		log("found, it is replaced with a new condition on an enable signal, allowing\n");
		log("for removal of the read port.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_MEM_FEEDBACK pass (finding memory read-to-write feedback paths).\n");
		extra_args(args, 1, design);
		OptMemFeedbackWorker worker(design);

		for (auto module : design->selected_modules())
			worker(module);
	}
} OptMemFeedbackPass;

PRIVATE_NAMESPACE_END

