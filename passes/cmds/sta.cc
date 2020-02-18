/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2019  Eddie Hung <eddie@fpgeh.com>
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
#include "kernel/timinginfo.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct StaWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;

	dict<SigBit, std::vector<pair<SigBit, int>>> fanouts;
	dict<SigBit, std::pair<SigBit,int>> backtrack;
	std::deque<SigBit> queue;
	dict<SigBit, int> endpoints;

	int maxarrival;
	SigBit maxbit;

	StaWorker(RTLIL::Module *module) : design(module->design), module(module), sigmap(module), maxarrival(0)
	{
		TimingInfo timing;

		for (auto cell : module->cells())
		{
			Module *inst_module = design->module(cell->type);
			log_assert(inst_module);

			if (!inst_module->get_blackbox_attribute()) {
				log_warning("Module '%s' is not a black- nor white-box!\n", log_id(cell->type));
				continue;
			}

			IdString derived_type = inst_module->derive(design, cell->parameters);
			inst_module = design->module(derived_type);
			log_assert(inst_module);

			if (!timing.count(derived_type)) {
				auto &t = timing.setup_module(inst_module);
				if (t.comb.empty() && t.arrival.empty() && t.required.empty())
					log_warning("Module '%s' has no timing arcs!\n", log_id(cell->type));
			}

			auto &t = timing.at(derived_type);
			if (t.comb.empty() && t.arrival.empty() && t.required.empty())
				continue;

			pool<std::pair<SigBit,TimingInfo::NameBit>> src_bits, dst_bits;

			for (auto &conn : cell->connections()) {
				auto rhs = sigmap(conn.second);
				for (auto i = 0; i < GetSize(rhs); i++) {
					const auto &bit = rhs[i];
					if (!bit.wire)
						continue;
					TimingInfo::NameBit namebit(conn.first,i);
					if (cell->input(conn.first)) {
						src_bits.insert(std::make_pair(bit,namebit));

						auto it = t.required.find(namebit);
						if (it == t.required.end())
							continue;
						endpoints[bit] = it->second;
					}
					if (cell->output(conn.first)) {
						dst_bits.insert(std::make_pair(bit,namebit));

						auto it = t.arrival.find(namebit);
						if (it == t.arrival.end())
							continue;
						auto arrivals = bit.wire->get_intvec_attribute(ID(sta_arrival));
						if (arrivals.empty())
							arrivals = std::vector<int>(GetSize(bit.wire), -1);
						else
							log_assert(GetSize(arrivals) == GetSize(bit.wire));
						arrivals[bit.offset] = it->second;
						bit.wire->set_intvec_attribute(ID(sta_arrival), arrivals);
						queue.emplace_back(bit);
					}
				}
			}

			for (const auto &s : src_bits)
				for (const auto &d : dst_bits) {
					auto it = t.comb.find(TimingInfo::BitBit(s.second,d.second));
					if (it == t.comb.end())
						continue;
					fanouts[s.first].emplace_back(d.first,it->second);
				}
		}

		for (auto port_name : module->ports) {
			auto wire = module->wire(port_name);
			if (!wire->port_input)
				continue;
			for (const auto &b : sigmap(wire))
				queue.emplace_back(b);
			// All primary inputs to arrive at time zero
			wire->set_intvec_attribute(ID(sta_arrival), std::vector<int>(GetSize(wire), 0));
		}
	}

	void run()
	{
		while (!queue.empty()) {
			auto b = queue.front();
			queue.pop_front();
			auto it = fanouts.find(b);
			if (it == fanouts.end())
				continue;
			const auto& src_arrivals = b.wire->get_intvec_attribute(ID(sta_arrival));
			log_assert(GetSize(src_arrivals) == GetSize(b.wire));
			auto src_arrival = src_arrivals[b.offset];
			for (const auto &d : it->second) {
				auto dst_arrivals = d.first.wire->get_intvec_attribute(ID(sta_arrival));
				if (dst_arrivals.empty())
					dst_arrivals = std::vector<int>(GetSize(d.first.wire), -1);
				else
					log_assert(GetSize(dst_arrivals) == GetSize(d.first.wire));
				auto &dst_arrival = dst_arrivals[d.first.offset];
				auto new_arrival = src_arrival + d.second + endpoints.at(d.first, 0);
				if (dst_arrival < new_arrival) {
					dst_arrival = std::max(dst_arrival, new_arrival);
					if (dst_arrival > maxarrival) {
						maxarrival = dst_arrival;
						maxbit = d.first;
					}
					d.first.wire->set_intvec_attribute(ID(sta_arrival), dst_arrivals);
					queue.emplace_back(d.first);
					backtrack[d.first] = std::make_pair(b, src_arrival);
				}
			}
		}

		log("Latest arrival time in '%s' is %d:\n", log_id(module), maxarrival);
		auto b = maxbit;
		auto arrival = maxarrival;
		auto it = backtrack.find(b);
		while (it != backtrack.end()) {
			log("    %6d %s\n", arrival, log_signal(b));
			std::tie(b,arrival) = it->second;
			it = backtrack.find(b);
		}
		log("    %6d %s\n", arrival, log_signal(b));
	}
};

struct StaPass : public Pass {
	StaPass() : Pass("sta", "perform static timing analysis") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sta [options] [selection]\n");
		log("\n");
		log("This command performs static timing analysis on the design. (Only considers\n");
		log("paths within a single module, so the design must be flattened.)\n");
		log("\n");
		log("    -TODO\n");
		log("        TODO\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing STA pass (static timing analysis).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-TODO") {
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);

		for (Module *module : design->selected_modules())
		{
			if (module->has_processes_warn())
				continue;

			StaWorker worker(module);
			worker.run();
		}
	}
} StaPass;

PRIVATE_NAMESPACE_END
