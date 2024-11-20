/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  George Rennie <georgrennie@gmail.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Standard visitor helper
template<class... Ts>
struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

struct OptBarriersPass : public Pass {
	OptBarriersPass() : Pass("optbarriers", "insert optimization barriers") {}

	void help() override {
		log("\n");
		log("    optbarriers [options] [selection]\n");
		log("\n");
		log("Insert optimization barriers to drivers of selected public wires.\n");
		log("\n");
		log("\n");
		log("    -nocells\n");
		log("        don't add optimization barriers to the outputs of cells\n");
		log("\n");
		log("    -noprocs\n");
		log("        don't add optimization barriers to the outputs of processes\n");
		log("\n");
		log("    -private\n");
		log("        also add optimization barriers to private wires\n");
		log("\n");
		log("    -remove\n");
		log("        replace selected optimization barriers with connections\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPTBARRIERS pass (insert optimization barriers).\n");

		bool nocells_mode = false;
		bool noprocs_mode = false;
		bool private_mode = false;
		bool remove_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-nocells") {
				nocells_mode = true;
				continue;
			}
			if (arg == "-noprocs") {
				noprocs_mode = true;
				continue;
			}
			if (arg == "-private") {
				private_mode = true;
				continue;
			}
			if (arg == "-remove") {
				remove_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (remove_mode) {
			log("Replacing optimization barriers with connections.\n");
			remove_barriers(design);
			return;
		}

		for (auto* module : design->selected_modules()) {
			// We can't just sigmap and iterate through wires for rewriting as
			// we want to maintain the structure in connections, and sigmap
			// will just return a canonical wire which does not have to be one
			// that is directly driving the wire. Therefore for each type of
			// object that could be driving the wires (cells, processes,
			// connections) we rewrite the sigspecs.

			// Keep track of which wires we have allocated new wires for
			dict<RTLIL::Wire*, RTLIL::Wire*> new_wires;
			// Keep track of bit pairs we need to construct barriers for from
			// Y to A
			dict<RTLIL::SigBit, RTLIL::SigBit> new_barriers;

			// Skip constants, unselected wires and private wires when not in
			// private mode. This works for SigChunk or SigBit input.
			const auto skip = [&](const auto& chunk) {
				if (!chunk.is_wire())
					return true;

				if (!design->selected(module, chunk.wire))
					return true;

				if (!private_mode && !chunk.wire->name.isPublic())
					return true;

				return false;
			};

			const auto rewrite_sigspec = [&](const SigSpec& sig) {
				RTLIL::SigSpec new_output;
				for (const auto& chunk : sig.chunks()) {
					if (skip(chunk)) {
						new_output.append(chunk);
						continue;
					}

					// Add a wire to drive if one does not already exist
					auto* new_wire = new_wires.at(chunk.wire, nullptr);
					if (!new_wire) {
						new_wire = module->addWire(NEW_ID, GetSize(chunk.wire));
						new_wires.emplace(chunk.wire, new_wire);
					}

					RTLIL::SigChunk new_chunk = chunk;
					new_chunk.wire = new_wire;

					// Rewrite output to drive new wire, and schedule adding
					// barrier bits from new wire to original
					new_output.append(new_chunk);
					for (int i = 0; i < GetSize(chunk); i++)
						new_barriers.emplace(chunk[i], new_chunk[i]);
				}

				return new_output;
			};

			// Rewrite cell outputs
			if (!nocells_mode)
			for (auto* cell : module->cells())
				if (cell->type != ID($barrier))
				for (const auto& [name, sig] : cell->connections())
					if (cell->output(name))
						cell->setPort(name, rewrite_sigspec(sig));

			// Rewrite connections in processes
			if (!noprocs_mode) {
				const auto proc_rewriter = overloaded{
					// Don't do anything for input sigspecs
					[&](const SigSpec&) {},
					// Rewrite connections to drive barrier if needed
					[&](SigSpec& lhs, const SigSpec&) {
						lhs = rewrite_sigspec(lhs);
					}
				};

				for (auto& proc : module->processes)
					proc.second->rewrite_sigspecs2(proc_rewriter);
			}

			// Add all the scheduled barriers. To minimize the number of cells,
			// first construct a sigspec of all bits, then sort and unify before
			// creating barriers
			SigSpec barrier_y;
			for (const auto&[y_bit, _] : new_barriers)
				barrier_y.append(y_bit);
			barrier_y.sort_and_unify();

			for (const auto& sig_y : barrier_y.chunks()) {
				log_assert(sig_y.is_wire());
				SigSpec sig_a;
				for (int i = 0; i < GetSize(sig_y); i++)
					sig_a.append(new_barriers[sig_y[i]]);
				module->addBarrier(NEW_ID, sig_a, sig_y);
			}

			// Rewrite connections
			std::vector<RTLIL::SigSig> new_connections;
			for (const auto& conn : module->connections()) {
				RTLIL::SigSig skip_conn, barrier_conn;

				for (int i = 0; i < GetSize(conn.first); i++) {
					auto& sigsig = skip(conn.first[i]) ? skip_conn : barrier_conn;
					sigsig.first.append(conn.first[i]);
					sigsig.second.append(conn.second[i]);
				}

				if (!skip_conn.first.empty())
					new_connections.emplace_back(std::move(skip_conn));

				if (!barrier_conn.first.empty())
					module->addBarrier(NEW_ID, barrier_conn.second, barrier_conn.first);
			}
			module->new_connections(new_connections);
		}
	}

	void remove_barriers(RTLIL::Design* design) {
		for (auto* module : design->selected_modules()) {
			std::vector<RTLIL::Cell*> barriers;

			for (auto* cell : module->selected_cells())
				if (cell->type == ID($barrier))
					barriers.emplace_back(cell);

			for (auto* cell : barriers) {
				const auto lhs = cell->getPort(ID::Y), rhs = cell->getPort(ID::A);
				module->connect(lhs, rhs);
				module->remove(cell);
			}
		}
	}

} OptBarriersPass;

PRIVATE_NAMESPACE_END
