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
#include "kernel/ffinit.h"
#include "kernel/topo_scc.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Standard visitor helper
template<class... Ts>
struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

// This computes a graph of assignment dependencies in a process, which is used
// to preserve SCCs in the process which are useful for DFF inference
struct ProcessDependencyWorker {
	ProcessDependencyWorker(const RTLIL::Process& proc) {
		add_process(proc);
		find_sccs();
	}

	ProcessDependencyWorker(const std::vector<RTLIL::SigSig>& connections) {
		for (const auto& sigsig : connections)
			add_sigsig(sigsig);
		find_sccs();
	}

	void add_process(const RTLIL::Process& proc) {
		add_caserule(proc.root_case);

		for (const auto* sync : proc.syncs)
			add_syncrule(*sync);
	}

	void add_syncrule(const RTLIL::SyncRule& sync) {
		for (const auto& sigsig : sync.actions)
			add_sigsig(sigsig);
	}

	void add_caserule(const RTLIL::CaseRule& caserule) {
		for (const auto& sigsig : caserule.actions)
			add_sigsig(sigsig);

		for (const auto* rule : caserule.switches)
			add_switchrule(*rule);
	}

	void add_switchrule(const RTLIL::SwitchRule& switchrule) {
		for (const auto* rule : switchrule.cases)
			add_caserule(*rule);
	}

	void add_sigsig(const RTLIL::SigSig& sigsig) {
		for (int i = 0; i < GetSize(sigsig.first); i++) {
			const auto lhs = sigsig.first[i], rhs = sigsig.second[i];
			// Every driven bit is a node, also one only assigned constants
			auto& rhs_bits = dependencies[lhs];
			if (rhs.is_wire())
				rhs_bits.emplace(rhs);
		}
	}

	// Returns the set of nodes that are on a cycle through this bit - its SCC,
	// or nothing when the bit is on no cycle
	const pool<SigBit>& scc_nodes(const SigBit bit) const {
		const auto it = scc_of.find(bit);
		return it == scc_of.end() ? no_nodes : sccs[it->second];
	}

	dict<SigBit, pool<SigBit>> dependencies;
private:
	// A lone bit is on a cycle only with a self-loop
	void find_sccs() {
		idict<SigBit> ids;
		IntGraph graph;
		for (const auto& [lhs, rhs_bits] : dependencies)
			for (const auto& rhs : rhs_bits)
				if (dependencies.count(rhs))
					graph.add_edge(ids(lhs), ids(rhs));

		TopoSortedSccs(graph, [&](int* begin, int* end) {
			pool<SigBit> scc;
			for (int* it = begin; it != end; it++)
				scc.insert(ids[*it]);
			const SigBit bit = *scc.begin();
			if (GetSize(scc) == 1 && !dependencies.at(bit).count(bit))
				return;
			for (const auto& member : scc)
				scc_of[member] = GetSize(sccs);
			sccs.push_back(std::move(scc));
		}).process_all();
	}

	dict<SigBit, int> scc_of;
	std::vector<pool<SigBit>> sccs;
	pool<SigBit> no_nodes;
};

struct ResetPathWorker {
	ResetPathWorker(RTLIL::Module* module) {
		std::vector<std::pair<const RTLIL::Process*, pool<SigBit>>> edge_procs;
		for (const auto& [_, proc] : module->processes) {
			pool<SigBit> edges;
			for (const auto* sync : proc->syncs)
				if (sync->type == RTLIL::STp || sync->type == RTLIL::STn || sync->type == RTLIL::STe)
					for (const auto& bit : sync->signal)
						edges.insert(bit);
			if (!edges.empty())
				edge_procs.emplace_back(proc, std::move(edges));
		}

		// Without edge triggered processes there are no reset paths
		if (edge_procs.empty())
			return;

		for (auto* cell : module->cells())
			if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($logic_not), ID($not), ID($eq), ID($eqx), ID($ne), ID($nex)))
				if (GetSize(cell->getPort(ID::Y)) == 1)
					drivers[cell->getPort(ID::Y)[0]] = cell;

		for (const auto& [proc, edges] : edge_procs)
			visit(proc->root_case, edges);
	}

	void visit(const RTLIL::CaseRule& caserule, const pool<SigBit>& edges) {
		if (GetSize(caserule.switches) != 1)
			return;
		const auto* sw = caserule.switches[0];
		std::vector<SigBit> trace;
		if (reaches_edge(sw->signal, edges, trace))
			path.insert(trace.begin(), trace.end());
		for (const auto* rule : sw->cases)
			visit(*rule, edges);
	}

	bool reaches_edge(RTLIL::SigSpec signal, const pool<SigBit>& edges, std::vector<SigBit>& trace) {
		while (GetSize(signal) == 1) {
			const SigBit bit = signal[0];
			if (edges.count(bit))
				return true;
			const auto it = drivers.find(bit);
			if (it == drivers.end() || GetSize(trace) > GetSize(drivers))
				return false;
			trace.push_back(bit);
			signal = next_signal(it->second);
		}
		return false;
	}

	static RTLIL::SigSpec next_signal(RTLIL::Cell* cell) {
		if (!cell->type.in(ID($eq), ID($eqx), ID($ne), ID($nex)))
			return cell->getPort(ID::A);
		if (cell->getPort(ID::A).is_fully_const())
			return cell->getPort(ID::B);
		if (cell->getPort(ID::B).is_fully_const())
			return cell->getPort(ID::A);
		return RTLIL::SigSpec();
	}

	dict<SigBit, RTLIL::Cell*> drivers;
	pool<SigBit> path;
};

struct OptBarriersPass : public Pass {
	OptBarriersPass() : Pass("optbarriers", "(experimental) insert optimization barriers")
	{
		experimental();
	}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
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
		log("    -noconns\n");
		log("        don't add optimization barriers to the left hand sides of connections\n");
		log("\n");
		log("    -private\n");
		log("        also add optimization barriers to private wires driven by cells and\n");
		log("        connections, excluding private wires driven by processes\n");
		log("\n");
		log("    -remove\n");
		log("        replace selected optimization barriers with connections\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPTBARRIERS pass (insert optimization barriers).\n");

		bool nocells_mode = false;
		bool noprocs_mode = false;
		bool noconns_mode = false;
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
			if (arg == "-noconns") {
				noconns_mode = true;
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

			// Nets that already drive a barrier input which must not get a second barrier.
			// Only private wires check this, so only needed in private mode
			SigMap sigmap;
			pool<SigBit> barrier_inputs;
			if (private_mode) {
				sigmap.set(module);
				for (auto* cell : module->cells())
					if (cell->type == ID($barrier))
						for (const auto& bit : sigmap(cell->getPort(ID::A)))
							barrier_inputs.insert(bit);
			}
			const ResetPathWorker reset_path(module);

			// Skip constants, unselected wires, private wires when not in
			// private mode, input and inout ports, and private pre-barrier bits.
			const auto skip = [&](const SigBit& bit) {
				if (!bit.is_wire())
					return true;

				if (!design->selected(module, bit.wire))
					return true;

				if (bit.wire->port_input)
					return true;

				if (reset_path.path.count(bit))
					return true;

				if (!bit.wire->name.isPublic() && (!private_mode || barrier_inputs.count(sigmap(bit))))
					return true;

				return false;
			};

			const auto rewrite_sigspec = [&](const SigSpec& sig) {
				RTLIL::SigSpec new_output;
				for (const auto& bit : sig) {
					if (skip(bit)) {
						new_output.append(bit);
						continue;
					}

					// Add a wire to drive if one does not already exist
					auto* new_wire = new_wires.at(bit.wire, nullptr);
					if (!new_wire) {
						new_wire = module->addWire(NEW_ID_SUFFIX(bit.wire->name.str()), GetSize(bit.wire));
						new_wires.emplace(bit.wire, new_wire);
					}

					// Rewrite output to drive new wire, and schedule adding
					// a barrier bit from new wire to original
					const SigBit new_bit(new_wire, bit.offset);
					new_output.append(new_bit);
					new_barriers.emplace(bit, new_bit);
				}

				return new_output;
			};

			// Rewrite processes. It is not as simple as changing all LHS
			// expressions to drive barriers if required, as this prevents
			// proc passes from optimizing self feedback which is important to
			// prevent false comb paths when generating FFs. We only care about
			// the assignments/connections within processes, and want to maintain
			// the property that if a bit that is to be rewritten to use a
			// barrier can be assigned transitively to itself, the value that is
			// assigned should be the value before the barrier.
			//
			// To do this we first enumerate the assignment dependency graph
			// for the process - marking which bits drive any other bit. We
			// then look for strongly connected components containing barrier
			// bits. These correspond to potential paths where the bit can be
			// driven by itself and so should see the pre-barrier value. For
			// each of the bits on this path we want to construct a parallel
			// version that appears in all the same process assignments but is
			// driven originally by the pre-barrier value.
			//
			// For example, consider the following set of assignments appear
			// somewhere in the process and we want to add a barrier to b:
			// a <- b
			// b <- a
			// There is a path from b to itself through a, so we add wire b\b to
			// represent the pre-barrier version of b and a\b to represent
			// the version of a that sees a pre-barrier version of b. We then
			// correspondingly add these paths to the assignments and a barrier:
			// {a\b, a} <- {b\b, b}
			// b\b <- a\b
			// b\b -$barrier> b
			//
			// This has retained that b\b is transitively driven by itself, but
			// a is still driven by b, the post-barrier version of b
			if (!noprocs_mode)
			for (const auto& proc : module->processes) {
				// A map from each bit driven by the original process to the
				// set of variants required for it. If a bit doesn't appear in
				// variants it is only needed in the original form it appears
				// in the process.
				//
				// To get bit a\b from the above example you would index
				// variants[a][b]
				dict<SigBit, dict<SigBit, SigBit>> variants;

				{
					// We want to minimize the number of wires we have to create
					// for each bit in variants, so for variants[a][b] we create
					// a unique wire with size GetSize(a.wire) for each tuple
					// of a.wire, b.wire, a.offset - b.offset rather than for
					// every pair (a, b).
					using IdxTuple = std::tuple<Wire*, Wire*, int>;
					dict<IdxTuple, Wire*> variant_wires;

					// Collect all assignment dependencies in the process
					ProcessDependencyWorker dep_worker(*proc.second);

					// Enumerate driven bits that need barriers added
					for (const auto& [variant_bit, _] : dep_worker.dependencies) {
						// Private bits driven by processes are frontend temporaries
						if (skip(variant_bit) || !variant_bit.wire->name.isPublic())
							continue;

						// Collect the bits that are in an SCC with this bit and
						// thus need to have variants constructed that see the
						// pre-barrier value
						for (const auto& lhs_bit : dep_worker.scc_nodes(variant_bit)) {
							// Don't add a new wire for the variant_bit itself as this
							// should be driven by a wire generated by rewrite_sigspec below
							if (lhs_bit == variant_bit)
								continue;

							const int offset = lhs_bit.offset - variant_bit.offset;
							const IdxTuple idx{lhs_bit.wire, variant_bit.wire, offset};
							auto it = variant_wires.find(idx);

							// Create a new wire to represent this offset combination
							// if needed
							if (it == variant_wires.end()) {
								const auto name = NEW_ID_SUFFIX(lhs_bit.wire->name.str());
								auto* new_wire = module->addWire(name, GetSize(lhs_bit.wire));
								it = variant_wires.emplace(idx, new_wire).first;
							}

							variants[lhs_bit].emplace(variant_bit, SigBit(it->second, lhs_bit.offset));
						}

						// Even if a bit doesn't appear in any SCCs we want to rewrite it if it
						// isn't skipped
						variants[variant_bit].emplace(variant_bit, rewrite_sigspec(variant_bit));
					}
				}

				const auto variant = [&](const SigBit a, const SigBit b) {
					const auto it1 = variants.find(a);
					// There are no variants of a required, so a definitely isn't
					// transitively driven by b
					if (it1 == variants.end())
						return a;

					const auto it2 = it1->second.find(b);
					// a isn't be transitively driven by b
					if (it2 == it1->second.end())
						return a;

					// a can be transitively driven by b so return the variant
					// of a that sees pre-barrier b
					return it2->second;
				};

				const auto proc_rewriter = overloaded{
					// Don't do anything for input sigspecs, these are not connections
					[&](const SigSpec&) {},
					// Rewrite connections to drive barrier and see pre-barrier
					// values if needed
					[&](SigSpec& lhs, SigSpec& rhs) {
						for (int i = 0; i < GetSize(lhs); i++) {
							const auto lhs_bit = lhs[i], rhs_bit = rhs[i];

							for (const auto& [variant_bit, variant_lhs_bit] : variants[lhs_bit]) {
								// For the existing connections, update the lhs to be pre-barrier
								// variant_lhs_bit and rhs to be the variant of itself that sees
								// the pre-barrier version of variant_bit
								if (variant_bit == lhs_bit) {
									lhs[i] = variant_lhs_bit;
									rhs[i] = variant(rhs_bit, variant_bit);
									continue;
								}

								// For new variants of lhs_bit that we need to exist, set the
								// rhs bit to the variant of rhs_bit that sees the pre_barrier
								// version of variant_bit
								lhs.append(variant_lhs_bit);
								rhs.append(variant(rhs_bit, variant_bit));
							}
						}
					}
				};

				proc.second->rewrite_sigspecs2(proc_rewriter);
			}

			// Rewrite cell outputs
			if (!nocells_mode)
			for (auto* cell : module->cells())
				if (cell->type != ID($barrier))
				for (const auto& [name, sig] : cell->connections())
					if (cell->output(name) && !cell->input(name))
						cell->setPort(name, rewrite_sigspec(sig));

			// Add all the scheduled barriers. To minimize the number of cells,
			// first construct a sigspec of all bits, then sort and unify before
			// creating barriers
			SigSpec barrier_y;
			for (const auto&[y_bit, _] : new_barriers)
				barrier_y.append(y_bit);
			barrier_y.sort_and_unify();

			bool added_barriers = !barrier_y.empty();
			for (const auto& sig_y : barrier_y.chunks()) {
				log_assert(sig_y.is_wire());
				SigSpec sig_a;
				for (int i = 0; i < GetSize(sig_y); i++)
					sig_a.append(new_barriers[sig_y[i]]);
				module->addBarrier(NEW_ID, sig_a, sig_y);
			}

			// Rewrite connections
			if (!noconns_mode) {
				// A connection on a cycle of connections would become a barrier loop
				const ProcessDependencyWorker conn_deps(module->connections());
				std::vector<RTLIL::SigSig> new_connections;
				for (const auto& conn : module->connections()) {
					RTLIL::SigSig skip_conn, barrier_conn;

					for (int i = 0; i < GetSize(conn.first); i++) {
						bool keep_conn = skip(conn.first[i]) || !conn_deps.scc_nodes(conn.first[i]).empty();
						auto& sigsig = keep_conn ? skip_conn : barrier_conn;
						sigsig.first.append(conn.first[i]);
						sigsig.second.append(conn.second[i]);
					}

					if (!skip_conn.first.empty())
						new_connections.emplace_back(std::move(skip_conn));

					if (!barrier_conn.first.empty()) {
						module->addBarrier(NEW_ID, barrier_conn.second, barrier_conn.first);
						added_barriers = true;
					}
				}
				module->new_connections(new_connections);
			}

			// Init values belong to the driver side of the barriers
			if (added_barriers) {
				SigMap init_sigmap(module);
				FfInitVals initvals(&init_sigmap, module);
				initvals.move_barrier_inits(module);
			}
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
