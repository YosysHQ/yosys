/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2019  Eddie Hung        <eddie@fpgeh.com>
 *                2024  Akash Levy        <akash@silimate.com>
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
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


struct OptBalanceTreeWorker {
	// Module and signal map
	Module *module;
	SigMap sigmap;

	// Counts of each cell type that are getting balanced
	dict<IdString, int> cell_count;
	int sliced_add_count = 0;

	struct SlicedAddContext {
		dict<SigBit, Cell*> bit_to_driver;
		dict<SigBit, int> bit_to_driver_index;
		dict<SigBit, pool<Cell*>> bit_to_sink;
		pool<SigBit> output_port_sigs;
	};

	// Per cell type netlist indexes, rebuilt for each balanced cell type
	dict<SigSpec, Cell*> sig_to_driver;
	pool<SigSpec> input_port_sigs;
	pool<Cell*> consumed_cells;

	// Width the sliced-add cluster currently being extracted truncates to
	int sliced_head_width = 0;

	// Check if cell is of the right type and has matching input/output widths
	// Only allow cells with "natural" output widths (no truncation) to prevent
	// equivalence issues when rebalancing (see YosysHQ/yosys#5605)
	bool is_right_type(Cell* cell, IdString cell_type) {
		if (cell->type != cell_type)
			return false;

		int y_width = cell->getParam(ID::Y_WIDTH).as_int();
		int a_width = cell->getParam(ID::A_WIDTH).as_int();
		int b_width = cell->getParam(ID::B_WIDTH).as_int();

		// Calculate the "natural" output width for this operation
		int natural_width;
		if (cell_type == ID($add)) {
			// Addition produces max(A_WIDTH, B_WIDTH) + 1 (for carry bit)
			natural_width = std::max(a_width, b_width) + 1;
			// SILIMATE: Ignore carry bit for now for more aggressive balancing
			natural_width--;
		} else if (cell_type == ID($mul)) {
			// Multiplication produces A_WIDTH + B_WIDTH
			natural_width = a_width + b_width;
		} else {
			// Logic operations ($and/$or/$xor) produce max(A_WIDTH, B_WIDTH)
			natural_width = std::max(a_width, b_width);
		}

		// Only allow cells where Y_WIDTH >= natural width (no truncation)
		// This prevents rebalancing chains where truncation semantics matter
		return y_width >= natural_width;
	}

	bool is_unsigned_add(Cell *cell)
	{
		return cell && is_right_type(cell, ID($add)) &&
				!cell->getParam(ID::A_SIGNED).as_bool() &&
				!cell->getParam(ID::B_SIGNED).as_bool();
	}

	// SILIMATE: is_right_type() admits an $add that discards its own carry out, but a
	// tree rebuilt from that cell's operands computes the carry back. The restored bit
	// only stays invisible where something downstream discards it again, so every
	// carry-dropping link needs the callers below to prove that.
	bool drops_carry(Cell *cell)
	{
		if (!cell || cell->type != ID($add))
			return false;
		int a_width = cell->getParam(ID::A_WIDTH).as_int();
		int b_width = cell->getParam(ID::B_WIDTH).as_int();
		return cell->getParam(ID::Y_WIDTH).as_int() < std::max(a_width, b_width) + 1;
	}

	// SILIMATE: merging drv into sink is only sound when sink truncates at least as
	// hard as drv, since mod-2**n addition is associative but mod-2**n then mod-2**m
	// with m > n is not
	bool carry_link_unsafe(Cell *drv, Cell *sink)
	{
		return drops_carry(drv) &&
				drv->getParam(ID::Y_WIDTH).as_int() < sink->getParam(ID::Y_WIDTH).as_int();
	}

	bool is_nonzero(const SigSpec &sig)
	{
		for (auto bit : sig)
			if (bit != State::S0)
				return true;
		return false;
	}

	SigSpec shift_summand(const SigSpec &sig, int offset)
	{
		SigSpec shifted(State::S0, offset);
		shifted.append(sig);
		return shifted;
	}

	// Get the driver of a cell input port if it continues the chain, else nullptr
	Cell *chain_driver(Cell *cell, IdString port, IdString cell_type) {
		auto sig = sigmap(cell->getPort(port));
		Cell *drv = sig_to_driver[sig];
		if (!drv || !is_right_type(drv, cell_type))
			return nullptr;
		// SILIMATE: the rebuilt tree keeps only the head cell's truncation, so a
		// carry-dropping driver cannot join a wider consumer
		if (carry_link_unsafe(drv, cell))
			return nullptr;
		for (auto bit : sig)
			if (input_port_sigs.count(bit) && !consumed_cells.count(drv))
				return nullptr;
		return drv;
	}

	// Create a balanced binary tree from a vector of source signals
	// One tree node combining two subtrees, modelled on `cell`. $add gains a
	// carry bit and $mul the sum of its operand widths; anything else keeps the
	// reference cell's output width.
	SigSpec emit_tree_node(SigSpec lhs, SigSpec rhs, IdString cell_type, Cell *cell)
	{
		Cell* new_cell = module->addCell(NEW_ID2_SUFFIX("tree"), cell_type);
		new_cell->attributes = cell->attributes;

		int out_width = cell->getParam(ID::Y_WIDTH).as_int();
		if (cell_type == ID($add))
			out_width = max(lhs.size(), rhs.size()) + 1;
		else if (cell_type == ID($mul))
			out_width = lhs.size() + rhs.size();
		Wire* out_wire = module->addWire(NEW_ID2_SUFFIX("tree_out"), out_width);

		new_cell->setPort(ID::A, lhs);
		new_cell->setPort(ID::B, rhs);
		new_cell->setPort(ID::Y, out_wire);
		new_cell->fixup_parameters();
		new_cell->setParam(ID::A_SIGNED, cell->getParam(ID::A_SIGNED));
		new_cell->setParam(ID::B_SIGNED, cell->getParam(ID::B_SIGNED));

		cell_count[cell_type]++;
		return out_wire;
	}

	// Splits at ceil(n/2) rather than floor, so the deeper half sits on the
	// left; the emitted netlist shape is pinned by the tests.
	SigSpec create_balanced_tree(vector<SigSpec> &sources, IdString cell_type, Cell* cell) {
		if (sources.size() == 0)
			return SigSpec();
		if (sources.size() == 1)
			return sources[0];

		int mid = (sources.size() + 1) / 2;
		vector<SigSpec> left_sources(sources.begin(), sources.begin() + mid);
		vector<SigSpec> right_sources(sources.begin() + mid, sources.end());

		// Named steps: emit_tree_node adds cells and argument evaluation order
		// is unspecified, which would renumber them.
		SigSpec left_tree = create_balanced_tree(left_sources, cell_type, cell);
		SigSpec right_tree = create_balanced_tree(right_sources, cell_type, cell);
		return emit_tree_node(left_tree, right_tree, cell_type, cell);
	}

	bool full_child_output_at(const SigSpec &sig, int pos, Cell *&child, int &child_width,
			SlicedAddContext &ctx)
	{
		child = nullptr;
		child_width = 0;
		if (pos >= GetSize(sig))
			return false;

		SigBit bit = sig[pos];
		auto driver_it = ctx.bit_to_driver.find(bit);
		if (driver_it == ctx.bit_to_driver.end())
			return false;

		Cell *candidate = driver_it->second;
		if (!is_unsigned_add(candidate))
			return false;

		auto index_it = ctx.bit_to_driver_index.find(bit);
		if (index_it == ctx.bit_to_driver_index.end() || index_it->second != 0)
			return false;

		SigSpec y = sigmap(candidate->getPort(ID::Y));
		child_width = GetSize(y);
		if (pos + child_width > GetSize(sig))
			return false;

		for (int i = 0; i < child_width; i++)
			if (sig[pos + i] != y[i])
				return false;

		child = candidate;
		return true;
	}

	bool bit_is_partial_add_output(SigBit bit, SlicedAddContext &ctx)
	{
		auto driver_it = ctx.bit_to_driver.find(bit);
		if (driver_it == ctx.bit_to_driver.end())
			return false;
		return is_unsigned_add(driver_it->second);
	}

	bool extract_sliced_operand(const SigSpec &sig, int base_offset, vector<SigSpec> &summands,
			pool<Cell*> &cluster, pool<Cell*> &visiting, SlicedAddContext &ctx, bool &saw_sliced_edge)
	{
		for (int i = 0; i < GetSize(sig); )
		{
			Cell *child = nullptr;
			int child_width = 0;
			if (full_child_output_at(sig, i, child, child_width, ctx))
			{
				// SILIMATE: a carry-dropping child placed below the head's truncation
				// would have its restored carry land on a bit the head still keeps,
				// where it collides with whatever else drives that position.
				if (drops_carry(child) && base_offset + i + child_width < sliced_head_width)
					return false;
				if (i != 0 || child_width != GetSize(sig))
					saw_sliced_edge = true;
				if (!extract_sliced_add(child, base_offset + i, summands, cluster, visiting, ctx, saw_sliced_edge))
					return false;
				i += child_width;
				continue;
			}

			if (bit_is_partial_add_output(sig[i], ctx))
				return false;

			SigSpec leaf;
			int leaf_start = i;
			while (i < GetSize(sig))
			{
				Cell *next_child = nullptr;
				int next_child_width = 0;
				if (full_child_output_at(sig, i, next_child, next_child_width, ctx))
					break;
				if (bit_is_partial_add_output(sig[i], ctx))
					return false;
				leaf.append(sig[i]);
				i++;
			}

			if (is_nonzero(leaf))
				summands.push_back(shift_summand(leaf, base_offset + leaf_start));
		}

		return true;
	}

	bool extract_sliced_add(Cell *cell, int base_offset, vector<SigSpec> &summands,
			pool<Cell*> &cluster, pool<Cell*> &visiting, SlicedAddContext &ctx, bool &saw_sliced_edge)
	{
		if (!is_unsigned_add(cell) || visiting.count(cell))
			return false;

		visiting.insert(cell);
		cluster.insert(cell);

		for (IdString port : {ID::A, ID::B}) {
			SigSpec sig = sigmap(cell->getPort(port));
			if (!extract_sliced_operand(sig, base_offset, summands, cluster, visiting, ctx, saw_sliced_edge))
				return false;
		}

		visiting.erase(cell);
		return true;
	}

	bool operand_contains_full_child_output(const SigSpec &sig, Cell *child)
	{
		SigSpec y = sigmap(child->getPort(ID::Y));
		int width = GetSize(y);
		for (int pos = 0; pos + width <= GetSize(sig); pos++)
		{
			bool found = true;
			for (int i = 0; i < width; i++)
				if (sig[pos + i] != y[i]) {
					found = false;
					break;
				}
			if (found)
				return true;
		}
		return false;
	}

	bool has_downstream_add_sink(Cell *cell, pool<Cell*> &consumed_cells, SlicedAddContext &ctx)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		for (auto bit : y)
			for (auto sink : ctx.bit_to_sink[bit])
				if (sink != cell && !consumed_cells.count(sink) && is_unsigned_add(sink))
					for (IdString port : {ID::A, ID::B})
						if (operand_contains_full_child_output(sigmap(sink->getPort(port)), cell))
							return true;
		return false;
	}

	bool sliced_cluster_has_external_fanout(Cell *head_cell, pool<Cell*> &cluster, pool<Cell*> &consumed_cells,
			SlicedAddContext &ctx)
	{
		for (auto cell : cluster)
		{
			if (cell == head_cell)
				continue;

			SigSpec y = sigmap(cell->getPort(ID::Y));
			for (auto bit : y)
			{
				if (ctx.output_port_sigs.count(bit))
					return true;
				for (auto sink : ctx.bit_to_sink[bit])
					if (!cluster.count(sink) && !consumed_cells.count(sink))
						return true;
			}
		}

		return false;
	}

	bool try_sliced_add_tree(Cell *head_cell, pool<Cell*> &consumed_cells, SlicedAddContext &ctx)
	{
		if (!is_unsigned_add(head_cell) || consumed_cells.count(head_cell) ||
				has_downstream_add_sink(head_cell, consumed_cells, ctx))
			return false;

		vector<SigSpec> summands;
		pool<Cell*> cluster, visiting;
		bool saw_sliced_edge = false;
		sliced_head_width = GetSize(sigmap(head_cell->getPort(ID::Y)));
		if (!extract_sliced_add(head_cell, 0, summands, cluster, visiting, ctx, saw_sliced_edge))
			return false;
		if (!saw_sliced_edge || GetSize(cluster) <= 1 || GetSize(summands) <= 2)
			return false;
		if (sliced_cluster_has_external_fanout(head_cell, cluster, consumed_cells, ctx))
			return false;

		log_debug("  Creating sliced add tree for %s with %d summands and %d cells...\n",
				log_id(head_cell), GetSize(summands), GetSize(cluster));

		SigSpec tree_output = create_balanced_tree(summands, ID($add), head_cell);
		SigSpec head_output = sigmap(head_cell->getPort(ID::Y));
		int connect_width = std::min(head_output.size(), tree_output.size());
		module->connect(head_output.extract(0, connect_width), tree_output.extract(0, connect_width));
		if (head_output.size() > tree_output.size())
			module->connect(head_output.extract(connect_width, head_output.size() - connect_width),
					SigSpec(State::S0, head_output.size() - connect_width));

		for (auto cell : cluster)
			consumed_cells.insert(cell);
		sliced_add_count++;
		return true;
	}

	OptBalanceTreeWorker(Module *module, const vector<IdString> cell_types) : module(module), sigmap(module) {
		// Do for each cell type
		for (auto cell_type : cell_types) {
			// Index all of the nets in the module
			sig_to_driver.clear();
			dict<SigSpec, pool<Cell*>> sig_to_sink;
			SlicedAddContext sliced_add_ctx;
			for (auto cell : module->selected_cells())
			{
				for (auto &conn : cell->connections())
				{
					SigSpec sig = sigmap(conn.second);
					if (cell->output(conn.first)) {
						sig_to_driver[sig] = cell;
						for (int i = 0; i < GetSize(sig); i++) {
							sliced_add_ctx.bit_to_driver[sig[i]] = cell;
							sliced_add_ctx.bit_to_driver_index[sig[i]] = i;
						}
					}

					if (cell->input(conn.first))
					{
						if (sig_to_sink.count(sig) == 0)
							sig_to_sink[sig] = pool<Cell*>();
						sig_to_sink[sig].insert(cell);
						for (auto bit : sig)
							sliced_add_ctx.bit_to_sink[bit].insert(cell);
					}
				}
			}

			// Need to check if any wires connect to module ports
			input_port_sigs.clear();
			pool<SigSpec> output_port_sigs;
			for (auto wire : module->selected_wires())
				if (wire->port_input || wire->port_output) {
					SigSpec sig = sigmap(wire);
					for (auto bit : sig) {
						if (wire->port_input)
							input_port_sigs.insert(bit);
						if (wire->port_output) {
							output_port_sigs.insert(bit);
							sliced_add_ctx.output_port_sigs.insert(bit);
						}
					}
				}

			// Actual logic starts here
			consumed_cells.clear();
			if (cell_type == ID($add))
				for (auto cell : module->selected_cells())
					try_sliced_add_tree(cell, consumed_cells, sliced_add_ctx);

			for (auto cell : module->selected_cells())
			{
				// If consumed or not the correct type, skip
				if (consumed_cells.count(cell) || !is_right_type(cell, cell_type))
					continue;

				// BFS, following all chains until they hit a cell of a different type
				// Pick the longest one
				auto y = sigmap(cell->getPort(ID::Y));
				pool<Cell*> sinks;

				// SILIMATE: a sink the carry guard refuses to merge ends the chain
				// here, so this cell heads its own subchain
				for (auto x : sig_to_sink[y])
					if (is_right_type(x, cell_type) && carry_link_unsafe(cell, x)) {
						sinks.insert(cell);
						break;
					}

				pool<Cell*> current_loads = sig_to_sink[y];
				pool<Cell*> next_loads;
				pool<Cell*> visited_loads;
				while (!current_loads.empty())
				{
					// Find each sink and see what they are
					for (auto x : current_loads)
					{
						if (!visited_loads.insert(x).second)
							continue;

						// If not the correct type, don't follow any further
						// (but add the originating cell to the list of sinks)
						if (!is_right_type(x, cell_type))
						{
							sinks.insert(cell);
							continue;
						}

						auto xy = sigmap(x->getPort(ID::Y));

						// If this signal drives a port, add it to the sinks
						// (even though it may not be the end of a chain)
						for (auto bit : xy) {
							if (output_port_sigs.count(bit) && !consumed_cells.count(x)) {
								sinks.insert(x);
								break;
							}
						}

						// Search signal's fanout
						auto& next = sig_to_sink[xy];
						for (auto z : next)
							next_loads.insert(z);
					}

					// If we couldn't find any downstream loads, stop.
					// Create a reduction for each of the max-length chains we found
					if (next_loads.empty())
					{
						for (auto s : current_loads)
						{
							// Not one of our gates? Don't follow any further
							if (!is_right_type(s, cell_type))
								continue;

							sinks.insert(s);
						}
						break;
					}

					// Otherwise, continue down the chain
					current_loads = next_loads;
					next_loads.clear();
				}

				// We have our list of sinks, now go tree balance the chains
				for (auto head_cell : sinks)
				{
					// Avoid duplication if we already were covered
					if (consumed_cells.count(head_cell))
						continue;

					// Collect the chain cone into a topological sort
					TopoSort<Cell*, IdString::compare_ptr_by_name<Cell>> toposort;
					toposort.analyze_loops = false;
					toposort.node(head_cell);
					vector<Cell*> queue = {head_cell};
					while (!queue.empty())
					{
						Cell *x = queue.back();
						queue.pop_back();
						for (IdString port: {ID::A, ID::B})
							if (Cell *drv = chain_driver(x, port, cell_type)) {
								if (!toposort.has_node(drv))
									queue.push_back(drv);
								toposort.edge(drv, x);
							}
					}

					// Abandon chains containing combinational loops, since
					// rebalancing them is not sound (and would not terminate)
					if (!toposort.sort())
						continue;

					// Get sources of the chain: process cells from head to
					// drivers, counting the paths leading back to the head so
					// reconvergent sources are counted with multiplicity
					dict<SigSpec, int> sources;
					dict<SigSpec, bool> signeds;
					int inner_cells = GetSize(toposort.sorted) - 1;
					dict<Cell*, int> reach;
					reach[head_cell] = 1;
					for (int i = GetSize(toposort.sorted); i-- > 0; )
					{
						Cell* x = toposort.sorted[i];
						for (IdString port: {ID::A, ID::B}) {
							if (Cell *drv = chain_driver(x, port, cell_type)) {
								reach[drv] += reach[x];
							} else {
								auto sig = sigmap(x->getPort(port));
								sources[sig] += reach[x];
								signeds[sig] = x->getParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
							}
						}
					}

					if (inner_cells)
					{
						// Create a tree
						log_debug("  Creating tree for %s with %d sources and %d inner cells...\n", head_cell, GetSize(sources), inner_cells);

						// Build a vector of all source signals
						vector<SigSpec> source_signals;
						vector<bool> signed_flags;
						for (auto &source : sources) {
							for (int i = 0; i < source.second; i++) {
								source_signals.push_back(source.first);
								signed_flags.push_back(signeds[source.first]);
							}
						}

						// If not all signed flags are the same, do not balance
						if (!std::all_of(signed_flags.begin(), signed_flags.end(), [&](bool flag) { return flag == signed_flags[0]; })) {
							continue;
						}

						// Create the balanced tree
						SigSpec tree_output = create_balanced_tree(source_signals, cell_type, head_cell);

						// Connect the tree output to the head cell's output
						SigSpec head_output = sigmap(head_cell->getPort(ID::Y));
						int connect_width = std::min(head_output.size(), tree_output.size());
						module->connect(head_output.extract(0, connect_width), tree_output.extract(0, connect_width));
						if (head_output.size() > tree_output.size()) {
							SigBit sext_bit = head_cell->getParam(ID::A_SIGNED).as_bool() ? head_output[connect_width - 1] : State::S0;
							module->connect(head_output.extract(connect_width, head_output.size() - connect_width), SigSpec(sext_bit, head_output.size() - connect_width));
						}

						// Mark consumed cell for removal
						consumed_cells.insert(head_cell);
					}
				}
			}

			// Remove all consumed cells, which now have been replaced by trees
			for (auto cell : consumed_cells)
				module->remove(cell);
		}
	}
};

struct OptBalanceTreePass : public Pass {
	OptBalanceTreePass() : Pass("opt_balance_tree", "$and/$or/$xor/$add/$mul cascades to trees") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_balance_tree [options] [selection]\n");
		log("\n");
		log("This pass converts cascaded chains of $and/$or/$xor/$add/$mul cells into\n");
		log("trees of cells to improve timing.\n");
		log("\n");
		log("    -arith\n");
		log("        only convert arithmetic cells.\n");
		log("\n");
		log("    -logic\n");
		log("        only convert logic cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_BALANCE_TREE pass (cell cascades to trees).\n");
		// log_experimental("open_balance_tree");

		// Handle arguments
		size_t argidx;
		vector<IdString> cell_types = {ID($and), ID($or), ID($xor), ID($add), ID($mul)};
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-arith") {
				cell_types = {ID($add), ID($mul)};
				continue;
			}
			if (args[argidx] == "-logic") {
				cell_types = {ID($and), ID($or), ID($xor)};
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Count of all cells that were packed
		dict<IdString, int> cell_count;
		int sliced_add_count = 0;
		for (auto module : design->selected_modules()) {
			OptBalanceTreeWorker worker(module, cell_types);
			for (auto cell : worker.cell_count) {
				cell_count[cell.first] += cell.second;
			}
			sliced_add_count += worker.sliced_add_count;
		}

		// Log stats
		for (auto cell_type : cell_types)
			log("Converted %d %s cells into trees.\n", cell_count[cell_type], cell_type.unescape());
		if (std::find(cell_types.begin(), cell_types.end(), ID($add)) != cell_types.end())
			log("Converted %d sliced $add chains into trees.\n", sliced_add_count);

		// Clean up
		Yosys::run_pass("clean -purge");
	}
} OptBalanceTreePass;

PRIVATE_NAMESPACE_END
