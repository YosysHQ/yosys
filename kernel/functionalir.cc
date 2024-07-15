/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
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

#include "kernel/functionalir.h"

YOSYS_NAMESPACE_BEGIN

template <class T, class Factory>
class CellSimplifier {
	Factory &factory;
	T reduce_shift_width(T b, int b_width, int y_width, int &reduced_b_width) {
		log_assert(y_width > 0);
		int new_width = ceil_log2(y_width + 1);
		if (b_width <= new_width) {
			reduced_b_width = b_width;
			return b;
		} else {
			reduced_b_width = new_width;
			T lower_b = factory.slice(b, b_width, 0, new_width);
			T overflow = factory.unsigned_greater_than(b, factory.constant(RTLIL::Const(y_width, b_width)), b_width);
			return factory.mux(lower_b, factory.constant(RTLIL::Const(y_width, new_width)), overflow, new_width);
		}
	}
	T sign(T a, int a_width) {
		return factory.slice(a, a_width, a_width - 1, 1);
	}
	T neg_if(T a, int a_width, T s) {
		return factory.mux(a, factory.unary_minus(a, a_width), s, a_width);
	}
	T abs(T a, int a_width) {
		return neg_if(a, a_width, sign(a, a_width));
	}
public:
	T reduce_or(T a, int width) {
		if (width == 1)
			return a;
		return factory.reduce_or(a, width);
	}
	T extend(T a, int in_width, int out_width, bool is_signed) {
		if(in_width == out_width)
			return a;
		if(in_width > out_width)
			return factory.slice(a, in_width, 0, out_width);
		return factory.extend(a, in_width, out_width, is_signed);
	}
	T logical_shift_left(T a, T b, int y_width, int b_width) {
		int reduced_b_width;
		T reduced_b = reduce_shift_width(b, b_width, y_width, reduced_b_width);
		return factory.logical_shift_left(a, reduced_b, y_width, reduced_b_width);
	}
	T logical_shift_right(T a, T b, int y_width, int b_width) {
		int reduced_b_width;
		T reduced_b = reduce_shift_width(b, b_width, y_width, reduced_b_width);
		return factory.logical_shift_right(a, reduced_b, y_width, reduced_b_width);
	}
	T arithmetic_shift_right(T a, T b, int y_width, int b_width) {
		int reduced_b_width;
		T reduced_b = reduce_shift_width(b, b_width, y_width, reduced_b_width);
		return factory.arithmetic_shift_right(a, reduced_b, y_width, reduced_b_width);
	}
	T bitwise_mux(T a, T b, T s, int width) {
		T aa = factory.bitwise_and(a, factory.bitwise_not(s, width), width);
		T bb = factory.bitwise_and(b, s, width);
		return factory.bitwise_or(aa, bb, width);
	}
	CellSimplifier(Factory &f) : factory(f) {}
private:
	T handle_pow(T a0, int a_width, T b, int b_width, int y_width, bool is_signed) {
		T a = extend(a0, a_width, y_width, is_signed);
		T r = factory.constant(Const(1, y_width));
		for(int i = 0; i < b_width; i++) {
			T b_bit = factory.slice(b, b_width, i, 1);
			r = factory.mux(r, factory.mul(r, a, y_width), b_bit, y_width);
			a = factory.mul(a, a, y_width);
		}
		if (is_signed) {
			T a_ge_1 = factory.unsigned_greater_than(abs(a0, a_width), factory.constant(Const(1, a_width)), a_width);
			T zero_result = factory.bitwise_and(a_ge_1, sign(b, b_width), 1);
			r = factory.mux(r, factory.constant(Const(0, y_width)), zero_result, y_width);
		}
		return r;
	}
	T handle_bmux(T a, T s, int a_width, int a_offset, int width, int s_width, int sn) {
		if(sn < 1)
			return factory.slice(a, a_width, a_offset, width);
		else {
			T y0 = handle_bmux(a, s, a_width, a_offset, width, s_width, sn - 1);
			T y1 = handle_bmux(a, s, a_width, a_offset + (width << (sn - 1)), width, s_width, sn - 1);
			return factory.mux(y0, y1, factory.slice(s, s_width, sn - 1, 1), width);
		}
	}
public:
	T handle(IdString cellType, dict<IdString, Const> parameters, dict<IdString, T> inputs)
	{
		int a_width = parameters.at(ID(A_WIDTH), Const(-1)).as_int();
		int b_width = parameters.at(ID(B_WIDTH), Const(-1)).as_int();
		int y_width = parameters.at(ID(Y_WIDTH), Const(-1)).as_int();
		bool a_signed = parameters.at(ID(A_SIGNED), Const(0)).as_bool();
		bool b_signed = parameters.at(ID(B_SIGNED), Const(0)).as_bool();
		if(cellType.in({ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor), ID($mul)})){
			bool is_signed = a_signed && b_signed;
			T a = extend(inputs.at(ID(A)), a_width, y_width, is_signed);
			T b = extend(inputs.at(ID(B)), b_width, y_width, is_signed);
			if(cellType == ID($add))
				return factory.add(a, b, y_width);
			else if(cellType == ID($sub))
				return factory.sub(a, b, y_width);
			else if(cellType == ID($mul))
				return factory.mul(a, b, y_width);
			else if(cellType == ID($and))
				return factory.bitwise_and(a, b, y_width);
			else if(cellType == ID($or))
				return factory.bitwise_or(a, b, y_width);
			else if(cellType == ID($xor))
				return factory.bitwise_xor(a, b, y_width);
			else if(cellType == ID($xnor))
				return factory.bitwise_not(factory.bitwise_xor(a, b, y_width), y_width);
			else
				log_abort();
		}else if(cellType.in({ID($eq), ID($ne), ID($eqx), ID($nex), ID($le), ID($lt), ID($ge), ID($gt)})){
			bool is_signed = a_signed && b_signed;
			int width = max(a_width, b_width);
			T a = extend(inputs.at(ID(A)), a_width, width, is_signed);
			T b = extend(inputs.at(ID(B)), b_width, width, is_signed);
			if(cellType.in({ID($eq), ID($eqx)}))
				return extend(factory.equal(a, b, width), 1, y_width, false);
			else if(cellType.in({ID($ne), ID($nex)}))
				return extend(factory.not_equal(a, b, width), 1, y_width, false);
			else if(cellType == ID($lt))
				return extend(is_signed ? factory.signed_greater_than(b, a, width) : factory.unsigned_greater_than(b, a, width), 1, y_width, false);
			else if(cellType == ID($le))
				return extend(is_signed ? factory.signed_greater_equal(b, a, width) : factory.unsigned_greater_equal(b, a, width), 1, y_width, false);
			else if(cellType == ID($gt))
				return extend(is_signed ? factory.signed_greater_than(a, b, width) : factory.unsigned_greater_than(a, b, width), 1, y_width, false);
			else if(cellType == ID($ge))
				return extend(is_signed ? factory.signed_greater_equal(a, b, width) : factory.unsigned_greater_equal(a, b, width), 1, y_width, false);
			else
				log_abort();
		}else if(cellType.in({ID($logic_or), ID($logic_and)})){
			T a = reduce_or(inputs.at(ID(A)), a_width);
			T b = reduce_or(inputs.at(ID(B)), b_width);
			T y = cellType == ID($logic_and) ? factory.bitwise_and(a, b, 1) : factory.bitwise_or(a, b, 1);
			return extend(y, 1, y_width, false);
		}else if(cellType == ID($not)){
			T a = extend(inputs.at(ID(A)), a_width, y_width, a_signed);
			return factory.bitwise_not(a, y_width);
		}else if(cellType == ID($pos)){
			return extend(inputs.at(ID(A)), a_width, y_width, a_signed);
		}else if(cellType == ID($neg)){
			T a = extend(inputs.at(ID(A)), a_width, y_width, a_signed);
			return factory.unary_minus(a, y_width);
		}else if(cellType == ID($logic_not)){
			T a = reduce_or(inputs.at(ID(A)), a_width);
			T y = factory.bitwise_not(a, 1);
			return extend(y, 1, y_width, false);
		}else if(cellType.in({ID($reduce_or), ID($reduce_bool)})){
			T a = reduce_or(inputs.at(ID(A)), a_width);
			return extend(a, 1, y_width, false);
		}else if(cellType == ID($reduce_and)){
			T a = factory.reduce_and(inputs.at(ID(A)), a_width);
			return extend(a, 1, y_width, false);
		}else if(cellType.in({ID($reduce_xor), ID($reduce_xnor)})){
			T a = factory.reduce_xor(inputs.at(ID(A)), a_width);
			T y = cellType == ID($reduce_xnor) ? factory.bitwise_not(a, 1) : a;
			return extend(y, 1, y_width, false);
		}else if(cellType == ID($shl) || cellType == ID($sshl)){
			T a = extend(inputs.at(ID(A)), a_width, y_width, a_signed);
			T b = inputs.at(ID(B));
			return logical_shift_left(a, b, y_width, b_width);
		}else if(cellType == ID($shr) || cellType == ID($sshr)){
			int width = max(a_width, y_width);
			T a = extend(inputs.at(ID(A)), a_width, width, a_signed);
			T b = inputs.at(ID(B));
			T y = a_signed && cellType == ID($sshr) ?
				arithmetic_shift_right(a, b, width, b_width) :
				logical_shift_right(a, b, width, b_width);
			return extend(y, width, y_width, a_signed);
		}else if(cellType == ID($shiftx) || cellType == ID($shift)){
			int width = max(a_width, y_width);
			T a = extend(inputs.at(ID(A)), a_width, width, cellType == ID($shift) && a_signed);
			T b = inputs.at(ID(B));
			T shr = logical_shift_right(a, b, width, b_width);
			if(b_signed) {
				T sign_b = sign(b, b_width);
				T shl = logical_shift_left(a, factory.unary_minus(b, b_width), width, b_width);
				T y = factory.mux(shr, shl, sign_b, width);
				return extend(y, width, y_width, false);
			} else {
				return extend(shr, width, y_width, false);
			}
		}else if(cellType == ID($mux)){
			int width = parameters.at(ID(WIDTH)).as_int();
			return factory.mux(inputs.at(ID(A)), inputs.at(ID(B)), inputs.at(ID(S)), width);
		}else if(cellType == ID($pmux)){
			int width = parameters.at(ID(WIDTH)).as_int();
			int s_width = parameters.at(ID(S_WIDTH)).as_int();
			return factory.pmux(inputs.at(ID(A)), inputs.at(ID(B)), inputs.at(ID(S)), width, s_width);
		}else if(cellType == ID($concat)){
			T a = inputs.at(ID(A));
			T b = inputs.at(ID(B));
			return factory.concat(a, a_width, b, b_width);
		}else if(cellType == ID($slice)){
			int offset = parameters.at(ID(OFFSET)).as_int();
			T a = inputs.at(ID(A));
			return factory.slice(a, a_width, offset, y_width);
		}else if(cellType.in({ID($div), ID($mod), ID($divfloor), ID($modfloor)})) {
			int width = max(a_width, b_width);
			bool is_signed = a_signed && b_signed;
			T a = extend(inputs.at(ID(A)), a_width, width, is_signed);
			T b = extend(inputs.at(ID(B)), b_width, width, is_signed);
			if(is_signed) {
				if(cellType == ID($div)) {
					T abs_y = factory.unsigned_div(abs(a, width), abs(b, width), width);
					T out_sign = factory.not_equal(sign(a, width), sign(b, width), 1);
					return neg_if(extend(abs_y, width, y_width, true), y_width, out_sign);
				} else if(cellType == ID($mod)) {
					T abs_y = factory.unsigned_mod(abs(a, width), abs(b, width), width);
					return neg_if(extend(abs_y, width, y_width, true), y_width, sign(a, width));
				} else if(cellType == ID($divfloor)) {
					T b_sign = sign(b, width);
					T a1 = neg_if(a, width, b_sign);
					T b1 = neg_if(b, width, b_sign);
					T a1_sign = sign(a1, width);
					T a2 = factory.mux(a1, factory.bitwise_not(a1, width), a1_sign, width);
					T y1 = factory.unsigned_div(a2, b1, width);
					T y2 = factory.mux(y1, factory.bitwise_not(y1, width), a1_sign, width);
					return extend(y2, width, y_width, true);
				} else if(cellType == ID($modfloor)) {
					T abs_b = abs(b, width);
					T abs_y = factory.unsigned_mod(abs(a, width), abs_b, width);
					T flip_y = factory.bitwise_and(factory.bitwise_xor(sign(a, width), sign(b, width), 1), factory.reduce_or(abs_y, width), 1);
					T y_flipped = factory.mux(abs_y, factory.sub(abs_b, abs_y, width), flip_y, width);
					T y = neg_if(y_flipped, width, sign(b, b_width));
					return extend(y, width, y_width, true);
				} else
					log_error("unhandled cell in CellSimplifier %s\n", cellType.c_str());
			} else {
				if(cellType.in({ID($mod), ID($modfloor)}))
					return extend(factory.unsigned_mod(a, b, width), width, y_width, false);
				else
					return extend(factory.unsigned_div(a, b, width), width, y_width, false);
			}
		} else if(cellType == ID($pow)) {
			return handle_pow(inputs.at(ID(A)), a_width, inputs.at(ID(B)), b_width, y_width, a_signed && b_signed);
		} else if (cellType == ID($lut)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			Const lut_table = parameters.at(ID(LUT));
			T a = inputs.at(ID(A));
			// Output initialization
			T y = factory.constant(Const(0, 1));
			// Iterate over each possible input combination
			for (int i = 0; i < (1 << width); ++i) {
				// Create a constant representing the value of i
				T i_val = factory.constant(Const(i, width));
				// Check if the input matches this value
				T match = factory.equal(a, i_val, width);
				// Get the corresponding LUT value
				bool lut_val = lut_table.bits[i] == State::S1;
				T lut_output = factory.constant(Const(lut_val, 1));
				// Use a multiplexer to select the correct output based on the match
				y = factory.mux(y, lut_output, match, 1);
			}
			return y;
		} else if (cellType == ID($bwmux)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			T a = inputs.at(ID(A));
			T b = inputs.at(ID(B));
			T s = inputs.at(ID(S));
			return factory.bitwise_or(
				factory.bitwise_and(a, factory.bitwise_not(s, width), width),
				factory.bitwise_and(b, s, width), width);
		} else if (cellType == ID($bweqx)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			T a = inputs.at(ID(A));
			T b = inputs.at(ID(B));
			return factory.bitwise_not(factory.bitwise_xor(a, b, width), width);
		} else if(cellType == ID($bmux)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			int s_width = parameters.at(ID(S_WIDTH)).as_int();
			return handle_bmux(inputs.at(ID(A)), inputs.at(ID(S)), width << s_width, 0, width, s_width, s_width);
		} else if(cellType == ID($demux)) {
			int width = parameters.at(ID(WIDTH)).as_int();
			int s_width = parameters.at(ID(S_WIDTH)).as_int();
			int y_width = width << s_width;
			int b_width = ceil_log2(y_width + 1);
			T a = extend(inputs.at(ID(A)), width, y_width, false);
			T s = factory.extend(inputs.at(ID(S)), s_width, b_width, false);
			T b = factory.mul(s, factory.constant(Const(width, b_width)), b_width);
			return factory.logical_shift_left(a, b, y_width, b_width);
		} else {
			log_error("unhandled cell in CellSimplifier %s\n", cellType.c_str());
		}
	}
};

template <class T, class Factory>
class FunctionalIRConstruction {
	std::deque<DriveSpec> queue;
	dict<DriveSpec, T> graph_nodes;
	idict<Cell *> cells;
	DriverMap driver_map;
	Factory& factory;
	CellSimplifier<T, Factory> simplifier;
	vector<Mem> memories_vector;
	dict<Cell*, Mem*> memories;

	T enqueue(DriveSpec const &spec)
	{
		auto it = graph_nodes.find(spec);
		if(it == graph_nodes.end()){
			auto node = factory.create_pending(spec.size());
			graph_nodes.insert({spec, node});
			queue.emplace_back(spec);
			return node;
		}else
			return it->second;
	}
public:
	FunctionalIRConstruction(Factory &f) : factory(f), simplifier(f) {}
	void add_module(Module *module)
	{
		driver_map.add(module);
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($assert), ID($assume), ID($cover), ID($check)))
				enqueue(DriveBitMarker(cells(cell), 0));
		}
		for (auto wire : module->wires()) {
			if (wire->port_output) {
				T node = enqueue(DriveChunk(DriveChunkWire(wire, 0, wire->width)));
				factory.declare_output(node, wire->name, wire->width);
			}
		}
		memories_vector = Mem::get_all_memories(module);
		for (auto &mem : memories_vector) {
			if (mem.cell != nullptr)
				memories[mem.cell] = &mem;
		}
	}
	T concatenate_read_results(Mem *, vector<T> results)
	{
        /* TODO: write code to check that this is ok to do */
		if(results.size() == 0)
			return factory.undriven(0);
		T node = results[0];
		int size = results[0].width();
		for(size_t i = 1; i < results.size(); i++) {
			node = factory.concat(node, size, results[i], results[i].width());
			size += results[i].width();
		}
		return node;
	}
	T handle_memory(Mem *mem)
	{
		vector<T> read_results;
		int addr_width = ceil_log2(mem->size);
		int data_width = mem->width;
		T node = factory.state_memory(mem->cell->name, addr_width, data_width);
		for (auto &rd : mem->rd_ports) {
			log_assert(!rd.clk_enable);
			T addr = enqueue(driver_map(DriveSpec(rd.addr)));
			read_results.push_back(factory.memory_read(node, addr, addr_width, data_width));
		}
		for (auto &wr : mem->wr_ports) {
			T en = enqueue(driver_map(DriveSpec(wr.en)));
			T addr = enqueue(driver_map(DriveSpec(wr.addr)));
			T new_data = enqueue(driver_map(DriveSpec(wr.data)));
			T old_data = factory.memory_read(node, addr, addr_width, data_width);
			T wr_data = simplifier.bitwise_mux(old_data, new_data, en, data_width);
			node = factory.memory_write(node, addr, wr_data, addr_width, data_width);
		}
		factory.declare_state_memory(node, mem->cell->name, addr_width, data_width);
		return concatenate_read_results(mem, read_results);
	}
	void process_queue()
	{
		for (; !queue.empty(); queue.pop_front()) {
			DriveSpec spec = queue.front();
			T pending = graph_nodes.at(spec);

			if (spec.chunks().size() > 1) {
				auto chunks = spec.chunks();
				T node = enqueue(chunks[0]);
				int width = chunks[0].size();
				for(size_t i = 1; i < chunks.size(); i++) {
					node = factory.concat(node, width, enqueue(chunks[i]), chunks[i].size());
					width += chunks[i].size();
				}
				factory.update_pending(pending, node);
			} else if (spec.chunks().size() == 1) {
				DriveChunk chunk = spec.chunks()[0];
				if (chunk.is_wire()) {
					DriveChunkWire wire_chunk = chunk.wire();
					if (wire_chunk.is_whole()) {
						if (wire_chunk.wire->port_input) {
							T node = factory.input(wire_chunk.wire->name, wire_chunk.width);
							factory.suggest_name(node, wire_chunk.wire->name);
							factory.update_pending(pending, node);
						} else {
							DriveSpec driver = driver_map(DriveSpec(wire_chunk));
							T node = enqueue(driver);
							factory.suggest_name(node, wire_chunk.wire->name);
							factory.update_pending(pending, node);
						}
					} else {
						DriveChunkWire whole_wire(wire_chunk.wire, 0, wire_chunk.wire->width);
						T node = factory.slice(enqueue(whole_wire), wire_chunk.wire->width, wire_chunk.offset, wire_chunk.width);
						factory.update_pending(pending, node);
					}
				} else if (chunk.is_port()) {
					DriveChunkPort port_chunk = chunk.port();
					if (port_chunk.is_whole()) {
						if (driver_map.celltypes.cell_output(port_chunk.cell->type, port_chunk.port)) {
							if (port_chunk.cell->type.in(ID($dff), ID($ff)))
							{
								Cell *cell = port_chunk.cell;
								T node = factory.state(cell->name, port_chunk.width);
								factory.suggest_name(node, port_chunk.cell->name);
								factory.update_pending(pending, node);
								for (auto const &conn : cell->connections()) {
									if (driver_map.celltypes.cell_input(cell->type, conn.first)) {
										T node = enqueue(DriveChunkPort(cell, conn));
										factory.declare_state(node, cell->name, port_chunk.width);
									}
								}
							}
							else
							{
								T cell = enqueue(DriveChunkMarker(cells(port_chunk.cell), 0, port_chunk.width));
								factory.suggest_name(cell, port_chunk.cell->name);
								T node = factory.cell_output(cell, port_chunk.cell->type, port_chunk.port, port_chunk.width);
								factory.suggest_name(node, port_chunk.cell->name.str() + "$" + port_chunk.port.str());
								factory.update_pending(pending, node);
							}
						} else {
							DriveSpec driver = driver_map(DriveSpec(port_chunk));
							factory.update_pending(pending, enqueue(driver));
						}
					} else {
						DriveChunkPort whole_port(port_chunk.cell, port_chunk.port, 0, GetSize(port_chunk.cell->connections().at(port_chunk.port)));
						T node = factory.slice(enqueue(whole_port), whole_port.width, port_chunk.offset, port_chunk.width);
						factory.update_pending(pending, node);
					}
				} else if (chunk.is_constant()) {
					T node = factory.constant(chunk.constant());
					factory.suggest_name(node, "$const" + std::to_string(chunk.size()) + "b" + chunk.constant().as_string());
					factory.update_pending(pending, node);
				} else if (chunk.is_multiple()) {
					vector<T> args;
					for (auto const &driver : chunk.multiple().multiple())
						args.push_back(enqueue(driver));
					T node = factory.multiple(args, chunk.size());
					factory.update_pending(pending, node);
				} else if (chunk.is_marker()) {
					Cell *cell = cells[chunk.marker().marker];
					if (cell->is_mem_cell()) {
						Mem *mem = memories.at(cell, nullptr);
						log_assert(mem != nullptr);
						T node = handle_memory(mem);
						factory.update_pending(pending, node);
					} else {
						dict<IdString, T> connections;
						for(auto const &conn : cell->connections()) {
							if(driver_map.celltypes.cell_input(cell->type, conn.first))
								connections.insert({ conn.first, enqueue(DriveChunkPort(cell, conn)) });
						}
						T node = simplifier.handle(cell->type, cell->parameters, connections);
						factory.update_pending(pending, node);
					}
				} else if (chunk.is_none()) {
					T node = factory.undriven(chunk.size());
					factory.update_pending(pending, node);
				} else {
					log_error("unhandled drivespec: %s\n", log_signal(chunk));
					log_abort();
				}
			} else {
				log_abort();
			}
		}
	}
};

FunctionalIR FunctionalIR::from_module(Module *module) {
    FunctionalIR ir;
    auto factory = ir.factory();
    FunctionalIRConstruction<FunctionalIR::Node, FunctionalIR::Factory> ctor(factory);
    ctor.add_module(module);
    ctor.process_queue();
    ir.topological_sort();
    ir.forward_buf();
    return ir;
}

void FunctionalIR::topological_sort() {
    Graph::SccAdaptor compute_graph_scc(_graph);
    bool scc = false;
    std::vector<int> perm;
    topo_sorted_sccs(compute_graph_scc, [&](int *begin, int *end) {
        perm.insert(perm.end(), begin, end);
        if (end > begin + 1)
        {
            log_warning("SCC:");
            for (int *i = begin; i != end; ++i)
                log(" %d", *i);
            log("\n");
            scc = true;
        }
    }, /* sources_first */ true);
    _graph.permute(perm);
    if(scc) log_error("combinational loops, aborting\n");
}

IdString merge_name(IdString a, IdString b) {
	if(a[0] == '$' && b[0] == '\\')
		return b;
	else
		return a;
}

void FunctionalIR::forward_buf() {
    std::vector<int> perm, alias;
    perm.clear();

    for (int i = 0; i < _graph.size(); ++i)
    {
        auto node = _graph[i];
        if (node.function().fn() == Fn::buf && node.arg(0).index() < i)
        {
            int target_index = alias[node.arg(0).index()];
            auto target_node = _graph[perm[target_index]];
			if(node.has_sparse_attr()) {
				if(target_node.has_sparse_attr()) {
					IdString id = merge_name(node.sparse_attr(), target_node.sparse_attr());
					target_node.sparse_attr() = id;
				} else {
					IdString id = node.sparse_attr();
					target_node.sparse_attr() = id;
				}
			}
            alias.push_back(target_index);
        }
        else
        {
            alias.push_back(GetSize(perm));
            perm.push_back(i);
        }
    }
    _graph.permute(perm, alias);
}

static std::string quote_fmt(const char *fmt)
{
	std::string r;
	for(const char *p = fmt; *p != 0; p++) {
		switch(*p) {
		case '\n': r += "\\n"; break;
		case '\t': r += "\\t"; break;
		case '"': r += "\\\""; break;
		case '\\': r += "\\\\"; break;
		default: r += *p; break;
		}
	}
	return r;
}

void FunctionalTools::Writer::print_impl(const char *fmt, vector<std::function<void()>> &fns)
{
	size_t next_index = 0;
	for(const char *p = fmt; *p != 0; p++)
		switch(*p) {
		case '{':
			if(*++p == '{') {
				*os << '{';
			} else {
				char *pe;
				size_t index = strtoul(p, &pe, 10);
				if(*pe != '}')
					log_error("invalid format string: expected {<number>}, {} or {{, got \"%s\": \"%s\"\n",
						quote_fmt(std::string(p - 1, pe - p + 2).c_str()).c_str(),
						quote_fmt(fmt).c_str());
				if(p == pe)
					index = next_index;
				else
					p = pe;
				if(index >= fns.size())
					log_error("invalid format string: index %zu out of bounds (%zu): \"%s\"\n", index, fns.size(), quote_fmt(fmt).c_str());
				fns[index]();
				next_index = index + 1;
			}
			break;
		case '}':
			p++;
			if(*p != '}')
				log_error("invalid format string: unescaped }: \"%s\"\n", quote_fmt(fmt).c_str());
			*os << '}';
			break;
		default:
			*os << *p;
		}
}

YOSYS_NAMESPACE_END
