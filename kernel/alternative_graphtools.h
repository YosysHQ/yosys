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

#ifndef GRAPHTOOLS_H
#define GRAPHTOOLS_H

#include "kernel/yosys.h"
#include "kernel/drivertools.h"
#include "kernel/functional.h"

USING_YOSYS_NAMESPACE
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
			T overflow = factory.gt(b, factory.constant(RTLIL::Const(y_width, b_width)), b_width);
			return factory.mux(lower_b, factory.constant(RTLIL::Const(y_width, new_width)), overflow, new_width);
		}
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
	CellSimplifier(Factory &f) : factory(f) {}
	T handle(IdString cellType, dict<IdString, Const> parameters, dict<IdString, T> inputs)
	{
		int a_width = parameters.at(ID(A_WIDTH), Const(-1)).as_int();
		int b_width = parameters.at(ID(B_WIDTH), Const(-1)).as_int();
		int y_width = parameters.at(ID(Y_WIDTH), Const(-1)).as_int();
		bool a_signed = parameters.at(ID(A_SIGNED), Const(0)).as_bool();
		bool b_signed = parameters.at(ID(B_SIGNED), Const(0)).as_bool();
		if(cellType.in({ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor)})){
			bool is_signed = a_signed && b_signed;
			T a = extend(inputs.at(ID(A)), a_width, y_width, is_signed);
			T b = extend(inputs.at(ID(B)), b_width, y_width, is_signed);
			if(cellType == ID($add))
				return factory.add(a, b, y_width);
			else if(cellType == ID($sub))
				return factory.sub(a, b, y_width);
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
				return extend(factory.eq(a, b, width), 1, y_width, false);
			if(cellType.in({ID($ne), ID($nex)}))
				return extend(factory.ne(a, b, width), 1, y_width, false);
			else if(cellType == ID($lt))
				return extend(is_signed ? factory.gt(b, a, width) : factory.ugt(b, a, width), 1, y_width, false);
			else if(cellType == ID($le))
				return extend(is_signed ? factory.ge(b, a, width) : factory.uge(b, a, width), 1, y_width, false);
			else if(cellType == ID($gt))
				return extend(is_signed ? factory.gt(a, b, width) : factory.ugt(a, b, width), 1, y_width, false);
			else if(cellType == ID($ge))
				return extend(is_signed ? factory.ge(a, b, width) : factory.uge(a, b, width), 1, y_width, false);
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
			return factory.neg(a, y_width);
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
				T sign_b = factory.slice(b, b_width, b_width - 1, 1);
				T shl = logical_shift_left(a, factory.neg(b, b_width), width, b_width);
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
		}else if(cellType == ID($mul)){
		  bool is_signed = a_signed && b_signed;
		  int width = a_width + b_width;
		  T a = extend(inputs.at(ID(A)), a_width, width, is_signed);
		  T b = extend(inputs.at(ID(B)), b_width, width, is_signed);
		  return extend(factory.mul(a, b, width), width, y_width, is_signed);	
		}else if(cellType == ID($div)){
		  bool is_signed = a_signed && b_signed;
		  int width = max(a_width, b_width);
		  T a = extend(inputs.at(ID(A)), a_width, width, is_signed);
		  T b = extend(inputs.at(ID(B)), b_width, width, is_signed);
		  return extend(factory.div(a, b, width), width, y_width, is_signed);  
		}else if(cellType == ID($mod)){
		  bool is_signed = a_signed && b_signed;
		  int width = max(a_width, b_width);
		  T a = extend(inputs.at(ID(A)), a_width, width, is_signed);
		  T b = extend(inputs.at(ID(B)), b_width, width, is_signed);
		  return extend(factory.mod(a, b, width), width, y_width, is_signed);  
		}else{
			log_error("unhandled cell in CellSimplifier %s\n", cellType.c_str());
		}
	}
};


struct Function {
  IdString name;
  int width;
  dict<IdString, Const> parameters;

  Function(IdString name, int width) : name(name), width(width) {}
  Function(IdString name, int width, dict<IdString, Const> parameters) : name(name), width(width), parameters(parameters) {}

  bool operator==(Function const &other) const {
    return name == other.name && parameters == other.parameters && width == other.width;
  }

  unsigned int hash() const {
    return mkhash(name.hash(), parameters.hash());
  }
};

typedef ComputeGraph<Function, int, IdString, IdString> CompleteComputeGraph;

class CompleteComputeGraphFactory {
  CompleteComputeGraph &graph;
  using T = CompleteComputeGraph::Ref;
  static bool is_single_output(IdString type)
  {
    auto it = yosys_celltypes.cell_types.find(type);
    return it != yosys_celltypes.cell_types.end() && it->second.outputs.size() <= 1;
  }
public:
  CompleteComputeGraphFactory(CompleteComputeGraph &g) : graph(g) {}
  T slice(T a, int in_width, int offset, int out_width) {
    assert(offset + out_width <= in_width);
    return graph.add(Function(ID($$slice), out_width, {{ID(offset), offset}}), 0, std::array<T, 1>{a});
  }
  T extend(T a, int in_width, int out_width, bool is_signed) {
    assert(in_width < out_width);
    if(is_signed)
      return graph.add(Function(ID($sign_extend), out_width, {{ID(WIDTH), out_width}}), 0, std::array<T, 1>{a});
    else
      return graph.add(Function(ID($zero_extend), out_width, {{ID(WIDTH), out_width}}), 0, std::array<T, 1>{a});
  }
  T concat(T a, int a_width, T b, int b_width) {
    return graph.add(Function(ID($$concat), a_width + b_width), 0, std::array<T, 2>{a, b});
  }
  T add(T a, T b, int width) { return graph.add(Function(ID($add), width), 0, std::array<T, 2>{a, b}); }
  T sub(T a, T b, int width) { return graph.add(Function(ID($sub), width), 0, std::array<T, 2>{a, b}); }
  T bitwise_and(T a, T b, int width) { return graph.add(Function(ID($and), width), 0, std::array<T, 2>{a, b}); }
  T bitwise_or(T a, T b, int width) { return graph.add(Function(ID($or), width), 0, std::array<T, 2>{a, b}); }
  T bitwise_xor(T a, T b, int width) { return graph.add(Function(ID($xor), width), 0, std::array<T, 2>{a, b}); }
  T bitwise_not(T a, int width) { return graph.add(Function(ID($not), width), 0, std::array<T, 1>{a}); }
  T neg(T a, int width) { return graph.add(Function(ID($neg), width), 0, std::array<T, 1>{a}); }
  T mux(T a, T b, T s, int width) { return graph.add(Function(ID($mux), width), 0, std::array<T, 3>{a, b, s}); }
  T pmux(T a, T b, T s, int width, int) { return graph.add(Function(ID($pmux), width), 0, std::array<T, 3>{a, b, s}); }
  T reduce_and(T a, int) { return graph.add(Function(ID($reduce_and), 1), 0, std::array<T, 1>{a}); }
  T reduce_or(T a, int) { return graph.add(Function(ID($reduce_or), 1), 0, std::array<T, 1>{a}); }
  T reduce_xor(T a, int) { return graph.add(Function(ID($reduce_xor), 1), 0, std::array<T, 1>{a}); }
  T eq(T a, T b, int) { return graph.add(Function(ID($eq), 1), 0, std::array<T, 2>{a, b}); }
  T ne(T a, T b, int) { return graph.add(Function(ID($ne), 1), 0, std::array<T, 2>{a, b}); }
  T gt(T a, T b, int) { return graph.add(Function(ID($gt), 1), 0, std::array<T, 2>{a, b}); }
  T ge(T a, T b, int) { return graph.add(Function(ID($ge), 1), 0, std::array<T, 2>{a, b}); }
  T ugt(T a, T b, int) { return graph.add(Function(ID($ugt), 1), 0, std::array<T, 2>{a, b}); }
  T uge(T a, T b, int) { return graph.add(Function(ID($uge), 1), 0, std::array<T, 2>{a, b}); }
  T logical_shift_left(T a, T b, int y_width, int) { return graph.add(Function(ID($shl), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }
  T logical_shift_right(T a, T b, int y_width, int) { return graph.add(Function(ID($shr), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }
  T arithmetic_shift_right(T a, T b, int y_width, int) { return graph.add(Function(ID($asr), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }
  T mul(T a, T b, int width) { return graph.add(Function(ID($mul), width), 0, std::array<T, 2>{a, b}); }
  T mod(T a, T b, int width) { return graph.add(Function(ID($mod), width), 0, std::array<T, 2>{a, b}); }
  T div(T a, T b, int width) { return graph.add(Function(ID($div), width), 0, std::array<T, 2>{a, b}); }
  
  T constant(RTLIL::Const value) {
    return graph.add(Function(ID($$const), value.size(), {{ID(value), value}}), 0);
  }
  T input(IdString name, int width) { return graph.add(Function(ID($$input), width, {{name, {}}}), 0); }
  T state(IdString name, int width) { return graph.add(Function(ID($$state), width, {{name, {}}}), 0); }
  T cell_output(T cell, IdString type, IdString name, int width) {
    if (is_single_output(type))
      return cell;
    else
      return graph.add(Function(ID($$cell_output), width, {{name, {}}}), 0, std::array<T, 1>{cell});
  }
  T multiple(vector<T> args, int width) {
    return graph.add(Function(ID($$multiple), width), 0, args);
  }
  T undriven(int width) {
    return graph.add(Function(ID($$undriven), width), 0);
  }

  T create_pending(int width) {
    return graph.add(Function(ID($$pending), width), 0);
  }
  void update_pending(T pending, T node) {
    assert(pending.function().name == ID($$pending));
    pending.set_function(Function(ID($$buf), pending.function().width));
    pending.append_arg(node);
  }
  void declare_output(T node, IdString name, int) {
    node.assign_key(name);
  }
  void declare_state(T node, IdString name, int) {
    node.assign_key(name);
  }
  void suggest_name(T node, IdString name) {
    node.sparse_attr() = name;
  }
};

template <class T, class Factory>
class ComputeGraphConstruction {
	std::deque<DriveSpec> queue;
	dict<DriveSpec, T> graph_nodes;
	idict<Cell *> cells;
	DriverMap driver_map;
	Factory& factory;
	CellSimplifier<T, Factory> simplifier;

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
	ComputeGraphConstruction(Factory &f) : factory(f), simplifier(f) {}
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
					dict<IdString, T> connections;
					for(auto const &conn : cell->connections()) {
						if(driver_map.celltypes.cell_input(cell->type, conn.first))
							connections.insert({ conn.first, enqueue(DriveChunkPort(cell, conn)) });
					}
					T node = simplifier.handle(cell->type, cell->parameters, connections);
					factory.update_pending(pending, node);
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

CompleteComputeGraph calculate_compute_graph(RTLIL::Module *module)
{
  CompleteComputeGraph compute_graph;
  CompleteComputeGraphFactory factory(compute_graph);
  ComputeGraphConstruction<CompleteComputeGraph::Ref, CompleteComputeGraphFactory> construction(factory);
  construction.add_module(module);
  construction.process_queue();
  
  // Perform topo sort and detect SCCs
  CompleteComputeGraph::SccAdaptor compute_graph_scc(compute_graph);
  
  bool scc = false;
  std::vector<int> perm;
  topo_sorted_sccs(compute_graph_scc, [&](int *begin, int *end) {
    perm.insert(perm.end(), begin, end);
    if (end > begin + 1)
      {
	log_warning("SCC:");
	for (int *i = begin; i != end; ++i)
	  log(" %d(%s)(%s)", *i, compute_graph[*i].function().name.c_str(), compute_graph[*i].has_sparse_attr() ? compute_graph[*i].sparse_attr().c_str() : "");
	log("\n");
	scc = true;
      }
  }, /* sources_first */ true);
  compute_graph.permute(perm);
  if(scc) log_error("combinational loops, aborting\n");
  
  // Forward $$buf
  std::vector<int> alias;
  perm.clear();
  
  for (int i = 0; i < compute_graph.size(); ++i)
    {
      auto node = compute_graph[i];
      if (node.function().name == ID($$buf) && node.arg(0).index() < i)
	{
	  int target_index = alias[node.arg(0).index()];
	  auto target_node = compute_graph[perm[target_index]];
	  if(!target_node.has_sparse_attr() && node.has_sparse_attr())
	    target_node.sparse_attr() = node.sparse_attr();
	  alias.push_back(target_index);
	}
      else
	{
	  alias.push_back(GetSize(perm));
	  perm.push_back(i);
	}
    }
  compute_graph.permute(perm, alias);
  return compute_graph;
};


YOSYS_NAMESPACE_END

#endif
