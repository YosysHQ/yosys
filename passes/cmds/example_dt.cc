#include "kernel/yosys.h"
#include "kernel/drivertools.h"
#include "kernel/topo_scc.h"
#include "kernel/compute_graph.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN




struct ExampleWorker
{
	DriverMap dm;
	Module *module;

	ExampleWorker(Module *module) : module(module) {
		dm.celltypes.setup();
	}
};

struct ExampleDtPass : public Pass
{
	ExampleDtPass() : Pass("example_dt", "drivertools example") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("TODO: add help message\n");
		log("\n");
    }


	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			ExampleWorker worker(module);
			DriverMap dm;

			struct ExampleFn {
				IdString name;
				dict<IdString, Const> parameters;

				ExampleFn(IdString name) : name(name) {}
				ExampleFn(IdString name, dict<IdString, Const> parameters) : name(name), parameters(parameters) {}

				bool operator==(ExampleFn const &other) const {
					return name == other.name && parameters == other.parameters;
				}

				unsigned int hash() const {
					return mkhash(name.hash(), parameters.hash());
				}
			};

			typedef ComputeGraph<ExampleFn, int, IdString, IdString> ExampleGraph;

			ExampleGraph compute_graph;


			dm.add(module);

			idict<DriveSpec> queue;
			idict<Cell *> cells;

			IntGraph edges;
			std::vector<int> graph_nodes;

			auto enqueue = [&](DriveSpec const &spec) {
				int index = queue(spec);
				if (index == GetSize(graph_nodes))
					graph_nodes.emplace_back(compute_graph.add(ID($pending), index).index());
				//if (index >= GetSize(graph_nodes))
				return compute_graph[graph_nodes[index]];
			};

			for (auto cell : module->cells()) {
				if (cell->type.in(ID($assert), ID($assume), ID($cover), ID($check)))
					enqueue(DriveBitMarker(cells(cell), 0));
			}

			for (auto wire : module->wires()) {
				if (!wire->port_output)
					continue;
				enqueue(DriveChunk(DriveChunkWire(wire, 0, wire->width))).assign_key(wire->name);
			}

			for (int i = 0; i != GetSize(queue); ++i)
			{
				DriveSpec spec = queue[i];
				ExampleGraph::Ref node = compute_graph[i];

				if (spec.chunks().size() > 1) {
					node.set_function(ID($$concat));

					for (auto const &chunk : spec.chunks()) {
						node.append_arg(enqueue(chunk));
					}
				} else if (spec.chunks().size() == 1) {
					DriveChunk chunk = spec.chunks()[0];
					if (chunk.is_wire()) {
						DriveChunkWire wire_chunk = chunk.wire();
						if (wire_chunk.is_whole()) {
							node.sparse_attr() = wire_chunk.wire->name;
							if (wire_chunk.wire->port_input) {
								node.set_function(ExampleFn(ID($$input), {{wire_chunk.wire->name, {}}}));
							} else {
								DriveSpec driver = dm(DriveSpec(wire_chunk));
								node.set_function(ID($$buf));

								node.append_arg(enqueue(driver));
							}
						} else {
							DriveChunkWire whole_wire(wire_chunk.wire, 0, wire_chunk.wire->width);
							node.set_function(ExampleFn(ID($$slice), {{ID(offset), wire_chunk.offset}, {ID(width), wire_chunk.width}}));
							node.append_arg(enqueue(whole_wire));
						}
					} else if (chunk.is_port()) {
						DriveChunkPort port_chunk = chunk.port();
						if (port_chunk.is_whole()) {
							if (dm.celltypes.cell_output(port_chunk.cell->type, port_chunk.port)) {
								if (port_chunk.cell->type.in(ID($dff), ID($ff)))
								{
									Cell *cell = port_chunk.cell;
									node.set_function(ExampleFn(ID($$state), {{cell->name, {}}}));
									for (auto const &conn : cell->connections()) {
										if (!dm.celltypes.cell_input(cell->type, conn.first))
											continue;
										enqueue(DriveChunkPort(cell, conn)).assign_key(cell->name);
									}
								}
								else
								{
									node.set_function(ExampleFn(ID($$cell_output), {{port_chunk.port, {}}}));
									node.append_arg(enqueue(DriveBitMarker(cells(port_chunk.cell), 0)));
								}
							} else {
								node.set_function(ID($$buf));

								DriveSpec driver = dm(DriveSpec(port_chunk));
								node.append_arg(enqueue(driver));
							}

						} else {
							DriveChunkPort whole_port(port_chunk.cell, port_chunk.port, 0, GetSize(port_chunk.cell->connections().at(port_chunk.port)));
							node.set_function(ExampleFn(ID($$slice), {{ID(offset), port_chunk.offset}}));
							node.append_arg(enqueue(whole_port));
						}
					} else if (chunk.is_constant()) {
						node.set_function(ExampleFn(ID($$const), {{ID(value), chunk.constant()}}));

					} else if (chunk.is_multiple()) {
						node.set_function(ID($$multi));
						for (auto const &driver : chunk.multiple().multiple())
							node.append_arg(enqueue(driver));
					} else if (chunk.is_marker()) {
						Cell *cell = cells[chunk.marker().marker];

						node.set_function(ExampleFn(cell->type, cell->parameters));
						for (auto const &conn : cell->connections()) {
							if (!dm.celltypes.cell_input(cell->type, conn.first))
								continue;

							node.append_arg(enqueue(DriveChunkPort(cell, conn)));
						}
					} else if (chunk.is_none()) {
						node.set_function(ID($$undriven));

					} else {
						log_error("unhandled drivespec: %s\n", log_signal(chunk));
						log_abort();
					}
				} else {
					log_abort();
				}
			}


			// Perform topo sort and detect SCCs
			ExampleGraph::SccAdaptor compute_graph_scc(compute_graph);


			std::vector<int> perm;
			TopoSortedSccs(compute_graph_scc, [&](int *begin, int *end) {
				perm.insert(perm.end(), begin, end);
				if (end > begin + 1)
				{
					log_warning("SCC:");
					for (int *i = begin; i != end; ++i)
						log(" %d", *i);
					log("\n");
				}
			}).process_sources().process_all();
			compute_graph.permute(perm);


			// Forward $$buf unless we have a name in the sparse attribute
			std::vector<int> alias;
			perm.clear();

			for (int i = 0; i < compute_graph.size(); ++i)
			{
				if (compute_graph[i].function().name == ID($$buf) && !compute_graph[i].has_sparse_attr() && compute_graph[i].arg(0).index() < i)
				{

					alias.push_back(alias[compute_graph[i].arg(0).index()]);
				}
				else
				{
					alias.push_back(GetSize(perm));
					perm.push_back(i);
				}
			}
			compute_graph.permute(perm, alias);

			// Dump the compute graph
			for (int i = 0; i < compute_graph.size(); ++i)
			{
				auto ref = compute_graph[i];
				log("n%d ", i);
				log("%s", log_id(ref.function().name));
				for (auto const &param : ref.function().parameters)
				{
					if (param.second.empty())
						log("[%s]", log_id(param.first));
					else
						log("[%s=%s]", log_id(param.first), log_const(param.second));
				}
				log("(");

				for (int i = 0, end = ref.size(); i != end; ++i)
				{
					if (i > 0)
						log(", ");
					log("n%d", ref.arg(i).index());
				}
				log(")\n");
				if (ref.has_sparse_attr())
					log("// wire %s\n", log_id(ref.sparse_attr()));
				log("// was #%d %s\n", ref.attr(), log_signal(queue[ref.attr()]));
			}

			for (auto const &key : compute_graph.keys())
			{
				log("return %d as %s \n", key.second, log_id(key.first));
			}
		}
		log("Plugin test passed!\n");
	}
} ExampleDtPass;

PRIVATE_NAMESPACE_END
