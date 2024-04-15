#include "kernel/yosys.h"
#include "kernel/drivertools.h"
#include "kernel/topo_scc.h"

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
    }


	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			ExampleWorker worker(module);
			DriverMap dm;

			dm.add(module);

			idict<DriveSpec> queue;
			idict<Cell *> cells;

			IntGraph edges;


			for (auto cell : module->cells()) {
				if (cell->type.in(ID($assert), ID($assume), ID($cover), ID($check)))
					queue(DriveBitMarker(cells(cell), 0));
			}

			for (auto wire : module->wires()) {
				if (!wire->port_output)
					continue;
				queue(DriveChunk(DriveChunkWire(wire, 0, wire->width)));
			}

#define emit log
// #define emit(X...) do {} while (false)

			for (int i = 0; i != GetSize(queue); ++i)
			{
				emit("n%d: ", i);
				DriveSpec spec = queue[i];
				if (spec.chunks().size() > 1) {
					emit("concat %s <-\n", log_signal(spec));
					for (auto const &chunk : spec.chunks()) {
						emit("  * %s\n", log_signal(chunk));
						edges.add_edge(i, queue(chunk));
					}
				} else if (spec.chunks().size() == 1) {
					DriveChunk chunk = spec.chunks()[0];
					if (chunk.is_wire()) {
						DriveChunkWire wire_chunk = chunk.wire();
						if (wire_chunk.is_whole()) {
							if (wire_chunk.wire->port_input) {
								emit("input %s\n", log_signal(spec));
							} else {
								DriveSpec driver = dm(DriveSpec(wire_chunk));
								edges.add_edge(i, queue(driver));
								emit("wire driver %s <- %s\n", log_signal(spec), log_signal(driver));
							}
						} else {
							DriveChunkWire whole_wire(wire_chunk.wire, 0, wire_chunk.width);
							edges.add_edge(i, queue(whole_wire));
							emit("wire slice %s <- %s\n", log_signal(spec), log_signal(DriveSpec(whole_wire)));
						}
					} else if (chunk.is_port()) {
						DriveChunkPort port_chunk = chunk.port();
						if (port_chunk.is_whole()) {
							if (dm.celltypes.cell_output(port_chunk.cell->type, port_chunk.port)) {
								int cell_marker = queue(DriveBitMarker(cells(port_chunk.cell), 0));
								if (!port_chunk.cell->type.in(ID($dff), ID($ff)))
									edges.add_edge(i, cell_marker);
								emit("cell output %s %s\n", log_id(port_chunk.cell), log_id(port_chunk.port));
							} else {
								DriveSpec driver = dm(DriveSpec(port_chunk));
								edges.add_edge(i, queue(driver));
								emit("cell port driver %s <- %s\n", log_signal(spec), log_signal(driver));
							}

						} else {
							DriveChunkPort whole_port(port_chunk.cell, port_chunk.port, 0, GetSize(port_chunk.cell->connections().at(port_chunk.port)));
							edges.add_edge(i, queue(whole_port));
							emit("port slice %s <- %s\n", log_signal(spec), log_signal(DriveSpec(whole_port)));
						}
					} else if (chunk.is_constant()) {
						emit("constant %s <- %s\n", log_signal(spec), log_const(chunk.constant()));
					} else if (chunk.is_marker()) {
						Cell *cell = cells[chunk.marker().marker];
						emit("cell %s %s\n", log_id(cell->type), log_id(cell));
						for (auto const &conn : cell->connections()) {
							if (!dm.celltypes.cell_input(cell->type, conn.first))
								continue;
							emit("  * %s <- %s\n", log_id(conn.first), log_signal(conn.second));
							edges.add_edge(i, queue(DriveChunkPort(cell, conn)));
						}
					} else {
						log_abort();
					}
				} else {
					log_abort();
				}
			}

			topo_sorted_sccs(edges, [&](int *begin, int *end) {
				emit("scc:");
				for (int *i = begin; i != end; ++i)
					emit(" n%d", *i);
				emit("\n");
			});

		}
		log("Plugin test passed!\n");
	}
} ExampleDtPass;

PRIVATE_NAMESPACE_END
