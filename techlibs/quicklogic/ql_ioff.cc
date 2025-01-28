#include "kernel/log.h"
#include "kernel/modtools.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QlIoffPass : public Pass {
	QlIoffPass() : Pass("ql_ioff", "Infer I/O FFs for qlf_k6n10f architecture") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_ioff [selection]\n");
		log("\n");
		log("This pass promotes qlf_k6n10f registers directly connected to a top-level I/O\n");
		log("port to I/O FFs.\n");
		log("\n");
	}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		log_header(design, "Executing QL_IOFF pass.\n");

		ModWalker modwalker(design);
		Module *module = design->top_module();
		if (!module)
			return;
		modwalker.setup(module);
		pool<RTLIL::Cell *> cells_to_replace;
		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID(dffsre), ID(sdffsre))) {
				bool e_const = cell->getPort(ID::E).is_fully_ones();
				bool r_const = cell->getPort(ID::R).is_fully_ones();
				bool s_const = cell->getPort(ID::S).is_fully_ones();

				if (!(e_const && r_const && s_const))
					continue;

				SigSpec d = cell->getPort(ID::D);
				if (GetSize(d) != 1) continue;
				SigBit d_sig = modwalker.sigmap(d[0]);
				if (d_sig.is_wire() && d_sig.wire->port_input) {
					log_debug("Cell %s is potentially eligible for promotion to input IOFF.\n", cell->name.c_str());
					// check that d_sig has no other consumers
					pool<ModWalker::PortBit> portbits;
					modwalker.get_consumers(portbits, d_sig);
					if (GetSize(portbits) > 1) {
						log_debug("not promoting: d_sig has other consumers\n");
						continue;
					}
					cells_to_replace.insert(cell);
					continue; // no need to check Q if we already put it on the list
				}
				SigSpec q = cell->getPort(ID::Q);
				if (GetSize(q) != 1) continue;
				SigBit q_sig = modwalker.sigmap(q[0]);
				if (q_sig.is_wire() && q_sig.wire->port_output) {
					log_debug("Cell %s is potentially eligible for promotion to output IOFF.\n", cell->name.c_str());
					// check that q_sig has no other consumers
					pool<ModWalker::PortBit> portbits;
					modwalker.get_consumers(portbits, q_sig);
					if (GetSize(portbits) > 0) {
						log_debug("not promoting: q_sig has other consumers\n");
						continue;
					}
					cells_to_replace.insert(cell);
				}
			}
		}

		for (auto cell : cells_to_replace) {
			log("Promoting register %s to IOFF.\n", log_signal(cell->getPort(ID::Q)));
			cell->type = ID(dff);
			cell->unsetPort(ID::E);
			cell->unsetPort(ID::R);
			cell->unsetPort(ID::S);
		}
	}
} QlIoffPass;

PRIVATE_NAMESPACE_END
