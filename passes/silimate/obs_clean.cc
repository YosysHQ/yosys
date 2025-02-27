#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Signal cell driver(s), precompute a cell output signal to a cell map
void sigCellDrivers(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout,
		    dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin)
{
	for (auto cell : module->selected_cells()) {
		for (auto &conn : cell->connections()) {
			IdString portName = conn.first;
			RTLIL::SigSpec actual = conn.second;
			if (cell->output(portName)) {
				sig2CellsInFanin[sigmap(actual)].insert(cell);
				for (int i = 0; i < actual.size(); i++) {
					SigSpec bit_sig = actual.extract(i, 1);
					sig2CellsInFanin[sigmap(bit_sig)].insert(cell);
				}
			} else {
				sig2CellsInFanout[sigmap(actual)].insert(cell);
				for (int i = 0; i < actual.size(); i++) {
					SigSpec bit_sig = actual.extract(i, 1);
					if (!bit_sig.is_fully_const()) {
						sig2CellsInFanout[sigmap(bit_sig)].insert(cell);
					}
				}
			}
		}
	}
}

// Assign statements fanin, fanout, traces the lhs2rhs and rhs2lhs sigspecs and precompute maps
void lhs2rhs_rhs2lhs(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> &rhsSig2LhsSig,
		     dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2rhsSig)
{
	for (auto it = module->connections().begin(); it != module->connections().end(); ++it) {
		RTLIL::SigSpec lhs = it->first;
		RTLIL::SigSpec rhs = it->second;
		if (!lhs.is_chunk()) {
			std::vector<SigSpec> lhsBits;
			for (int i = 0; i < lhs.size(); i++) {
				SigSpec bit_sig = lhs.extract(i, 1);
				lhsBits.push_back(bit_sig);
			}
			std::vector<SigSpec> rhsBits;
			for (int i = 0; i < rhs.size(); i++) {
				SigSpec bit_sig = rhs.extract(i, 1);
				rhsBits.push_back(bit_sig);
			}

			for (uint32_t i = 0; i < lhsBits.size(); i++) {
				if (i < rhsBits.size()) {
					rhsSig2LhsSig[sigmap(rhsBits[i])].insert(sigmap(lhsBits[i]));
					lhsSig2rhsSig[lhsBits[i]] = sigmap(rhsBits[i]);
				}
			}
		} else {
			rhsSig2LhsSig[sigmap(rhs)].insert(sigmap(lhs));
			lhsSig2rhsSig[lhs] = sigmap(rhs);
		}
	}
}

// Collect transitive fanin of a sig
void collectTransitiveFanin(RTLIL::SigSpec &sig, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin,
			    dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig, std::set<Cell *> &visitedCells,
			    std::set<RTLIL::SigSpec> &visitedSigSpec)
{
	if (visitedSigSpec.count(sigmap(sig))) {
		return;
	}
	visitedSigSpec.insert(sigmap(sig));

	if (sig2CellsInFanin.count(sigmap(sig))) {
		for (Cell *cell : sig2CellsInFanin[sigmap(sig)]) {
			if (visitedCells.count(cell)) {
				continue;
			}
			visitedCells.insert(cell);
			for (auto &conn : cell->connections()) {
				IdString portName = conn.first;
				RTLIL::SigSpec actual = conn.second;
				if (cell->input(portName)) {
					collectTransitiveFanin(actual, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
					for (int i = 0; i < actual.size(); i++) {
						SigSpec bit_sig = actual.extract(i, 1);
						collectTransitiveFanin(bit_sig, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells,
								       visitedSigSpec);
					}
				}
			}
		}
	}
	if (lhsSig2RhsSig.count(sigmap(sig))) {
		RTLIL::SigSpec rhs = lhsSig2RhsSig[sigmap(sig)];
		collectTransitiveFanin(rhs, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < rhs.size(); i++) {
			SigSpec bit_sig = rhs.extract(i, 1);
			collectTransitiveFanin(bit_sig, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}
}

// Only keep the cells and wires that are visited using the transitive fanin reached from output ports or keep signals
void observabilityClean(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin,
			dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig, bool unused_wires, bool unused_assigns, bool debug)
{
	if (module->get_bool_attribute(ID::keep))
		return;
	std::set<Cell *> visitedCells;
	std::set<RTLIL::SigSpec> visitedSigSpec;
	if (debug) {
		log("Collecting cell transitive fanin\n");
		log_flush();
	}
	// Collect observable logic (connected to one output)
	// By cells
	for (auto elt : sig2CellsInFanin) {
		RTLIL::SigSpec po = elt.first;
		if ((!po.size()) || (!po[0].is_wire())) {
			// Can't perform the analysis correctly.
			log_warning("Module %s contains some logic that prevents obs_clean analysis\n", module->name.c_str());
			log_flush();
			return;
		}
		RTLIL::Wire *w = po[0].wire;
		if (w && (!w->port_output) && (!w->get_bool_attribute(ID::keep))) {
			continue;
		}
		RTLIL::SigSpec spo = sigmap(po);
		collectTransitiveFanin(spo, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < po.size(); i++) {
			SigSpec bit_sig = po.extract(i, 1);
			bit_sig = sigmap(bit_sig);
			collectTransitiveFanin(bit_sig, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}

	if (debug) {
		log("Collecting assign transitive fanin\n");
		log_flush();
	}
	// By assigns
	for (auto elt : lhsSig2RhsSig) {
		RTLIL::SigSpec po = elt.first;
		if ((!po.size()) || (!po[0].is_wire())) {
			// Can't perform the analysis correctly.
			log_warning("Module %s contains some logic that prevents obs_clean analysis\n", module->name.c_str());
			log_flush();
			return;
		}
		RTLIL::Wire *w = po[0].wire;
		if (w && (!w->port_output) && (!w->get_bool_attribute(ID::keep))) {
			continue;
		}
		RTLIL::SigSpec spo = sigmap(po);
		collectTransitiveFanin(spo, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < po.size(); i++) {
			SigSpec bit_sig = po.extract(i, 1);
			bit_sig = sigmap(bit_sig);
			collectTransitiveFanin(bit_sig, sigmap, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}

	if (unused_assigns) {
		// Remove unused assign stmts
		if (debug) {
			log("Removing unused assign\n");
			log_flush();
		}
		std::vector<RTLIL::SigSig> newConnections;
		for (auto it = module->connections().begin(); it != module->connections().end(); ++it) {
			RTLIL::SigSpec lhs = it->first;
			if (visitedSigSpec.count(sigmap(lhs))) {
				newConnections.push_back(*it);
			} else {
				for (int i = 0; i < lhs.size(); i++) {
					SigSpec bit_sig = lhs.extract(i, 1);
					if (visitedSigSpec.count(sigmap(bit_sig))) {
						newConnections.push_back(*it);
						break;
					}
				}
			}
		}

		module->connections_.clear();
		for (auto conn : newConnections) {
			module->connect(conn);
		}
	}

	if (unused_wires) {
		// Remove unused wires
		if (debug) {
			log("Removing unused wires\n");
			log_flush();
		}
		// TODO: This impacts equiv_opt ability to perform equivalence checking
		pool<RTLIL::Wire *> wiresToRemove;
		for (auto wire : module->wires()) {
			RTLIL::SigSpec sig = wire;
			if (visitedSigSpec.count(sigmap(sig))) {
				continue;
			}
			bool bitVisited = false;
			for (int i = 0; i < sig.size(); i++) {
				SigSpec bit_sig = sig.extract(i, 1);
				if (visitedSigSpec.count(bit_sig)) {
					bitVisited = true;
					break;
				}
			}
			if (bitVisited)
				continue;
			if (wire->port_id) {
				continue;
			}
			if (wire->get_bool_attribute(ID::keep))
				continue;
			wiresToRemove.insert(wire);
		}

		module->remove(wiresToRemove);
	}

	// Remove unused cells
	if (debug) {
		log("Removing unused cells\n");
		log_flush();
	}
	std::set<Cell *> cellsToRemove;
	for (auto cell : module->cells()) {
		if (visitedCells.count(cell)) {
			continue;
		}
		if (cell->has_keep_attr())
			continue;
		cellsToRemove.insert(cell);
	}

	for (auto cell : cellsToRemove) {
		module->remove(cell);
	}
}

struct ObsClean : public ScriptPass {
	ObsClean() : ScriptPass("obs_clean", "Observability-based cleanup") {}
	void script() override {}
	void help() override
	{
		log("\n");
		log("    obs_clean [options] [selection]\n");
		log("\n");
		log("This pass performs an obversability-based logic removal.\n");
		log("\n");
		log("    -wires\n");
		log("        Also removes dangling wires. This option prevents formal verifciation at this time.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool unused_wires = false;
		bool unused_assigns = false;
		bool debug = false;
		if (std::getenv("DEBUG_OBS_CLEAN")) {
			debug = true;
		}
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-wires") {
				unused_wires = true;
				continue;
			}
			if (args[argidx] == "-assigns") {
				unused_assigns = true;
				continue;
			}
			if (args[argidx] == "-debug") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		log("Running obs_clean pass\n");
		log_flush();
		for (auto module : design->selected_modules()) {
			// We cannot safely perform this analysis when processes or memories are present
			if (module->has_processes_warn())
				continue;
			if (module->has_memories_warn())
				continue;
			if (debug) {
				log("Processing module: %s\n", module->name.c_str());
				log_flush();
			}
			SigMap sigmap(module);
			// Precompute cell output sigspec to cell map
			if (debug) {
				log("Collecting cell info\n");
				log_flush();
			}
			dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
			dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
			sigCellDrivers(module, sigmap, sig2CellsInFanout, sig2CellsInFanin);
			// Precompute lhs2rhs and rhs2lhs sigspec map
			if (debug) {
				log("Collecting assign info\n");
				log_flush();
			}
			dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
			dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> rhsSig2LhsSig;
			lhs2rhs_rhs2lhs(module, sigmap, rhsSig2LhsSig, lhsSig2RhsSig);
			// Actual cleanup
			observabilityClean(module, sigmap, sig2CellsInFanin, lhsSig2RhsSig, unused_wires, unused_assigns, debug);
		}
		log("End obs_clean pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
