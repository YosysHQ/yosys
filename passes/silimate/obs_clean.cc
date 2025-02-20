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
				sig2CellsInFanin[actual].insert(cell);
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
				lhsSig2rhsSig[sigmap(lhsBits[i])] = sigmap(rhsBits[i]);
			}
		}
	}
}

// Collect transitive fanin of a sig
void collectTransitiveFanin(RTLIL::SigSpec &sig, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin,
			    dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig, std::set<Cell *> &visitedCells,
			    std::set<RTLIL::SigSpec> &visitedSigSpec)
{
	if (visitedSigSpec.count(sig)) {
		return;
	}
	visitedSigSpec.insert(sig);

	if (sig2CellsInFanin.count(sig)) {
		for (Cell *cell : sig2CellsInFanin[sig]) {
			if (visitedCells.count(cell)) {
				continue;
			}
			visitedCells.insert(cell);
			for (auto &conn : cell->connections()) {
				IdString portName = conn.first;
				RTLIL::SigSpec actual = conn.second;
				if (cell->input(portName)) {
					collectTransitiveFanin(actual, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
					for (int i = 0; i < actual.size(); i++) {
						SigSpec bit_sig = actual.extract(i, 1);
						collectTransitiveFanin(bit_sig, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
					}
				}
			}
		}
	}
	if (lhsSig2RhsSig.count(sig)) {
		RTLIL::SigSpec rhs = lhsSig2RhsSig[sig];
		collectTransitiveFanin(rhs, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < rhs.size(); i++) {
			SigSpec bit_sig = rhs.extract(i, 1);
			collectTransitiveFanin(bit_sig, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}
}

// Only keep the cells and wires that are visited using the transitive fanin reached from output ports
void observabilityClean(RTLIL::Module *module, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin,
			dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig)
{
	if (module->get_bool_attribute(ID::keep))
		return;
	std::set<Cell *> visitedCells;
	std::set<RTLIL::SigSpec> visitedSigSpec;

	for (auto elt : sig2CellsInFanin) {
		RTLIL::SigSpec po = elt.first;
		RTLIL::Wire *w = po[0].wire;
		if (w && !w->port_output) {
			continue;
		}
		collectTransitiveFanin(po, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < po.size(); i++) {
			SigSpec bit_sig = po.extract(i, 1);
			collectTransitiveFanin(bit_sig, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}

	for (auto elt : lhsSig2RhsSig) {
		RTLIL::SigSpec po = elt.first;
		RTLIL::Wire *w = po[0].wire;
		if (w && !w->port_output) {
			continue;
		}
		collectTransitiveFanin(po, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		for (int i = 0; i < po.size(); i++) {
			SigSpec bit_sig = po.extract(i, 1);
			collectTransitiveFanin(bit_sig, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
		}
	}

	pool<RTLIL::SigSig> newConnections;
	for (auto it = module->connections().begin(); it != module->connections().end(); ++it) {
		RTLIL::SigSpec lhs = it->first;
		if (visitedSigSpec.count(lhs)) {
			newConnections.insert(*it);
		} else {
			for (int i = 0; i < lhs.size(); i++) {
				SigSpec bit_sig = lhs.extract(i, 1);
				if (visitedSigSpec.count(bit_sig)) {
					newConnections.insert(*it);
					break;
				}
			}
		}
	}

	module->connections_.clear();
	for (auto conn : newConnections) {
		module->connect(conn);
	}

	pool<RTLIL::Wire *> wiresToRemove;
	for (auto wire : module->wires()) {
		RTLIL::SigSpec sig = wire;
		if (visitedSigSpec.count(sig)) {
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

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		log("Running obs_clean pass\n");
		log_flush();
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			if (module->has_memories_warn())
				continue;
			SigMap sigmap(module);
			// Precompute cell output sigspec to cell map
			dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
			dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
			sigCellDrivers(module, sigmap, sig2CellsInFanout, sig2CellsInFanin);
			// Precompute lhs2rhs and rhs2lhs sigspec map
			dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
			dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> rhsSig2LhsSig;
			lhs2rhs_rhs2lhs(module, sigmap, rhsSig2LhsSig, lhsSig2RhsSig);
			// Actual cleanup
			observabilityClean(module, sig2CellsInFanin, lhsSig2RhsSig);
		}
		log("End obs_clean pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
