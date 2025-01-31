#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Signal cell driver(s), precompute a cell output signal to a cell map
void sigCellDrivers(RTLIL::Design *design, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout,
		    dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin)
{
	if (!design->top_module())
		return;
	if (design->top_module()->cells().size() == 0)
		return;
	for (auto module : design->selected_modules()) {
		SigMap sigmap(module);
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
}

// Assign statements fanin, fanout, traces the lhs2rhs and rhs2lhs sigspecs and precompute maps
void lhs2rhs_rhs2lhs(RTLIL::Design *design, dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> &rhsSig2LhsSig,
		     dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2rhsSig)
{
	for (auto module : design->selected_modules()) {
		SigMap sigmap(module);
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
				if (bit_sig.is_fully_const()) {
					continue;
				}
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
}

struct AnnotateCellFanout : public ScriptPass {
	AnnotateCellFanout() : ScriptPass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
	void script() override {}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		log("Running annotate_cell_fanout pass\n");
		log_flush();
		// Precompute cell output sigspec to cell map
		dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
		dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
		sigCellDrivers(design, sig2CellsInFanout, sig2CellsInFanin);
		// Precompute lhs2rhs and rhs2lhs sigspec map
		dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
		dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> rhsSig2LhsSig;
		lhs2rhs_rhs2lhs(design, rhsSig2LhsSig, lhsSig2RhsSig);

		// Accumulate fanout from cell connections
		dict<RTLIL::SigSpec, int> sigFanout;
		for (auto itrSig : sig2CellsInFanout) {
			SigSpec sigspec = itrSig.first;
			std::set<Cell *> &cells = itrSig.second;
			sigFanout[sigspec] = cells.size();
		}

		// Accumulate fanout from assign stmts connections
		for (auto itrSig : rhsSig2LhsSig) {
			SigSpec sigspec = itrSig.first;
			std::set<RTLIL::SigSpec> &fanout = itrSig.second;
			if (sigFanout.count(sigspec)) {
				sigFanout[sigspec] += fanout.size();
			} else {
				sigFanout[sigspec] = fanout.size();
			}
		}

		// Collect max fanout from all the output bits of a cell
		dict<Cell *, int> cellFanout;
		for (auto itrSig : sigFanout) {
			SigSpec sigspec = itrSig.first;
			int fanout = itrSig.second;
			std::set<Cell *> &cells = sig2CellsInFanin[sigspec];
			for (Cell *cell : cells) {
				if (cellFanout.count(cell)) {
					cellFanout[cell] = std::max(fanout, cellFanout[cell]);
				} else {
					cellFanout[cell] = fanout;
				}
			}
		}

		// Find cells with no fanout info (connected to output ports, or not connected)
		std::set<Cell *> noFanoutInfo;
		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				if (!cellFanout.count(cell)) {
					noFanoutInfo.insert(cell);
				}
			}
		}
		// Set those cells to fanout 1
		for (auto cell : noFanoutInfo) {
			cellFanout[cell] = 1;
		}

		// Add attribute with fanout info to every cell
		for (auto itrCell : cellFanout) {
			Cell *cell = itrCell.first;
			int fanout = itrCell.second;
			cell->set_string_attribute("$FANOUT", std::to_string(fanout));
		}

		log("End annotate_cell_fanout pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
