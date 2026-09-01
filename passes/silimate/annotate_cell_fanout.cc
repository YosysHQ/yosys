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

// Record one load per module output port bit, keyed by the sigmapped bit driving it. Port bits
// are stored un-sigmapped: SigMap folds every `connect` alias onto one canonical bit, so a set
// of sigmapped bits collapses N output ports on a net into one entry (this is what made a
// feedthrough net, whose whole fanout is output ports, come out as fanout 1). Internal
// wire-to-wire aliases are not loads, matching how fanoutbuf and report_fanout count.
void outputPortFanout(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> &sig2SigsInFanout)
{
	for (Wire *wire : module->wires()) {
		if (!wire->port_output)
			continue;
		for (int i = 0; i < wire->width; i++) {
			SigSpec bit_sig(wire, i);
			// A constant-driven output port loads no driver
			if (sigmap(bit_sig).is_fully_const())
				continue;
			sig2SigsInFanout[sigmap(bit_sig)].insert(bit_sig);
		}
	}
}

// Calculate cells and nets fanout
void calculateFanout(RTLIL::Module *module, SigMap &sigmap, dict<Cell *, int> &cellFanout, dict<SigSpec, int> &sigFanout)
{
	dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout, sig2CellsInFanin;
	dict<RTLIL::SigSpec, std::set<SigSpec>> sig2SigsInFanout;
	// Precompute cell output sigspec to cell map
	sigCellDrivers(module, sigmap, sig2CellsInFanout, sig2CellsInFanin);
	// Precompute the output port bits loading each net
	outputPortFanout(module, sigmap, sig2SigsInFanout);

	// Accumulate fanout from cell connections, then from output port loads
	for (auto &itrSig : sig2CellsInFanout)
		sigFanout[itrSig.first] = itrSig.second.size();
	for (auto &itrSig : sig2SigsInFanout)
		sigFanout[itrSig.first] += itrSig.second.size();

	// A cell's fanout is that of its most loaded output net or bit
	for (auto &itrSig : sigFanout)
		for (Cell *cell : sig2CellsInFanin[itrSig.first])
			cellFanout[cell] = std::max(itrSig.second, cellFanout.at(cell, 0));

	// Cells with no fanout info (dangling, or driving only constants) count as 1
	for (auto cell : module->selected_cells())
		if (!cellFanout.count(cell))
			cellFanout[cell] = 1;

	// An input port's fanout is that of its most loaded bit when the whole net has no loads
	for (Wire *wire : module->wires()) {
		if (!wire->port_input)
			continue;
		SigSpec inp = sigmap(wire);
		if (sigFanout[inp] != 0)
			continue;
		int max = 0;
		for (int i = 0; i < inp.size(); i++)
			max = std::max(max, sigFanout[inp.extract(i, 1)]);
		sigFanout[inp] = max;
	}
}

// Annotate cell and input port fanout as a $FANOUT attribute
struct AnnotateCellFanout : public ScriptPass {
	AnnotateCellFanout() : ScriptPass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
	void script() override {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    annotate_cell_fanout [selection]\n");
		log("\n");
		log("Annotate each cell and module input port with a $FANOUT attribute holding the\n");
		log("number of loads on its most loaded output net, counting both cell input pins\n");
		log("and module output ports. Improves area/timing predictions on high-fanout\n");
		log("designs. Run fanoutbuf first to actually limit fanout.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ANNOTATE_CELL_FANOUT pass (annotate cell fanout).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);
			dict<Cell *, int> cellFanout;
			dict<SigSpec, int> sigFanout;
			calculateFanout(module, sigmap, cellFanout, sigFanout);

			for (auto &itrCell : cellFanout)
				itrCell.first->set_string_attribute("$FANOUT", std::to_string(itrCell.second));
			for (Wire *wire : module->wires())
				if (wire->port_input)
					wire->set_string_attribute("$FANOUT", std::to_string(sigFanout[sigmap(wire)]));
		}
	}
} AnnotateCellFanout;

PRIVATE_NAMESPACE_END
