#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Count the loads on every net and bit, and record which cell drives each. Both whole buses and
// their individual bits are keyed so a driver can be scored on whichever of the two is worse.
// Internal wire-to-wire aliases are not loads, matching how fanoutbuf and report_fanout count.
void countLoads(RTLIL::Module *module, SigMap &sigmap, dict<SigSpec, int> &sigFanout,
		dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin)
{
	for (auto cell : module->selected_cells()) {
		for (auto &conn : cell->connections()) {
			RTLIL::SigSpec actual = conn.second;
			if (cell->output(conn.first)) {
				// Drivers are recorded, not counted: they are what fanout gets scored onto
				sig2CellsInFanin[sigmap(actual)].insert(cell);
				for (int i = 0; i < actual.size(); i++)
					sig2CellsInFanin[sigmap(actual.extract(i, 1))].insert(cell);
			} else {
				// One load per pin, not per cell: a cell reading one net on two pins is two
				// loads. A 1-bit pin's bus and bit key are identical, so let the bit loop
				// below count it and do not add it twice here.
				if (actual.size() != 1)
					sigFanout[sigmap(actual)]++;
				for (int i = 0; i < actual.size(); i++) {
					SigSpec bit_sig = actual.extract(i, 1);
					if (!bit_sig.is_fully_const())
						sigFanout[sigmap(bit_sig)]++;
				}
			}
		}
	}

	// Each module output port bit is one further load on whatever drives it. Counting per port
	// bit rather than per canonical net keeps N ports on one net at N, so a feedthrough net
	// (whose entire fanout is output ports) does not collapse to 1.
	for (Wire *wire : module->wires()) {
		if (!wire->port_output)
			continue;
		for (int i = 0; i < wire->width; i++) {
			SigSpec bit_sig = sigmap(SigSpec(wire, i));
			// A constant-driven output port loads no driver
			if (!bit_sig.is_fully_const())
				sigFanout[bit_sig]++;
		}
	}
}

// Calculate cells and nets fanout
void calculateFanout(RTLIL::Module *module, SigMap &sigmap, dict<Cell *, int> &cellFanout, dict<SigSpec, int> &sigFanout)
{
	dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
	countLoads(module, sigmap, sigFanout, sig2CellsInFanin);

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
struct AnnotateCellFanout : public Pass {
	AnnotateCellFanout() : Pass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
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
