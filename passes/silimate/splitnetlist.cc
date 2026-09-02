#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Recursively traverses backward from a sig, record if a cell was traversed, and push onto the cell's inputs.
// Similarly with assign statements traverses lhs -> rhs
void recordTransFanin(RTLIL::SigSpec &sig, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin,
		      dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig, std::set<Cell *> &visitedCells, std::set<RTLIL::SigSpec> &visitedSigSpec)
{
	if (sig.is_fully_const()) {
		return;
	}
	if (visitedSigSpec.count(sig)) {
		return;
	}
	visitedSigSpec.insert(sig);
	auto fanin_it = sig2CellsInFanin.find(sig);
	if (fanin_it != sig2CellsInFanin.end()) {
		for (Cell *cell : fanin_it->second) {
			if (visitedCells.count(cell)) {
				continue;
			}
			visitedCells.insert(cell);
			for (auto &conn : cell->connections()) {
				IdString portName = conn.first;
				RTLIL::SigSpec actual = conn.second;

				if (cell->input(portName)) {
					if (!actual.is_chunk()) {
						auto chunks = actual.chunks();
						for (auto it = chunks.rbegin(); it != chunks.rend(); ++it) {
							RTLIL::SigSpec sub_actual = *it;
							recordTransFanin(sub_actual, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
						}
					} else {
						recordTransFanin(actual, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
					}
				}
			}
		}
	}
	if (lhsSig2RhsSig.count(sig)) {
		RTLIL::SigSpec rhs = lhsSig2RhsSig[sig];
		recordTransFanin(rhs, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
	}
}

// Signal cell driver(s), precompute a cell output signal to a cell map
void sigCellDrivers(RTLIL::Design *design, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanin)
{
	if (!design->top_module())
		return;
	for (auto cell : design->top_module()->cells()) {
		for (auto &conn : cell->connections()) {
			if (!cell->output(conn.first))
				continue;
			RTLIL::SigSpec actual = conn.second;
			// A concatenation is keyed by each chunk; a plain chunk is keyed both
			// whole and per bit, because recordTransFanin looks the output up
			// either way depending on how its caller sliced it.
			if (!actual.is_chunk()) {
				for (auto &chunk : actual.chunks())
					sig2CellsInFanin[RTLIL::SigSpec(chunk)].insert(cell);
				continue;
			}
			sig2CellsInFanin[actual].insert(cell);
			for (int i = 0; i < actual.size(); i++)
				sig2CellsInFanin[actual.extract(i, 1)].insert(cell);
		}
	}
}

// Assign statements fanin, traces the lhs to rhs sigspecs and precompute a map
void lhs2rhs(RTLIL::Design *design, dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2rhsSig)
{
	if (!design->top_module())
		return;
	if (design->top_module()->connections().size() == 0)
		return;
	for (auto it = design->top_module()->connections().begin(); it != design->top_module()->connections().end(); ++it) {
		RTLIL::SigSpec lhs = it->first;
		RTLIL::SigSpec rhs = it->second;
		if (rhs.is_fully_const()) {
			continue;
		}
		if (!lhs.is_chunk()) {
			// If lhs is not a chunk (leaf) ie: assign {a,b} = ..., then bitblast both lhs and rhs
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
				if (i < rhsBits.size())
					lhsSig2rhsSig[lhsBits[i]] = rhsBits[i];
			}
		} else {
			lhsSig2rhsSig[lhs] = rhs;
		}
	}
}

std::string_view rtrim_until(std::string_view str, char c)
{
	auto pos = str.rfind(c);
	if (pos != std::string_view::npos)
		str = str.substr(0, pos);
	return str;
}

struct SplitNetlist : public ScriptPass {
	SplitNetlist()
	    : ScriptPass("splitnetlist", "split a flat netlist into modules by output-port prefix via transitive fanin")
	{
	}
	void script() override {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splitnetlist\n");
		log("\n");
		log("Split a flat top module into multiple modules by clustering transitive fanin of\n");
		log("output ports that share a name prefix (<prefix>_<name>, e.g. add_Y_0_ -> add).\n");
		log("Each cluster is tagged with \\submod and extracted via the submod command.\n");
		log("\n");
		log("Used in bitblasted training flows after bus_rebuild so OpenSTA sees one module\n");
		log("per logical cell. Modules with processes or memories are not supported.\n");
		log("\n");
	}

	void execute(std::vector<std::string>, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}

		bool debug = false;
		if (std::getenv("DEBUG_SPLITNETLIST")) {
			debug = true;
		}
		log("Running splitnetlist pass\n");
		log_flush();

		if (debug)
			run_pass("write_rtlil post_buf.rtlil");

		log("Mapping signals to cells\n");
		log_flush();
		// Precompute cell output sigspec to cell map
		dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
		sigCellDrivers(design, sig2CellsInFanin);
		log("Mapping assignments\n");
		log_flush();
		// Precompute lhs to rhs sigspec map
		dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
		lhs2rhs(design, lhsSig2RhsSig);
		// Cells of each cluster, mapped by output-port prefix. Only the cells are
		// kept: the signals of a cone are reachable from them, and nothing below
		// reads them.
		std::map<std::string, std::set<Cell *>> cellName_ObjectMap;
		// Record logic cone by output sharing the same prefix
		if (!design->top_module())
			return;
		if (design->top_module()->wires().size() == 0)
			return;
		log("Cells grouping\n");
		log_flush();
		for (auto wire : design->top_module()->wires()) {
			if (!wire->port_output)
				continue;
			std::string output_port_name = wire ? wire->name.c_str() : "";
			if (output_port_name.empty())
				continue;
			// We want to truncate the final _<index>_ part of the string
			// Example: "add_Y_0_"
			// Result:  "add_Y"
			std::string::iterator end = output_port_name.end() - 1;
			if ((*end) == '_') {
				// Last character is an _, it is a bit blasted index
				end--;
				for (; end != output_port_name.begin(); end--) {
					if ((*end) != '_') {
						// Truncate until the next _
						continue;
					} else {
						// Truncate the _
						break;
					}
				}
			}
			std::string no_bitblast_prefix;
			std::copy(output_port_name.begin(), end, std::back_inserter(no_bitblast_prefix));
			// We then truncate the port name, Result: "add"
			std::string_view po_prefix = rtrim_until(std::string_view(no_bitblast_prefix), '_');
			std::set<Cell *> visitedCells;
			std::set<RTLIL::SigSpec> visitedSigSpec;
			RTLIL::SigSpec actual = wire;
			// Visit the output sigspec
			recordTransFanin(actual, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
			// Visit the output sigspec bits
			for (int i = 0; i < actual.size(); i++) {
				SigSpec bit_sig = actual.extract(i, 1);
				recordTransFanin(bit_sig, sig2CellsInFanin, lhsSig2RhsSig, visitedCells, visitedSigSpec);
			}
			// Record the visited cells in the corresponding cluster
			cellName_ObjectMap[std::string(po_prefix)].insert(visitedCells.begin(), visitedCells.end());
		}
		// Create submod attributes for the submod command
		log("Creating submods\n");
		log_flush();
		for (auto &cluster : cellName_ObjectMap) {
			if (debug)
				std::cout << "Cluster name: " << cluster.first << std::endl;
			for (auto cell : cluster.second) {
				cell->set_string_attribute(RTLIL::escape_id("submod"), cluster.first);
				if (debug)
					std::cout << "  CELL: " << cell->name.c_str() << std::endl;
			}
		}

		// Execute the submod command
		Pass::call(design, "submod");

		log("End splitnetlist pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
