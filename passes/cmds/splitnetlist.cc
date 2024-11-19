#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Recursively traverses backward from a sig, record if a cell was traversed, and push onto the cell's inputs.
// Similarly with assign statements traverses lhs -> rhs
void recordTransFanin(RTLIL::SigSpec &sig, dict<RTLIL::SigSpec, std::set<Cell *> *> &sig2CellsInFanin,
		      dict<RTLIL::SigSpec, RTLIL::SigSpec> &lhsSig2RhsSig, std::set<Cell *> &visitedCells, std::set<RTLIL::SigSpec> &visitedSigSpec)
{
	if (sig.is_fully_const()) {
		return;
	}
	if (visitedSigSpec.count(sig)) {
		return;
	}
	visitedSigSpec.insert(sig);
	if (sig2CellsInFanin.count(sig)) {
		std::set<Cell *> *sigFanin = sig2CellsInFanin[sig];
		for (std::set<Cell *>::iterator it = sigFanin->begin(); it != sigFanin->end(); it++) {
			Cell *cell = *it;
			if (visitedCells.count(cell)) {
				continue;
			}
			visitedCells.insert(cell);
			for (auto &conn : cell->connections()) {
				IdString portName = conn.first;
				RTLIL::SigSpec actual = conn.second;

				if (cell->input(portName)) {
					if (!actual.is_chunk()) {
						for (auto it = actual.chunks().rbegin(); it != actual.chunks().rend(); ++it) {
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
void sigCellDrivers(RTLIL::Design *design, dict<RTLIL::SigSpec, std::set<Cell *> *> &sig2CellsInFanin)
{
	if (!design->top_module())
		return;
	if (design->top_module()->cells().size() == 0)
		return;
	for (auto cell : design->top_module()->cells()) {
		for (auto &conn : cell->connections()) {
			IdString portName = conn.first;
			RTLIL::SigSpec actual = conn.second;
			std::set<Cell *> *newSet;
			if (cell->output(portName)) {
				if (!actual.is_chunk()) {
					for (auto it = actual.chunks().rbegin(); it != actual.chunks().rend(); ++it) {
						RTLIL::SigSpec sub_actual = *it;
						if (sig2CellsInFanin.count(sub_actual)) {
							newSet = sig2CellsInFanin[sub_actual];
						} else {
							newSet = new std::set<Cell *>;
							sig2CellsInFanin[sub_actual] = newSet;
						}
						newSet->insert(cell);
					}
				} else {
					if (sig2CellsInFanin.count(actual)) {
						newSet = sig2CellsInFanin[actual];
					} else {
						newSet = new std::set<Cell *>;
						sig2CellsInFanin[actual] = newSet;
					}
					newSet->insert(cell);
					for (int i = 0; i < actual.size(); i++) {
						SigSpec bit_sig = actual.extract(i, 1);
						if (sig2CellsInFanin.count(bit_sig)) {
							newSet = sig2CellsInFanin[bit_sig];
						} else {
							newSet = new std::set<Cell *>;
							sig2CellsInFanin[bit_sig] = newSet;
						}
						newSet->insert(cell);
					}
				}
			}
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
	    : ScriptPass("splitnetlist", "Splits a netlist into multiple modules using transitive fanin grouping. \
	       The output names that belong in the same logical cluster have to have the same prefix: <prefix>_<name>")
	{
	}
	void script() override {}

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

		// Add buffers for pass-through and connections to constants
		// so we can find cells that can be used by submod
		Pass::call(design, "bufnorm -buf");

		if (debug)
			run_pass("write_rtlil post_buf.rtlil");

		log("Mapping signals to cells\n");
		log_flush();
		// Precompute cell output sigspec to cell map
		dict<RTLIL::SigSpec, std::set<Cell *> *> sig2CellsInFanin;
		sigCellDrivers(design, sig2CellsInFanin);
		log("Mapping assignments\n");
		log_flush();
		// Precompute lhs to rhs sigspec map
		dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
		lhs2rhs(design, lhsSig2RhsSig);
		// Struct representing a cluster
		typedef struct CellsAndSigs {
			std::set<Cell *> visitedCells;
			std::set<RTLIL::SigSpec> visitedSigSpec;
		} CellsAndSigs;
		// Cluster mapped by prefix
		typedef std::map<std::string, CellsAndSigs> CellName_ObjectMap;
		CellName_ObjectMap cellName_ObjectMap;
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
			// Record the visited objects in the corresponding cluster
			CellName_ObjectMap::iterator itr = cellName_ObjectMap.find(std::string(po_prefix));
			if (itr == cellName_ObjectMap.end()) {
				CellsAndSigs components;
				for (auto cell : visitedCells) {
					components.visitedCells.insert(cell);
				}
				for (auto sig : visitedSigSpec) {
					components.visitedSigSpec.insert(sig);
				}
				cellName_ObjectMap.emplace(std::string(po_prefix), components);
			} else {
				CellsAndSigs &components = itr->second;
				for (auto cell : visitedCells) {
					components.visitedCells.insert(cell);
				}
				for (auto sig : visitedSigSpec) {
					components.visitedSigSpec.insert(sig);
				}
			}
		}
		// Create submod attributes for the submod command
		log("Creating submods\n");
		log_flush();
		for (CellName_ObjectMap::iterator itr = cellName_ObjectMap.begin(); itr != cellName_ObjectMap.end(); itr++) {
			if (debug)
				std::cout << "Cluster name: " << itr->first << std::endl;
			CellsAndSigs &components = itr->second;
			for (auto cell : components.visitedCells) {
				cell->set_string_attribute(RTLIL::escape_id("submod"), itr->first);
				if (debug)
					std::cout << "  CELL: " << cell->name.c_str() << std::endl;
			}
		}

		// Execute the submod command
		Pass::call(design, "submod");

		// Remove buffers introduced by bufnorm
		Pass::call(design, "techmap -D SIMLIB_NOCHECKS -map +/simlib.v t:$buf");
		Pass::call(design, "clean");

		log("End splitnetlist pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
