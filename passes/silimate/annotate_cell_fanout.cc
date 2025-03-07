#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Return substring up to a delimiter or full string if not found
std::string substringuntil(const std::string &str, char delimiter)
{
	size_t pos = str.find(delimiter);
	if (pos != std::string::npos) {
		return str.substr(0, pos);
	} else {
		return str;
	}
}

// Generate a meaningful name for a sigspec, uniquify if necessary
RTLIL::IdString generateSigSpecName(Module *module, const RTLIL::SigSpec &sigspec, bool makeUnique = false, std::string postfix = "",
				    bool cellName = false)
{
	if (sigspec.empty()) {
		return RTLIL::IdString(); // Empty SigSpec, return empty IdString
	}
	std::stringstream ss;
	if (sigspec.is_wire()) {
		// Handle wires
		ss << sigspec.as_wire()->name.str();
	} else if (sigspec.size() == 1 && sigspec[0].wire) {
		// Handle single-bit SigSpecs
		ss << sigspec[0].wire->name.str();
		if (sigspec[0].wire->width != 1) {
			ss << "[" << sigspec[0].offset << "]";
		}
	} else if (!sigspec.is_chunk()) {
		// Handle vector of chunks
		int max = 0;
		int min = INT_MAX;
		RTLIL::Wire *parent_wire = sigspec[0].wire;
		int width = 0;
		for (SigChunk chunk : sigspec.chunks()) {
			width += chunk.width;
			max = std::max(max, chunk.offset);
			min = std::min(min, chunk.offset);
		}
		if (max == 0) {
			max = width - 1;
		}
		if (parent_wire) {
			if (max != min) {
				ss << substringuntil(parent_wire->name.str(), '[') << "[" << max << ":" << min << "]";
			} else {
				ss << parent_wire->name.str();
			}
		} else {
			ss << "\\sigspec_[" << max << ":" << min << "]";
		}
	}
	ss << postfix;
	if (makeUnique) {
		RTLIL::IdString base_name = RTLIL::IdString(ss.str());
		// Ensure uniqueness
		int counter = 0;
		if (cellName) {
			while (module->cells_.count(RTLIL::IdString(ss.str()))) {
				ss.str("");
				ss << base_name.str() << "_" << counter++;
			}
		} else {
			while (module->wires_.count(RTLIL::IdString(ss.str()))) {
				ss.str("");
				ss << base_name.str() << "_" << counter++;
			}
		}
	}
	return RTLIL::IdString(ss.str());
}

// Collect fanout cells of a given sig, collects all bits connections
void getFanout(dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout, SigMap &sigmap, SigSpec sig, std::set<Cell *> &fanoutcells)
{
	fanoutcells = sig2CellsInFanout[sig];
	for (int i = 0; i < sig.size(); i++) {
		SigSpec bit_sig = sig.extract(i, 1);
		for (Cell *c : sig2CellsInFanout[sigmap(bit_sig)]) {
			fanoutcells.insert(c);
		}
	}
}

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

// Returns the parent wire of a sigspec
RTLIL::Wire *getParentWire(const RTLIL::SigSpec &sigspec)
{
	if (sigspec.empty()) {
		return nullptr; // Empty SigSpec, no parent wire
	}
	// Get the first SigBit
	const RTLIL::SigBit &first_bit = sigspec[0];
	// Return the parent wire
	return first_bit.wire;
}

// Find if a signal is used in another (One level)
bool isSigSpecUsedIn(SigSpec &haystack, SigMap &sigmap, SigSpec &needle)
{
	bool match = false;
	// Input chunk is one of the cell's outputs, its a match
	for (SigChunk chunk_a : haystack.chunks()) {
		if (sigmap(SigSpec(chunk_a)) == sigmap(needle)) {
			match = true;
		} else {
			for (SigChunk chunk_c : needle.chunks()) {
				if (sigmap(SigSpec(chunk_a)) == sigmap(SigSpec(chunk_c))) {
					match = true;
					break;
				}
			}
		}
		if (match)
			break;
	}
	return match;
}

// Remove a buffer and fix the fanout connections to use the buffer's input
void removeBuffer(Module *module, SigMap &sigmap, std::set<Cell *> &fanoutcells, std::map<Cell *, Wire *> &insertedBuffers, Cell *buffer, bool debug)
{
	if (debug)
		std::cout << "Buffer with fanout 1: " << buffer->name.c_str() << std::endl;
	RTLIL::SigSpec bufferInSig = buffer->getPort(ID::A);
	RTLIL::SigSpec bufferOutSig = buffer->getPort(ID::Y);
	// Find which cell use that buffer's output and reconnect its input to the former cell (buffer's input)
	for (Cell *c : fanoutcells) {
		bool reconnected = false;
		if (debug)
			std::cout << "  Cell in its fanout: " << c->name.c_str() << std::endl;
		for (auto &conn : c->connections()) {
			IdString portName = conn.first;
			RTLIL::SigSpec actual = conn.second;
			if (c->input(portName)) {
				if (actual.is_chunk()) {
					// Input is a chunk
					if (bufferOutSig == sigmap(actual)) {
						// Input is one of the cell's outputs, its a match
						if (debug)
							std::cout << "   Replace: " << getParentWire(bufferOutSig)->name.c_str() << " by "
								  << getParentWire(bufferInSig)->name.c_str() << std::endl;
						// Override cell's input with original buffer's input
						c->setPort(portName, bufferInSig);
						reconnected = true;
						break;
					}
				} else {
					// Input is a vector of chunks
					if (isSigSpecUsedIn(actual, sigmap, bufferOutSig)) {
						std::vector<RTLIL::SigChunk> newChunks;
						for (SigChunk chunk : actual.chunks()) {
							if (sigmap(SigSpec(chunk)) == sigmap(bufferOutSig)) {
								if (debug)
									std::cout << "    Replace: " << getParentWire(bufferOutSig)->name.c_str()
										  << " by " << getParentWire(bufferInSig)->name.c_str() << std::endl;
								newChunks.push_back(bufferInSig.as_chunk());
							} else {
								newChunks.push_back(chunk);
							}
						}
						c->setPort(portName, newChunks);
						reconnected = true;
						break;
					}
				}
			}
		}
		if (reconnected)
			break;
	}
	// Delete the now unsused buffer and it's output signal
	auto itr = insertedBuffers.find(buffer);
	insertedBuffers.erase(itr);
	module->remove(buffer);
	module->remove({bufferOutSig.as_wire()});
}

// Returns the first output (sigmaped sigspec) of a cell
RTLIL::SigSpec getCellOutputSigSpec(Cell *cell, SigMap &sigmap)
{
	RTLIL::SigSpec cellOutSig;
	for (auto &conn : cell->connections()) {
		IdString portName = conn.first;
		RTLIL::SigSpec actual = conn.second;
		if (cell->output(portName)) {
			cellOutSig = sigmap(actual);
			break;
		}
	}
	return cellOutSig;
}

// Get new output signal for a given signal, used all datastructures with change to buffer
SigSpec updateToBuffer(Module *module, std::map<SigSpec, int> &bufferIndexes,
		       std::map<RTLIL::SigSpec, std::vector<std::pair<RTLIL::SigSpec, Cell *>>> &buffer_outputs,
		       dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout, std::map<Cell *, int> &bufferActualFanout,
		       std::map<SigSpec, SigSpec> &usedBuffers, int max_output_per_buffer, Cell *fanoutcell, SigSpec sigToReplace, bool debug)
{
	if (debug)
		std::cout << "  CHUNK, indexCurrentBuffer: " << bufferIndexes[sigToReplace] << " buffer_outputs "
			  << buffer_outputs[sigToReplace].size() << std::endl;
	// Reuse cached result for a given cell;
	std::map<SigSpec, SigSpec>::iterator itrBuffer = usedBuffers.find(sigToReplace);
	if (itrBuffer != usedBuffers.end()) {
		if (debug)
			std::cout << "REUSE CACHE:" << fanoutcell->name.c_str() << " SIG: " << generateSigSpecName(module, sigToReplace).c_str()
				  << std::endl;
		return itrBuffer->second;
	}

	// Retrieve the buffer information for that cell's chunk
	std::vector<std::pair<RTLIL::SigSpec, Cell *>> &buf_info_vec = buffer_outputs[sigToReplace];
	// Retrieve which buffer is getting filled
	int bufferIndex = bufferIndexes[sigToReplace];
	std::pair<RTLIL::SigSpec, Cell *> &buf_info = buf_info_vec[bufferIndex];
	SigSpec newSig = buf_info.first;
	Cell *newBuf = buf_info.second;
	// Keep track of fanout map information for recursive calls
	sig2CellsInFanout[newSig].insert(fanoutcell);
	// Increment buffer capacity
	bufferActualFanout[newBuf]++;
	if (debug)
		std::cout << "   USE: " << newBuf->name.c_str() << " fanout: " << bufferActualFanout[newBuf] << std::endl;
	// If we reached capacity for a given buffer, move to the next buffer
	if (bufferActualFanout[newBuf] >= max_output_per_buffer) {
		if (debug)
			std::cout << "  REACHED MAX" << std::endl;
		if (int(buffer_outputs[sigToReplace].size() - 1) > bufferIndex) {
			bufferIndexes[sigToReplace]++;
			if (debug)
				std::cout << "  NEXT BUFFER" << std::endl;
		}
	}
	// Cache result
	if (debug)
		std::cout << "CACHE:" << fanoutcell->name.c_str() << " SIG: " << generateSigSpecName(module, sigToReplace).c_str() << " BY "
			  << generateSigSpecName(module, newSig).c_str() << std::endl;
	usedBuffers.emplace(sigToReplace, newSig);

	// Return buffer's output
	return newSig;
}

// For a given cell with fanout exceeding the limit,
//  - create an array of buffers per cell output chunk (2 dimentions array of buffers)
//  - connect cell chunk to corresponding buffers
//  - reconnected cells in the fanout using the chunk to the newly created buffer
//  - when a buffer reaches capacity, switch to the next buffer
// The capacity of the buffers might be larger than the limit in a given pass,
// Recursion is used until all buffers capacity is under or at the limit.
void fixfanout(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout,
	       std::map<Cell *, Wire *> &insertedBuffers, SigSpec sigToBuffer, int fanout, int limit, bool debug)
{
	if (sigToBuffer.is_fully_const()) {
		return;
	}
	std::string signame = generateSigSpecName(module, sigToBuffer).c_str();
	if (fanout <= limit) {
		if (debug) {
			std::cout << "Nothing to do for: " << signame << std::endl;
			std::cout << "Fanout: " << fanout << std::endl;
		}
		return; // No need to insert buffers
	} else {
		if (debug) {
			std::cout << "Something to do for: " << signame << std::endl;
			std::cout << "Fanout: " << fanout << std::endl;
		}
	}
	// The number of buffers inserted: NbBuffers = Min( Ceil( Fanout / Limit), Limit)
	// By definition, we cannot insert more buffers than the limit (Use of the Min function),
	// else the driving cell would violate the fanout limit.
	int num_buffers = std::min((int)std::ceil(static_cast<double>(fanout) / limit), limit);
	// The max output (fanout) per buffer: MaxOut = Ceil(Fanout / NbBuffers)
	int max_output_per_buffer = std::ceil((float)fanout / (float)num_buffers);
	if (debug) {
		std::cout << "Fanout: " << fanout << "\n";
		std::cout << "Limit: " << limit << "\n";
		std::cout << "Num_buffers: " << num_buffers << "\n";
		std::cout << "Max_output_per_buffer: " << max_output_per_buffer << "\n";
		std::cout << "Signal: " << signame << "\n" << std::flush;
	}

	// Keep track of the fanout count for each new buffer
	std::map<Cell *, int> bufferActualFanout;
	// Array of buffers (The buffer output signal and the buffer cell) per cell output chunks
	std::map<RTLIL::SigSpec, std::vector<std::pair<RTLIL::SigSpec, Cell *>>> buffer_outputs;
	// Keep track of which buffer in the array is getting filled for a given chunk
	std::map<SigSpec, int> bufferIndexes;

	// Create new buffers and new wires
	int index_buffer = 0;
	for (SigChunk chunk : sigToBuffer.chunks()) {
		std::vector<std::pair<RTLIL::SigSpec, Cell *>> buffer_chunk_outputs;
		for (int i = 0; i < num_buffers; ++i) {
			std::string wireName = generateSigSpecName(module, sigToBuffer, true, "_wbuf" + std::to_string(index_buffer)).c_str();
			std::string cellName = generateSigSpecName(module, sigToBuffer, true, "_fbuf" + std::to_string(index_buffer), true).c_str();
			RTLIL::Cell *buffer = module->addCell(cellName, ID($buf));
			bufferActualFanout[buffer] = 0;
			RTLIL::SigSpec buffer_output = module->addWire(wireName, chunk.size());
			insertedBuffers.emplace(buffer, buffer_output.as_wire());
			buffer->setPort(ID(A), chunk);
			buffer->setPort(ID(Y), sigmap(buffer_output));
			buffer->fixup_parameters();
			buffer_chunk_outputs.push_back(std::make_pair(buffer_output, buffer)); // Old - New
			bufferIndexes[chunk] = 0;
			index_buffer++;
		}
		buffer_outputs.emplace(sigmap(SigSpec(chunk)), buffer_chunk_outputs);
	}

	// Cumulate all cells in the fanout of this cell
	std::set<Cell *> fanoutcells;
	getFanout(sig2CellsInFanout, sigmap, sigToBuffer, fanoutcells);

	// Fix input connections to cells in fanout of buffer to point to the inserted buffer
	for (Cell *fanoutcell : fanoutcells) {
		if (debug)
			std::cout << "\n  CELL in fanout: " << fanoutcell->name.c_str() << "\n" << std::flush;
		// For a given cell, if a buffer drives multiple inputs, use the same buffer for all connections to that cell
		std::map<SigSpec, SigSpec> usedBuffers;
		for (auto &conn : fanoutcell->connections()) {
			IdString portName = conn.first;
			// RTLIL::SigSpec actual = sigmap(conn.second);
			RTLIL::SigSpec actual = conn.second;
			if (fanoutcell->input(portName)) {
				if (actual.is_chunk()) {
					// Input of that cell is a chunk
					if (debug)
						std::cout << "  IS A CHUNK" << std::endl;
					if (buffer_outputs.find(actual) != buffer_outputs.end()) {
						if (debug)
							std::cout << "  MATCH" << std::endl;
						// Input is one of the cell's outputs, its a match
						SigSpec newSig =
						  updateToBuffer(module, bufferIndexes, buffer_outputs, sig2CellsInFanout, bufferActualFanout,
								 usedBuffers, max_output_per_buffer, fanoutcell, actual, debug);
						// Override the fanout cell's input with the buffer output
						fanoutcell->setPort(portName, newSig);
					}
				} else {
					// Input of that cell is a list of chunks
					if (debug)
						std::cout << "  NOT A CHUNK" << std::endl;
					if (isSigSpecUsedIn(actual, sigmap, sigToBuffer)) {
						// Create a new chunk vector
						std::vector<RTLIL::SigChunk> newChunks;
						for (SigChunk chunk : actual.chunks()) {
							if (buffer_outputs.find(chunk) != buffer_outputs.end()) {
								if (debug)
									std::cout << "  MATCH" << std::endl;
								SigSpec newSig = updateToBuffer(module, bufferIndexes, buffer_outputs,
												sig2CellsInFanout, bufferActualFanout, usedBuffers,
												max_output_per_buffer, fanoutcell, chunk, debug);
								// Append the buffer's output in the chunk vector
								newChunks.push_back(newSig.as_chunk());
							} else {
								// Append original chunk if no buffer used
								newChunks.push_back(chunk);
							}
						}
						// Override the fanout cell's input with the newly created chunk vector
						fanoutcell->setPort(portName, newChunks);
					}
				}
			}
		}
	}

	// Post-processing for all newly added buffers
	for (std::map<Cell *, int>::iterator itr = bufferActualFanout.begin(); itr != bufferActualFanout.end(); itr++) {
		if (itr->second == 1) {
			// Remove previously inserted buffers with fanout of 1 (Hard to predict the last buffer usage in above step)
			removeBuffer(module, sigmap, fanoutcells, insertedBuffers, itr->first, debug);
		} else {
			// Recursively fix the fanout of the newly created buffers
			RTLIL::SigSpec sig = getCellOutputSigSpec(itr->first, sigmap);
			fixfanout(module, sigmap, sig2CellsInFanout, insertedBuffers, sig, itr->second, limit, debug);
		}
	}
}

// Calculate cells and nets fanout
void calculateFanout(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout, dict<Cell *, int> &cellFanout,
		     dict<SigSpec, int> &sigFanout)
{
	// Precompute cell output sigspec to cell map
	dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
	sigCellDrivers(module, sigmap, sig2CellsInFanout, sig2CellsInFanin);
	// Precompute lhs2rhs and rhs2lhs sigspec map
	dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
	dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> rhsSig2LhsSig;
	lhs2rhs_rhs2lhs(module, sigmap, rhsSig2LhsSig, lhsSig2RhsSig);

	// Accumulate fanout from cell connections
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
	for (auto cell : module->selected_cells()) {
		if (!cellFanout.count(cell)) {
			noFanoutInfo.insert(cell);
		}
	}

	// Set those cells to fanout 1
	for (auto cell : noFanoutInfo) {
		cellFanout[cell] = 1;
	}

	// Correct input pin fanout
	for (Wire *wire : module->wires()) {
		if (wire->port_input) {
			SigSpec inp = sigmap(wire);
			int fanout = sigFanout[inp];
			if (fanout == 0) {
				int max = 0;
				for (int i = 0; i < inp.size(); i++) {
					SigSpec bit_sig = inp.extract(i, 1);
					int fa = sigFanout[bit_sig];
					max = std::max(max, fa);
				}
				sigFanout[inp] = max;
			}
		}
	}
}

// Bulk call to splitnets, filters bad requests and separates out types (Wires, ports) for proper processing
void splitNets(Design *design, std::map<Module *, std::vector<RTLIL::SigSpec>> &sigsToSplit, bool formalFriendly)
{
	std::string wires;
	std::string inputs;
	std::string outputs;
	// Memorize selection
	Pass::call(design, "select -set presplitnets %");
	// Clear selection
	Pass::call(design, "select -none");
	std::set<Wire *> selected;
	for (std::map<Module *, std::vector<RTLIL::SigSpec>>::iterator itr = sigsToSplit.begin(); itr != sigsToSplit.end(); itr++) {
		Module *module = itr->first;
		for (RTLIL::SigSpec sigToSplit : itr->second) {
			Wire *parentWire = getParentWire(sigToSplit);
			if (!parentWire)
				continue;
			if (selected.find(parentWire) != selected.end())
				continue;
			selected.insert(parentWire);
			if (formalFriendly) {
				// Formal verification does not like ports to be split.
				// This option will prevent some buffering to happen on high fanout input/output ports,
				// but it will make formal happy.
				if ((!parentWire->port_input) && (!parentWire->port_output))
			    design->select(module, parentWire);
			} else {
			  design->select(module, parentWire);
			}
		}
	}
	Pass::call(design, std::string("splitnets") + (formalFriendly ? "" : " -ports"));
	// Restore selection
	Pass::call(design, "select @presplitnets");
}

struct AnnotateCellFanout : public ScriptPass {
	AnnotateCellFanout() : ScriptPass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
	void script() override {}
	void help() override
	{
		log("\n");
		log("    annotate_cell_fanout [options] [selection]\n");
		log("\n");
		log("This pass annotates cell fanout and optionally inserts balanced buffer trees to limit fanout.\n");
		log("\n");
		log("    -limit <limit>\n");
		log("        Limits the fanout by inserting balanced buffer trees.\n");
		log("    -formal\n");
		log("        For formal verification to pass, will prevent splitnets passes on ports, even if they have large fanout.\n");
		log("    -inputs\n");
		log("        Fix module inputs fanout.\n");
		log("    -clocks\n");
		log("        Fix module clocks fanout.\n");
		log("    -resets\n");
		log("        Fix module resets fanout.\n");
		log("    -debug\n");
		log("        Debug trace.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int limit = -1;
		bool formalFriendly = false;
		bool buffer_inputs = false;
		bool buffer_clocks = false;
		bool buffer_resets = false;
		bool debug = false;
		if (design == nullptr) {
			log_error("No design object\n");
			return;
		}
		log("Running annotate_cell_fanout pass\n");
		log_flush();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-debug") {
				debug = true;
				continue;
			}
			if (args[argidx] == "-limit") {
				limit = std::atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-formal") {
				formalFriendly = true;
				continue;
			}
			if (args[argidx] == "-inputs") {
				buffer_inputs = true;
				continue;
			}
			if (args[argidx] == "-clocks") {
				buffer_clocks = true;
				continue;
			}
			if (args[argidx] == "-resets") {
				buffer_resets = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if ((limit != -1) && (limit < 2)) {
			log_error("Fanout cannot be limited to less than 2\n");
			return;
		}

		// Collect all the high fanout signals to split
		std::map<Module *, std::vector<SigSpec>> signalsToSplit;
		for (auto module : design->selected_modules()) {
			// Calculate fanout
			SigMap sigmap(module);
			dict<Cell *, int> cellFanout;
			dict<SigSpec, int> sigFanout;
			dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
			calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout, sigFanout);

			// Cells output nets with high fanout
			std::vector<RTLIL::SigSpec> netsToSplit;
			for (auto itrCell : cellFanout) {
				Cell *cell = itrCell.first;
				int fanout = itrCell.second;
				if (limit > 0 && (fanout > limit)) {
					int nbOutputs = 0;
					for (auto &conn : cell->connections()) {
						IdString portName = conn.first;
						if (cell->output(portName)) {
							nbOutputs++;
						}
					}
					for (auto &conn : cell->connections()) {
						IdString portName = conn.first;
						RTLIL::SigSpec actual = conn.second;
						if (cell->output(portName)) {
							RTLIL::SigSpec cellOutSig = sigmap(actual);
							netsToSplit.push_back(cellOutSig);
						}
					}
				}
			}
			if (buffer_inputs) {
				// Module input nets with high fanout
				std::vector<RTLIL::SigSpec> wiresToSplit;
				for (Wire *wire : module->wires()) {
					if (wire->port_input) {
						SigSpec inp = sigmap(wire);
						int fanout = sigFanout[inp];
						if (limit > 0 && (fanout > limit)) {
							netsToSplit.push_back(inp);
						}
					}
				}
			}
			signalsToSplit.emplace(module, netsToSplit);
		}
		// Split all the high fanout nets in one pass for the whole design
		splitNets(design, signalsToSplit, formalFriendly);

		// Fix the high fanout nets
		for (auto module : design->selected_modules()) {
			bool fixedFanout = false;
			// All the buffers inserted in the module
			std::map<Cell *, Wire *> insertedBuffers;
			{
				// Fix high fanout
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<SigSpec, int> sigFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout, sigFanout);

				// Fix cells outputs with high fanout
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					if (limit > 0 && (fanout > limit)) {
						for (auto &conn : cell->connections()) {
							IdString portName = conn.first;
							RTLIL::SigSpec actual = conn.second;
							if (cell->output(portName)) {
								RTLIL::SigSpec cellOutSig = sigmap(actual);
								for (int i = 0; i < cellOutSig.size(); i++) {
									SigSpec bit_sig = cellOutSig.extract(i, 1);
									int bitfanout = sig2CellsInFanout[bit_sig].size();
									fixfanout(module, sigmap, sig2CellsInFanout, insertedBuffers, bit_sig,
										  bitfanout, limit, debug);
								}
							}
						}
						fixedFanout = true;
					} else {
						// Add attribute with fanout info to every cell
						cell->set_string_attribute("$FANOUT", std::to_string(fanout));
					}
				}

				// Mark clocks, resets
				std::set<SigSpec> clock_sigs;
				std::set<SigSpec> reset_sigs;
				for (auto cell : module->selected_cells()) {
					if (cell->type.in(ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe), ID($aldff),
							  ID($aldffe), ID($sdff), ID($sdffe), ID($sdffce), ID($fsm), ID($memrd), ID($memrd_v2),
							  ID($memwr), ID($memwr_v2))) {
						// Check for clock input connection
						if (cell->hasPort(ID(CLK))) {
							RTLIL::SigSpec clk_sig = sigmap(cell->getPort(ID(CLK)));
							clock_sigs.insert(clk_sig);
						}
						if (cell->hasPort(ID(RST))) {
							RTLIL::SigSpec clk_sig = sigmap(cell->getPort(ID(RST)));
							reset_sigs.insert(clk_sig);
						}
						if (cell->hasPort(ID(ARST))) {
							RTLIL::SigSpec clk_sig = sigmap(cell->getPort(ID(ARST)));
							reset_sigs.insert(clk_sig);
						}
					}
				}

				// Fix module input nets with high fanout
				std::map<SigSpec, int> sigsToFix;
				for (Wire *wire : module->wires()) {
					if (wire->port_input) {
						SigSpec inp = sigmap(wire);
						bool is_clock = clock_sigs.find(inp) != clock_sigs.end();
						bool is_reset = reset_sigs.find(inp) != reset_sigs.end();
						bool filter_sig = (is_clock && !buffer_clocks) || (is_reset && !buffer_resets);
						int fanout = sigFanout[inp];
						if (limit > 0 && (fanout > limit)) {
							if (buffer_inputs && !(filter_sig)) {
								sigsToFix.emplace(inp, fanout);
							} else {
								wire->set_string_attribute("$FANOUT", std::to_string(fanout));
							}
						} else {
							wire->set_string_attribute("$FANOUT", std::to_string(fanout));
						}
					}
				}
				for (auto sig : sigsToFix) {
					for (int i = 0; i < sig.first.size(); i++) {
						SigSpec bit_sig = sig.first.extract(i, 1);
						int bitfanout = sig2CellsInFanout[bit_sig].size();
						fixfanout(module, sigmap, sig2CellsInFanout, insertedBuffers, bit_sig, bitfanout, limit, debug);
					}
					fixedFanout = true;
				}
			}

			if (fixedFanout) {
				// If Fanout got fixed, recalculate and annotate final fanout
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<SigSpec, int> sigFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout, sigFanout);

				// Cleanup and annotation
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					// Final cleanup, remove buffers of 1
					if ((fanout == 1) && insertedBuffers.find(cell) != insertedBuffers.end()) {
						SigSpec bufferOut = insertedBuffers.find(cell)->second;
						std::set<Cell *> fanoutcells;
						getFanout(sig2CellsInFanout, sigmap, bufferOut, fanoutcells);
						removeBuffer(module, sigmap, fanoutcells, insertedBuffers, cell, debug);
						continue;
					}
					// Add attribute with fanout info to every cell
					cell->set_string_attribute("$FANOUT", std::to_string(fanout));
				}
				for (Wire *wire : module->wires()) {
					if (wire->port_input) {
						SigSpec inp = sigmap(wire);
						int fanout = sigFanout[inp];
						// Add attribute with fanout info to every input port
						wire->set_string_attribute("$FANOUT", std::to_string(fanout));
					}
				}
				log("Added %ld buffers in module %s\n", insertedBuffers.size(), module->name.c_str());
			}
		}

		log("End annotate_cell_fanout pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
