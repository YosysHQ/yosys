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

void fixfanout(RTLIL::Design *design, RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout,
	       RTLIL::Cell *cell, int fanout, int limit, bool debug)
{
	if (fanout <= limit) {
		if (debug) {
		  std::cout << "Nothing to do for: " << cell->name.c_str() << std::endl;
		  std::cout << "Fanout: " << fanout << std::endl;
		}
		return; // No need to insert buffers
	} else {
		if (debug) {
		  std::cout << "Something to do for: " << cell->name.c_str() << std::endl;
		  std::cout << "Fanout: " << fanout << std::endl;
		}
	}
	int num_buffers = std::min((int)std::ceil(static_cast<double>(fanout) / limit), limit);
	int max_output_per_buffer = std::ceil((float)fanout / (float)num_buffers);
	if (debug) {
	  std::cout << "fanout: " << fanout << "\n";
	  std::cout << "limit: " << limit << "\n";
	  std::cout << "num_buffers: " << num_buffers << "\n";
	  std::cout << "max_output_per_buffer: " << max_output_per_buffer << "\n";
	  std::cout << "CELL: " << cell->name.c_str() << "\n" << std::flush;
	}

	// Get cell output
	RTLIL::SigSpec cellOutSig;
	for (auto &conn : cell->connections()) {
		IdString portName = conn.first;
		RTLIL::SigSpec actual = conn.second;
		if (cell->output(portName)) {
			cellOutSig = sigmap(actual);
			break;
		}
	}

	// Create buffers and new wires
	std::map<Cell *, int> bufferActualFanout; // Keep track of the fanout count for each new buffer
	std::map<RTLIL::SigSpec, std::vector<std::tuple<RTLIL::SigSpec, Cell *>>> buffer_outputs;
	std::map<SigSpec, int> bufferIndexes;
	for (SigChunk chunk : cellOutSig.chunks()) {
		std::vector<std::tuple<RTLIL::SigSpec, Cell *>> buffer_chunk_outputs;
		for (int i = 0; i < num_buffers; ++i) {
			RTLIL::Cell *buffer = module->addCell(NEW_ID2_SUFFIX("fbuf"), ID($pos));
			bufferActualFanout[buffer] = 0;
			RTLIL::SigSpec buffer_output = module->addWire(NEW_ID2_SUFFIX("fbuf"), chunk.size());
			buffer->setPort(ID(A), chunk);
			buffer->setPort(ID(Y), sigmap(buffer_output));
			buffer->fixup_parameters();
			buffer_chunk_outputs.push_back(std::make_tuple(buffer_output, buffer)); // Old - New
			bufferIndexes[chunk] = 0;
		}
		buffer_outputs.emplace(sigmap(SigSpec(chunk)), buffer_chunk_outputs);
	}

	// Cumulate all cells in the fanout of this cell
	std::set<Cell *> cells = sig2CellsInFanout[cellOutSig];
	for (int i = 0; i < cellOutSig.size(); i++) {
		SigSpec bit_sig = cellOutSig.extract(i, 1);
		for (Cell *c : sig2CellsInFanout[sigmap(bit_sig)]) {
			cells.insert(c);
		}
	}

	// Fix input connections to cells in fanout of buffer to point to the inserted buffer
	for (Cell *c : cells) {
		if (debug)
		  std::cout << "\n  CELL in fanout: " << c->name.c_str() << "\n" << std::flush;
		for (auto &conn : c->connections()) {
			IdString portName = conn.first;
			RTLIL::SigSpec actual = sigmap(conn.second);
			if (c->input(portName)) {
				if (actual.is_chunk()) {
					if (debug)
					  std::cout << "  IS A CHUNK" << std::endl;
					if (buffer_outputs.find(actual) != buffer_outputs.end()) {
						if (debug) std::cout << "  CHUNK, indexCurrentBuffer: " << bufferIndexes[actual] << " buffer_outputs "
							  << buffer_outputs[actual].size() << std::endl;
						std::vector<std::tuple<RTLIL::SigSpec, Cell *>> &buf_info_vec = buffer_outputs[actual];
						int bufferIndex = bufferIndexes[actual];
						std::tuple<RTLIL::SigSpec, Cell *> &buf_info = buf_info_vec[bufferIndex];
						SigSpec newSig = std::get<0>(buf_info);
						Cell *newBuf = std::get<1>(buf_info);
						c->setPort(portName, newSig);
						sig2CellsInFanout[newSig].insert(c);
						bufferActualFanout[newBuf]++;
						if (debug)std::cout << "   USE: " << newBuf->name.c_str() << " fanout: " << bufferActualFanout[newBuf]
							    << std::endl;
						if (bufferActualFanout[newBuf] >= max_output_per_buffer) {
							if (debug) std::cout << "  REACHED MAX" << std::endl;
							if (buffer_outputs[actual].size() - 1 > bufferIndex) {
								bufferIndexes[actual]++;
								if (debug) std::cout << "  NEXT BUFFER" << std::endl;
							}
						}
					}
				} else {
					if (debug)
					  std::cout << "  NOT A CHUNK" << std::endl;
					bool match = false;
					for (SigChunk chunk_a : actual.chunks()) {
						if (sigmap(SigSpec(chunk_a)) == sigmap(SigSpec(cellOutSig))) {
							match = true;
						} else {
							for (SigChunk chunk_c : cellOutSig.chunks()) {
								if (sigmap(SigSpec(chunk_a)) == sigmap(SigSpec(chunk_c))) {
									match = true;
									break;
								}
							}
						}
						if (match)
							break;
					}
					if (match) {
						if (debug) std::cout << "  MATCH" << std::endl;
						std::vector<RTLIL::SigChunk> newChunks;
						for (SigChunk chunk : actual.chunks()) {
							bool replaced = false;
							if (buffer_outputs.find(chunk) != buffer_outputs.end()) {
								if (debug) std::cout << "  CHUNK, indexCurrentBuffer: " << bufferIndexes[chunk]
									  << " buffer_outputs " << buffer_outputs[chunk].size() << std::endl;
								std::vector<std::tuple<RTLIL::SigSpec, Cell *>> &buf_info_vec = buffer_outputs[chunk];
								int bufferIndex = bufferIndexes[chunk];
								std::tuple<RTLIL::SigSpec, Cell *> &buf_info = buf_info_vec[bufferIndex];
								SigSpec newSig = std::get<0>(buf_info);
								Cell *newBuf = std::get<1>(buf_info);
								newChunks.push_back(newSig.as_chunk());
								sig2CellsInFanout[newSig].insert(c);
								replaced = true;
								bufferActualFanout[newBuf]++;
								if (debug) std::cout << "   USE: " << newBuf->name.c_str()
									  << " fanout: " << bufferActualFanout[newBuf] << std::endl;
								if (bufferActualFanout[newBuf] >= max_output_per_buffer) {
									if (debug) std::cout << "  REACHED MAX" << std::endl;
									if (buffer_outputs[chunk].size() - 1 > bufferIndex) {
										bufferIndexes[chunk]++;
										if (debug) std::cout << "  NEXT BUFFER" << std::endl;
									}
								}
							}
							if (!replaced) {
								newChunks.push_back(chunk);
							}
						}
						c->setPort(portName, newChunks);
						break;
					}
				}
			}
		}
	}

	for (std::map<Cell *, int>::iterator itr = bufferActualFanout.begin(); itr != bufferActualFanout.end(); itr++) {
		if (itr->second == 1) {
			// Remove previously inserted buffers with fanout of 1 (Hard to predict the last buffer usage in above step)
			if (debug) std::cout << "Buffer with fanout 1: " << itr->first->name.c_str() << std::endl;
			RTLIL::SigSpec bufferInSig = itr->first->getPort(ID::A);
			RTLIL::SigSpec bufferOutSig = itr->first->getPort(ID::Y);
			for (Cell *c : cells) {
				if (debug) std::cout << "Cell in its fanout: " << c->name.c_str() << std::endl;
				for (auto &conn : c->connections()) {
					IdString portName = conn.first;
					RTLIL::SigSpec actual = conn.second;
					if (c->input(portName)) {
						if (actual.is_chunk()) {
							if (bufferOutSig == sigmap(actual)) {
								if (debug) std::cout << "Replace: " << getParentWire(bufferOutSig)->name.c_str() << " by "
									  << getParentWire(bufferInSig)->name.c_str() << std::endl;
								c->setPort(portName, bufferInSig);
							}
						} else {
							std::vector<RTLIL::SigChunk> newChunks;
							for (SigChunk chunk : actual.chunks()) {
								if (sigmap(SigSpec(chunk)) == sigmap(bufferOutSig)) {
									if (debug) std::cout << "Replace: " << getParentWire(bufferOutSig)->name.c_str()
										  << " by " << getParentWire(bufferInSig)->name.c_str() << std::endl;
									newChunks.push_back(bufferInSig.as_chunk());
								} else {
									newChunks.push_back(chunk);
								}
							}
							c->setPort(portName, newChunks);
						}
					}
				}
			}
			module->remove(itr->first);
			module->remove({bufferOutSig.as_wire()});
		} else {
			// Recursively fix the fanout of the newly created buffers
			fixfanout(design, module, sigmap, sig2CellsInFanout, itr->first, itr->second, limit, debug);
		}
	}
}

void calculateFanout(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout, dict<Cell *, int> &cellFanout)
{
	// Precompute cell output sigspec to cell map
	dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanin;
	sigCellDrivers(module, sigmap, sig2CellsInFanout, sig2CellsInFanin);
	// Precompute lhs2rhs and rhs2lhs sigspec map
	dict<RTLIL::SigSpec, RTLIL::SigSpec> lhsSig2RhsSig;
	dict<RTLIL::SigSpec, std::set<RTLIL::SigSpec>> rhsSig2LhsSig;
	lhs2rhs_rhs2lhs(module, sigmap, rhsSig2LhsSig, lhsSig2RhsSig);

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
}

std::string substringuntil(const std::string &str, char delimiter)
{
	size_t pos = str.find(delimiter);
	if (pos != std::string::npos) {
		return str.substr(0, pos);
	} else {
		return str;
	}
}

struct AnnotateCellFanout : public ScriptPass {
	AnnotateCellFanout() : ScriptPass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
	void script() override {}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int limit = -1;
		bool formalFriendly = false;
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
			break;
		}
		extra_args(args, argidx, design);
		if ((limit != -1) && (limit < 2)) {
			log_error("Fanout cannot be limited to less than 2\n");
			return;
		}
		for (auto module : design->selected_modules()) {
			bool fixedFanout = false;
			{
				// Split output nets of cells with high fanout
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout);

				std::vector<Cell *> cellsToFixFanout;
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					if (limit > 0 && (fanout > limit)) {
						cellsToFixFanout.push_back(cell);
					}
				}
				std::set<std::string> netsToSplitS;
				std::string netsToSplit;
				std::string portsToSplit;
				for (Cell *cell : cellsToFixFanout) {
					RTLIL::SigSpec cellOutSig;
					for (auto &conn : cell->connections()) {
						IdString portName = conn.first;
						RTLIL::SigSpec actual = conn.second;
						if (cell->output(portName)) {
							cellOutSig = sigmap(actual);
							break;
						}
					}
					std::string parent = getParentWire(cellOutSig)->name.c_str();
					parent = substringuntil(parent, '[');
					if (netsToSplitS.find(parent) == netsToSplitS.end()) {
						netsToSplit += std::string(" w:") + parent;  // Wire
						portsToSplit += std::string(" o:") + parent; // Output port
						netsToSplitS.insert(parent);
						// Splitnets has to be invoke with individual nets, sending a bunch of nets as selection
						// selects more than required (bug in selection/splitnets).
						std::string splitnets = std::string("splitnets ") + netsToSplit;
						Pass::call(design, splitnets);
						splitnets = std::string("splitnets -ports_only ") + portsToSplit;
						if (!formalFriendly) 
							// Formal verification does not like ports to be split.
							// This will prevent some buffering to happen on output ports used also internally in high fanout,
							// but it will make formal happy.
						  Pass::call(design, splitnets);
						netsToSplit = "";
						portsToSplit = "";
					}
				}
			}

			{
				// Fix high fanout
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout);

				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					if (limit > 0 && (fanout > limit)) {
						fixfanout(design, module, sigmap, sig2CellsInFanout, cell, fanout, limit, debug);
						fixedFanout = true;
					} else {
						// Add attribute with fanout info to every cell
						cell->set_string_attribute("$FANOUT", std::to_string(fanout));
					}
				}
			}

			if (fixedFanout) {
				// If Fanout got fixed, recalculate and annotate final fanout
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout);
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					// Add attribute with fanout info to every cell
					cell->set_string_attribute("$FANOUT", std::to_string(fanout));
				}
			}
		}

		log("End annotate_cell_fanout pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
