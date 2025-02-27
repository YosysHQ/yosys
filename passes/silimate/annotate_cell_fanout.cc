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

void fixfanout(RTLIL::Module *module, SigMap &sigmap, dict<RTLIL::SigSpec, std::set<Cell *>> &sig2CellsInFanout, RTLIL::Cell *cell, int fanout,
	       int limit)
{
	if (fanout <= limit) {
		std::cout << "Nothing to do for: " << cell->name.c_str() << std::endl;
		std::cout << "Fanout: " << fanout << std::endl;
		return; // No need to insert buffers
	} else {
		std::cout << "Something to do for: " << cell->name.c_str() << std::endl;
		std::cout << "Fanout: " << fanout << std::endl;
	}

	int num_buffers = std::min((int)std::ceil(static_cast<double>(fanout) / limit), limit);
	int max_output_per_buffer = std::ceil((float)fanout / (float)num_buffers);
	std::cout << "fanout: " << fanout << "\n";
	std::cout << "limit: " << limit << "\n";
	std::cout << "num_buffers: " << num_buffers << "\n";
	std::cout << "max_output_per_buffer: " << max_output_per_buffer << "\n";
	std::vector<RTLIL::SigSpec> buffer_outputs;
	std::vector<RTLIL::Cell *> buffers;
	std::cout << "CELL: " << cell->name.c_str() << "\n" << std::flush;
	RTLIL::SigSpec cellOutSig;
	for (auto &conn : cell->connections()) {
		IdString portName = conn.first;
		RTLIL::SigSpec actual = conn.second;
		if (cell->output(portName)) {
			cellOutSig = sigmap(actual);
			break;
		}
	}
	for (int i = 0; i < num_buffers; ++i) {
		RTLIL::Cell *buffer = module->addCell(NEW_ID2_SUFFIX("fbuf"), ID($buf)); // Assuming BUF is defined
		RTLIL::SigSpec buffer_output = module->addWire(NEW_ID2_SUFFIX("fbuf"));
		buffer->setPort(ID(A), cellOutSig);
		buffer->setPort(ID(Y), sigmap(buffer_output));
		buffer_outputs.push_back(buffer_output);
		buffers.push_back(buffer);
	}
	std::set<Cell *> cells = sig2CellsInFanout[cellOutSig];
	int indexCurrentBuffer = 0;
	int indexFanout = 0;
	std::map<Cell *, int> bufferActualFanout;
	for (Cell *c : cells) {
		for (auto &conn : c->connections()) {
			IdString portName = conn.first;
			RTLIL::SigSpec actual = conn.second;
			if (c->input(portName)) {
				if (actual.is_chunk()) {
					if (sigmap(actual) == cellOutSig) {
						std::cout << "vector size: " << buffer_outputs.size() << std::endl;
						std::cout << "index : " << indexCurrentBuffer << std::endl;
						c->setPort(portName, buffer_outputs[indexCurrentBuffer]);
						sig2CellsInFanout[sigmap(buffer_outputs[indexCurrentBuffer])].insert(c);
						indexFanout++;
						bufferActualFanout[buffers[indexCurrentBuffer]] = indexFanout;
						if (indexFanout >= max_output_per_buffer) {
							indexFanout = 0;
							indexCurrentBuffer++;
						}
						break;
					}
				} else {
					bool match = false;
					for (SigChunk chunk : actual.chunks()) {
						if (sigmap(SigSpec(chunk)) == cellOutSig) {
							match = true;
							break;
						}
					}
					if (match) {
						std::vector<RTLIL::SigChunk> newChunks;
						for (SigChunk chunk : actual.chunks()) {
						  if (sigmap(SigSpec(chunk)) == cellOutSig) {
								newChunks.push_back(buffer_outputs[indexCurrentBuffer].as_wire());
							} else {
								newChunks.push_back(chunk);
							}
						}
						c->setPort(portName, newChunks);
						sig2CellsInFanout[sigmap(buffer_outputs[indexCurrentBuffer])].insert(c);
						indexFanout++;
						bufferActualFanout[buffers[indexCurrentBuffer]] = indexFanout;
						if (indexFanout >= max_output_per_buffer) {
							indexFanout = 0;
							indexCurrentBuffer++;
						}
						break;
					}
				}
			}
		}
	}

	// Recursively fix the fanout of the newly created buffers
	for (std::map<Cell *, int>::iterator itr = bufferActualFanout.begin(); itr != bufferActualFanout.end(); itr++) {
		if (itr->second == 1) {
			// Remove newly created buffers with a fanout of 1
			std::cout << "Buffer of 1" << std::endl;
			for (Cell *c : cells) {
				for (auto &conn : c->connections()) {
					IdString portName = conn.first;
					RTLIL::SigSpec actual = conn.second;
					if (c->input(portName)) {
						if (sigmap(buffer_outputs[indexCurrentBuffer]) == sigmap(actual)) {
							c->setPort(portName, cellOutSig);
							std::cout << "Remove buffer of 1" << std::endl;
							module->remove(buffers[indexCurrentBuffer]);
							// module->remove({buffer_outputs[indexCurrentBuffer].as_wire()});
							break;
						}
					}
				}
			}
		} else {
			fixfanout(module, sigmap, sig2CellsInFanout, itr->first, itr->second, limit);
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

struct AnnotateCellFanout : public ScriptPass {
	AnnotateCellFanout() : ScriptPass("annotate_cell_fanout", "Annotate the cell fanout on the cell") {}
	void script() override {}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int limit = -1;
		if (design == nullptr) {
			log_error("No design object\n");
			return;
		}
		log("Running annotate_cell_fanout pass\n");
		log_flush();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-limit") {
				limit = std::atoi(args[++argidx].c_str());
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
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout);
				// Add attribute with fanout info to every cell
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					if (limit > 0 && (fanout > limit)) {
						fixfanout(module, sigmap, sig2CellsInFanout, cell, fanout, limit);
						fixedFanout = true;
					} else {
						cell->set_string_attribute("$FANOUT", std::to_string(fanout));
					}
				}
			}
			if (fixedFanout) {
				SigMap sigmap(module);
				dict<Cell *, int> cellFanout;
				dict<RTLIL::SigSpec, std::set<Cell *>> sig2CellsInFanout;
				calculateFanout(module, sigmap, sig2CellsInFanout, cellFanout);
				for (auto itrCell : cellFanout) {
					Cell *cell = itrCell.first;
					int fanout = itrCell.second;
					cell->set_string_attribute("$FANOUT", std::to_string(fanout));
				}
			}
		}

		log("End annotate_cell_fanout pass\n");
		log_flush();
	}
} SplitNetlist;

PRIVATE_NAMESPACE_END
