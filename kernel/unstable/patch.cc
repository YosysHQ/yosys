#include "kernel/unstable/patch.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

/** 
* Notes
*
* If we want GC, we need more indices
* namely user count (and users?). This should be optional
*
*
*/
using namespace RTLIL;

template class CellAdderMixin<Patch>;

Cell* Patch::addCell(IdString name, IdString type) {
	cells_.push_back(std::make_unique<Cell>(Cell::ConstructToken{}));

	Cell* cell = cells_.back().get();
	cell->name = name;
	cell->type = type;
	return cell;
}

Wire* Patch::addWire(IdString name, int width) {
	(void)name;
	(void)width;
	log_assert(false);
	return nullptr;
}

void Patch::patch(Cell* old_cell, Cell* new_cell) {
	pool<Cell*> patch_cells;
	for (auto& cell: cells_) {
		patch_cells.insert(cell.get());
	}
	log("patching:\n");
	log_cell(old_cell);
	for (auto& cell: cells_) {
		log("with:\n");
		log_cell(cell.get());
		log("ptr %p\n", cell.get());
		Cell* raw = cell.release();
		log("ptr2 %p\n", raw);
		mod->cells_[raw->name] = raw;
		raw->module = mod;
		for (auto [port_name, sig] : raw->connections()) {
			auto dir = raw->port_dir(port_name);
			log_assert(dir != PD_UNKNOWN);
			if (raw == new_cell)
				if (dir == PD_OUTPUT || dir == PD_INOUT) {
					// RAUW
					old_cell->setPort(port_name, mod->addWire(NEW_ID, sig.size()));
					new_cell->setPort(port_name, sig);
					auto* wire = sig.as_wire();
					wire->driverCell_ = new_cell;
					wire->driverPort_ = port_name;
				}
				// } else {
				// 	new_cell->setPort(port_name, sig); // map?
					// for (auto chunk : map(sig).chunks()) {
					// 	if (chunk.size() == 0)
					// 		continue;
					// 	log_assert(chunk.is_wire());
					// 	auto* wire = chunk.wire;
					// 	// TODO Use roots instead?
					// 	if (patch_cells.count(wire->driverCell_)) {
					// 		// How do we handle this?
					// 		log_assert(false);
					// 	} else {
					// 		// mod->sig_norm_index

					// 	}
					// }
		}
	}
	log_module(mod, "");
}


YOSYS_NAMESPACE_END