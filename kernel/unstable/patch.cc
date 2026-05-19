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
	wires_.push_back(std::make_unique<Wire>(Wire::ConstructToken{}));

	Wire* wire = wires_.back().get();
	wire->name = name;
	wire->width = width;
	return wire;
}

// TODO code golf


RTLIL::Wire *RTLIL::Patch::addWire(RTLIL::IdString name, const RTLIL::Wire *other)
{
	RTLIL::Wire *wire = addWire(std::move(name));
	wire->width = other->width;
	wire->start_offset = other->start_offset;
	wire->port_id = other->port_id;
	wire->port_input = other->port_input;
	wire->port_output = other->port_output;
	wire->upto = other->upto;
	wire->is_signed = other->is_signed;
	wire->attributes = other->attributes;
	return wire;
}

void Patch::patch(Cell* old_cell, Cell* new_cell) {
	for (auto& wire: wires_) {
		Wire* raw = wire.release();
		mod->wires_[raw->name] = raw;
	}
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
					// TODO optimized implementation for signorm fanout transfer?
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