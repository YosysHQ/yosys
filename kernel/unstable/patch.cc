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
	cell->module = nullptr;
	return cell;
}

Wire* Patch::addWire(IdString name, int width) {
	wires_.push_back(std::make_unique<Wire>(Wire::ConstructToken{}));

	Wire* wire = wires_.back().get();
	wire->name = name;
	wire->width = width;
	wire->module = nullptr;
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
		wire->module = mod;
		Wire* raw = wire.release();
		mod->wires_[raw->name] = raw;
	}
	log("patching:\n");
	log_cell(old_cell);
	for (auto& cell: cells_) {
		log_cell(cell.get());
		Cell* raw = cell.release();
		mod->cells_[raw->name] = raw;
		for (auto [port_name, sig] : raw->connections()) {
			auto dir = raw->port_dir(port_name);
			log_assert(dir != PD_UNKNOWN);
			if (dir == PD_OUTPUT || dir == PD_INOUT) {
				SigSpec sig_to_fix = sig;
				if (raw == new_cell) {
					// RAUW
					// TODO optimized implementation for signorm fanout transfer that avoids expensive(?) setPort?
					auto yoink = old_cell->getPort(port_name);
					log(">>>> RAUW %s to %s\n", port_name, log_signal(yoink));
					new_cell->setPort(port_name, yoink);
					old_cell->setPort(port_name, mod->addWire(NEW_ID, yoink.size()));
					sig_to_fix = yoink;
				}
				if (sig_to_fix.size()) {
					auto* wire = sig_to_fix.as_wire();
					wire->driverCell_ = raw;
					wire->driverPort_ = port_name;
				}
			}
		}
		raw->module = mod;
		raw->fixup_parameters();
	}
	log_module(mod, "");
}


YOSYS_NAMESPACE_END