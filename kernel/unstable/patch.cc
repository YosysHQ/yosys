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



struct SrcCollector {
	pool<Cell*> to_do;
	pool<Cell*> done;
	pool<string> src;

	void collect_src(Cell* old_cell) {
		if (done.count(old_cell))
			return;
		done.insert(old_cell);

		log("collect %s\n", old_cell->name);
		src.insert(old_cell->get_src_attribute());

		std::vector<Cell*> input_cells = {};
		for (auto [port_name, sig] : old_cell->connections()) {
			auto dir = old_cell->port_dir(port_name);
			log_assert(dir != PD_UNKNOWN);
			if (dir == PD_INPUT || dir == PD_INOUT) {
				if (sig.size() && sig.is_wire()) {
					Wire* in_wire = sig.as_wire();
					if (!in_wire->module)
						input_cells.push_back(in_wire->driverCell());
					// if (!leaves.count(in_wire))
				}
			}
		}
		for (auto input : input_cells)
			collect_src(input);
	}

	void collect_src(SigSpec old_sig) {
		log("collect %s\n", log_signal(old_sig));
		for (auto bit : old_sig) {
			if (bit.is_wire() && bit.wire->module) {
				log_assert(bit.wire->driverCell_);
				to_do.insert(bit.wire->driverCell_);
			}
		}
		for (auto cell : to_do)
			collect_src(cell);
	}
};

void Patch::gc(Cell* old_cell) {
	log("gc %s\n", old_cell->name);
	std::vector<Cell*> inputs = {};
	for (auto [port_name, sig] : old_cell->connections()) {
		auto dir = old_cell->port_dir(port_name);
		log_assert(dir != PD_UNKNOWN);
		if (sig.size() && sig.is_wire()) {
			if (dir == PD_OUTPUT || dir == PD_INOUT) {
				for (auto bit : sig) {
					// Reject GC if used
					if (!mod->fanout(bit).empty())
						return;
				}
			}
			if (dir == PD_INPUT || dir == PD_INOUT) {
				Wire* in_wire = sig.as_wire();
				log_assert(in_wire);
				log_debug("%s\n", in_wire->name);
				if (in_wire->known_driver() && !leaves.count(in_wire))
					inputs.push_back(in_wire->driverCell());
			}
		}
	}
	old_cell->module->remove(old_cell);
	for (auto input : inputs)
		gc(input);
}

Wire* Patch::commit_wire(std::unique_ptr<Wire> wire) {
	Wire* raw = wire.release();
	mod->wires_[raw->name] = raw;
	raw->module = mod;
	return raw;
}

Cell* Patch::commit_cell(std::unique_ptr<Cell> cell) {
	Cell* raw = cell.release();
	mod->cells_[raw->name] = raw;
	raw->module = mod;
	raw->initIndex();
	return raw;
}

void Patch::patch(Cell* old_cell, IdString old_port, SigSpec new_sig) {
	SigSpec old_sig = old_cell->getPort(old_port);
	log_assert(old_sig.size() == new_sig.size());
	log_debug("patching %s %s which is %s with %s:\n", old_cell->name, old_port, log_signal(old_sig), log_signal(new_sig));

	SrcCollector collector;
	collector.collect_src(old_sig);
	std::string src_str = AttrObject::strpool_attribute_to_str(collector.src);

	old_cell->setPort(old_port, SigSpec());
	mod->connect(old_sig, new_sig);
	if (map)
		map->add(old_sig, new_sig);

	for (auto& cell: cells_) {
		cell->set_src_attribute(src_str);
		cell->fixup_parameters();
		commit_cell(std::move(cell));
	}

	for (auto& wire: wires_)
		commit_wire(std::move(wire));

	gc(old_cell);
}

YOSYS_NAMESPACE_END