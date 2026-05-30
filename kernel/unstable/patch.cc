#include "kernel/unstable/patch.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

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

void Patch::gc(Cell* old_cell, bool track, pool<string>* src_pool) {
	log_debug("gc %s\n", old_cell->name);
	if (old_cell->type.in(ID($input_port), ID($output_port), ID($public)))
		return;
	pool<Cell*> inputs;
	for (auto [port_name, sig] : old_cell->connections()) {
		auto dir = old_cell->port_dir(port_name);
		// Unknown port direction (e.g. user module instance whose interface
		// isn't registered): can't decide input vs output, so don't gc it.
		// TODO: should be log_assert once PD_UNKNOWN is fixed at the source
		// (see claude-notes.md).
		if (dir == PD_UNKNOWN)
			return;
		// TODO only running GC through whole connections?
		log_debug("\tport %s\n", port_name);
		if (sig.size() && sig.is_wire()) {
			if (dir == PD_OUTPUT || dir == PD_INOUT) {
				for (auto bit : sig) {
					// Reject GC if used
					if (!mod->fanout(bit).empty()) {
						log_debug("\treject fanout\n");
						return;
					} else
					 	log_debug("\tok\n");
				}
			}
			if (dir == PD_INPUT || dir == PD_INOUT) {
				Wire* in_wire = sig.as_wire();
				log_assert(in_wire);
				log_debug("\twire %s\n", in_wire->name);
				if (in_wire->known_driver() && !leaves.count(in_wire))
					inputs.insert(in_wire->driverCell());
			}
		}
	}
	log_debug("\tremove %s\n", old_cell->name);
	// Only track recursively-removed cells. The top-level patched cell is the
	// caller's current iteration variable and won't be re-encountered.
	if (track && removed_cells)
		removed_cells->insert(old_cell);
	// The cell about to be removed contributes its src so all the cells gc'd
	// in this patch (top-level + input cone) get merged into the new cells'
	// src — that's the "transfer src automatically" guarantee.
	if (src_pool)
		src_pool->insert(old_cell->get_src_attribute());
	old_cell->module->remove(old_cell);
	for (auto input : inputs)
		gc(input, /*track=*/true, src_pool);
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
	patch(old_cell, {{old_port, new_sig}}, nullptr);
}

void Patch::patch(Cell* old_cell, const std::vector<std::pair<IdString, SigSpec>> &port_replacements) {
	patch(old_cell, port_replacements, nullptr);
}

void Patch::patch(Cell* old_cell, IdString old_port, SigSpec new_sig, Cell* merge_src_into) {
	patch(old_cell, {{old_port, new_sig}}, merge_src_into);
}

void Patch::patch(Cell* old_cell, const std::vector<std::pair<IdString, SigSpec>> &port_replacements, Cell* merge_src_into) {
	std::vector<SigSpec> old_sigs;
	for (auto &[port, new_sig] : port_replacements) {
		SigSpec old_sig = old_cell->getPort(port);
		if (old_sig.size() != new_sig.size())
			log_error("patch size mismatch on cell %s port %s: old %d (%s) vs new %d (%s)\n",
					log_id(old_cell->name), log_id(port), old_sig.size(), log_signal(old_sig),
					new_sig.size(), log_signal(new_sig));
		log_debug("patching %s %s which is %s with %s:\n", old_cell->name, port, log_signal(old_sig), log_signal(new_sig));
		old_sigs.push_back(old_sig);
	}

	// Record leaves (existing wires consumed as inputs by the new cells) so
	// gc() stops at them. Detected via bit.wire->module being non-null:
	// uncommitted wires belong to no module yet.
	for (auto& cell : cells_) {
		for (auto& [port_name, sig] : cell->connections()) {
			auto dir = cell->port_dir(port_name);
			if (dir == PD_INPUT || dir == PD_INOUT) {
				for (auto bit : sig) {
					if (bit.is_wire() && bit.wire->module)
						leaves.insert(bit.wire);
				}
			}
		}
	}

	// Commit new cells/wires first so new_sig becomes a driven signal in the
	// signorm index before we merge. Track raw pointers so we can update
	// their src attribute after gc finishes collecting from removed cells.
	std::vector<Cell*> committed_new_cells;
	committed_new_cells.reserve(cells_.size());
	for (auto& cell: cells_) {
		cell->fixup_parameters();
		committed_new_cells.push_back(commit_cell(std::move(cell)));
	}

	for (auto& wire: wires_)
		commit_wire(std::move(wire));

	// Now drop old_cell's drivers so old_sigs are undriven, then merge each
	// into its new_sig. connect_incremental updates sigmap and re-normalizes
	// fanout consumers in place — no full sigNormalize needed.
	for (auto &[port, new_sig] : port_replacements)
		old_cell->setPort(port, SigSpec());
	for (size_t i = 0; i < port_replacements.size(); i++) {
		auto &[port, new_sig] = port_replacements[i];
		if (map)
			map->add(old_sigs[i], new_sig);
		mod->connect_incremental(old_sigs[i], new_sig);
	}

	// gc removes old_cell AND any newly-dead input-cone cells, contributing
	// each removed cell's src into the pool. The merged-into cell (e.g. an
	// opt_merge keep_cell) and any caller-bequeathed pool entries also get
	// folded in here.
	pool<string> src_pool;
	if (merge_src_into)
		src_pool.insert(merge_src_into->get_src_attribute());
	gc(old_cell, /*track=*/false, &src_pool);

	std::string src_str = AttrObject::strpool_attribute_to_str(src_pool);
	for (Cell* c : committed_new_cells)
		c->set_src_attribute(src_str);
	if (merge_src_into)
		merge_src_into->set_src_attribute(src_str);

	cells_.clear();
	wires_.clear();
	leaves.clear();
}

void Patch::commit_inheriting_src(Cell* src_source) {
	std::string src = src_source ? src_source->get_src_attribute() : std::string();
	for (auto& cell : cells_) {
		cell->set_src_attribute(src);
		cell->fixup_parameters();
		commit_cell(std::move(cell));
	}
	for (auto& wire : wires_)
		commit_wire(std::move(wire));
	cells_.clear();
	wires_.clear();
}

YOSYS_NAMESPACE_END