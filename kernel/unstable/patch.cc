#include "kernel/unstable/patch.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/newcelltypes.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

using namespace RTLIL;

template class CellAdderMixin<Patch>;

Cell* Patch::addCell(TwineRef name, TwineRef type) {
	cells_.push_back(std::make_unique<Cell>(Cell::ConstructToken{}));

	Cell* cell = cells_.back().get();
	cell->type_impl = type;
	cell->module = nullptr;
	staged_cell_names_[cell] = name;
	return cell;
}

// Cell* Patch::addCell(TwineRef name, IdString type) {
// 	static TwinePool s_pool;
// 	TwineRef tref = s_pool.lookup(type.str());
// 	log_assert(tref != Twine::Null);
// 	return addCell(name, tref);
// }

Cell* Patch::addCell(TwineRef name, Twine &&type) {
	return addCell(name, twine_staging.add(std::move(type)));
}

Cell* Patch::addCell(Twine &&name, TwineRef type) {
	return addCell(twine_staging.add(std::move(name)), type);
}

Wire* Patch::addWire(TwineRef name, int width) {
	wires_.push_back(std::make_unique<Wire>(Wire::ConstructToken{}));

	Wire* wire = wires_.back().get();
	staged_wire_names_[wire] = name;
	wire->width = width;
	wire->module = nullptr;
	return wire;
}

Wire* Patch::addWire(Twine &&name, int width) {
	return addWire(twine_staging.add(std::move(name)), width);
}

// TODO code golf

RTLIL::Wire *RTLIL::Patch::addWire(TwineRef name, const RTLIL::Wire *other)
{
	RTLIL::Wire *wire = addWire(name);
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

RTLIL::Wire *RTLIL::Patch::addWire(Twine &&name, const RTLIL::Wire *other)
{
	return addWire(twine_staging.add(std::move(name)), other);
}

TwineRef Patch::new_name(const std::string *prefix) {
	TwineRef pref;
	if (auto it = staged_prefix_cache_.find(prefix); it != staged_prefix_cache_.end())
		pref = it->second;
	else
		pref = staged_prefix_cache_[prefix] = twine_staging.add(Twine{*prefix});
	return twine_staging.add(Twine{Twine::Suffix{pref, std::to_string(autoidx++)}});
}

Wire* Patch::commit_wire(std::unique_ptr<Wire> wire) {
	Wire* raw = wire.release();
	TwineRef id = twine_staging.resolve(staged_wire_names_.at(raw));
	staged_wire_names_.erase(raw);
	if (!raw->meta_)
		raw->meta_ = mod->design->alloc_obj_meta();
	raw->meta_->name = id;
	mod->wires_[raw->meta_->name] = raw;
	raw->module = mod;
	return raw;
}

Cell* Patch::commit_cell(std::unique_ptr<Cell> cell) {
	Cell* raw = cell.release();
	TwineRef id = twine_staging.resolve(staged_cell_names_.at(raw));
	staged_cell_names_.erase(raw);
	if (!raw->meta_)
		raw->meta_ = mod->design->alloc_obj_meta();
	raw->meta_->name = id;
	raw->module = mod;
	mod->cells_[raw->meta_->name] = raw;
	if (auto it = staged_cell_src_.find(raw); it != staged_cell_src_.end()) {
		raw->set_src_attribute(twine_staging.resolve(it->second));
		staged_cell_src_.erase(it);
	}
	raw->initIndex();
	return raw;
}

std::vector<Cell*> Patch::commit_staged() {
	twine_staging.commit_into(mod->design->twines);
	staged_prefix_cache_.clear();
	std::vector<Cell*> committed;
	committed.reserve(cells_.size());
	for (auto& cell : cells_) {
		cell->fixup_parameters();
		committed.push_back(commit_cell(std::move(cell)));
	}
	for (auto& wire : wires_)
		commit_wire(std::move(wire));
	cells_.clear();
	wires_.clear();
	return committed;
}

namespace {
	std::string port_name(Cell* cell, TwineRef port) {
		if (cell->module && cell->module->design)
			return cell->module->design->twines.str(port);
		return "<port#" + std::to_string(port) + ">";
	}

	void apply_src(Module* mod, Cell* root, const std::vector<Cell*>& extras,
			const std::vector<Cell*>& targets, Cell* merge_src_into)
	{
		// Without a design there's no pool — the cells can't carry typed
		// src, so silently drop merge-of-src in that path.
		if (!mod || !mod->design)
			return;

		TwinePool& pool = mod->design->twines;
		std::vector<TwineRef> ids;
		ids.reserve(2 + extras.size());
		auto push = [&](Cell *c) {
			if (c && c->src_id() != Twine::Null)
				ids.push_back(c->src_id());
		};
		push(root);
		for (Cell *c : extras)
			push(c);
		push(merge_src_into);
		if (ids.empty())
			return;
		TwineRef merged = ids.size() == 1 ? ids[0] : pool.add(Twine{std::move(ids)});
		if (ys_debug()) {
			log_debug("twine: merge yields %s (pool size %zu)\n",
					pool.str(merged).c_str(), pool.backing.size());
			if (ys_debug(2))
				pool.dump();
		}
		for (Cell* c : targets)
			c->set_src_id(merged);
		if (merge_src_into)
			merge_src_into->set_src_id(merged);
	}

	// Verifies via newcelltypes that root_cell has exactly one output port
	// and that it matches `expected_port`.
	void assert_single_output(Cell* root_cell, TwineRef expected_port) {
		int count = 0;
		TwineRef found = Twine::Null;
		for (auto &[port, sig] : root_cell->connections()) {
			if (root_cell->output(port)) {
				found = port;
				count++;
			}
		}
		if (count != 1)
			log_error("Patch: cell %s of type %s has %d output ports, expected exactly one\n",
					log_id(root_cell->name), log_id(root_cell->type), count);
		if (found != expected_port)
			log_error("Patch: cell %s of type %s sole output port %s does not match patched port %s\n",
					log_id(root_cell->name), log_id(root_cell->type),
					port_name(root_cell, found).c_str(), port_name(root_cell, expected_port).c_str());
	}
}

void Patch::patch(Cell* root_cell, TwineRef old_port, SigSpec new_sig,
		const std::vector<Cell*>& extras, Cell* merge_src_into)
{
	assert_single_output(root_cell, old_port);

	SigSpec old_sig = root_cell->getPort(old_port);
	if (old_sig.size() != new_sig.size())
		log_error("patch size mismatch on cell %s port %s: old %d (%s) vs new %d (%s)\n",
				log_id(root_cell->name), port_name(root_cell, old_port).c_str(),
				old_sig.size(), log_signal(old_sig),
				new_sig.size(), log_signal(new_sig));
	log_debug("patching %s %s which is %s with %s\n",
			log_id(root_cell->name), port_name(root_cell, old_port).c_str(),
			log_signal(old_sig), log_signal(new_sig));

	std::vector<Cell*> committed = commit_staged();
	apply_src(mod, root_cell, extras, committed, merge_src_into);

	// Drop root_cell's driver on the output port BEFORE wiring old_sig to
	// new_sig — otherwise old_sig would briefly have two drivers (root_cell
	// and new_sig) which signorm flags as conflicting.
	root_cell->unsetPort(old_port);

	if (map)
		map->add(old_sig, new_sig);
	mod->connect_incremental(old_sig, new_sig);

	// Remove root cell only — no input-cone walk.
	mod->remove(root_cell);
}

void Patch::patch_ports(Cell* root_cell,
		const std::vector<std::pair<TwineRef, SigSpec>>& port_replacements,
		const std::vector<Cell*>& extras, Cell* merge_src_into)
{
	// Verify each listed port is an output of root_cell and that the
	// replacements cover every output port of root_cell.
	pool<TwineRef> listed;
	std::vector<SigSpec> old_sigs;
	old_sigs.reserve(port_replacements.size());
	for (auto &[port, new_sig] : port_replacements) {
		if (!root_cell->output(port))
			log_error("patch_ports: cell %s of type %s port %s is not an output\n",
					log_id(root_cell->name), log_id(root_cell->type), port_name(root_cell, port).c_str());
		SigSpec old_sig = root_cell->getPort(port);
		if (old_sig.size() != new_sig.size())
			log_error("patch_ports size mismatch on cell %s port %s: old %d (%s) vs new %d (%s)\n",
					log_id(root_cell->name), port_name(root_cell, port).c_str(),
					old_sig.size(), log_signal(old_sig),
					new_sig.size(), log_signal(new_sig));
		listed.insert(port);
		old_sigs.push_back(old_sig);
	}
	for (auto &[port, sig] : root_cell->connections())
		if (root_cell->output(port) && !listed.count(port))
			log_error("patch_ports: cell %s of type %s has output port %s not in port_replacements\n",
					log_id(root_cell->name), log_id(root_cell->type), port_name(root_cell, port).c_str());

	std::vector<Cell*> committed = commit_staged();
	apply_src(mod, root_cell, extras, committed, merge_src_into);

	// Drop every port (inputs included) so root_cell becomes a disconnected
	// shell before we wire old_sigs to new_sigs. Doing this first ensures
	// the old port signals are not briefly double-driven by root_cell and
	// the new connection.
	std::vector<TwineRef> all_ports;
	all_ports.reserve(root_cell->connections().size());
	for (auto &[port, sig] : root_cell->connections())
		all_ports.push_back(port);
	for (auto port : all_ports)
		root_cell->unsetPort(port);
	log_assert(root_cell->connections().empty());

	for (size_t i = 0; i < port_replacements.size(); i++) {
		auto &[port, new_sig] = port_replacements[i];
		if (map)
			map->add(old_sigs[i], new_sig);
		mod->connect_incremental(old_sigs[i], new_sig);
	}

	mod->remove(root_cell);
}

void Patch::commit_inheriting_src(Cell* src_source) {
	twine_staging.commit_into(mod->design->twines);
	staged_prefix_cache_.clear();
	for (auto& cell : cells_) {
		cell->fixup_parameters();
		Cell *committed = commit_cell(std::move(cell));
		// commit_cell attaches the cell to mod, so adopt_src_from can
		// now resolve the pool via committed->module->design. Direct
		// id transfer — no flatten/re-intern detour.
		if (src_source)
			committed->adopt_src_from(src_source);
	}
	for (auto& wire : wires_)
		commit_wire(std::move(wire));
	cells_.clear();
	wires_.clear();
}

YOSYS_NAMESPACE_END
