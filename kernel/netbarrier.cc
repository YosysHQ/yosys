// barriers of NetTracker, see CheckpointWriter
#include "kernel/nettrack_internal.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

void NetTracker::unprotect(RTLIL::Design *design)
{
	RTLIL::Selection barriers = RTLIL::Selection::EmptySelection(design);
	for (RTLIL::Cell *cell : detail::trackedCells(design)) {
		if (cell->type == ID($barrier))
			barriers.select(cell->module, cell);
	}
	Pass::call_on_selection(design, barriers, "optbarriers -remove");
	detail::removeOwnedKeeps(design);
	RTLIL::IdString cut = design->twines().find(detail::cut_attr);
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Wire *wire : module->wires())
			wire->attributes.erase(cut);
	}
}

// two cells of a module with the same id and hdlname are copies, one gets its own id
detail::CheckpointWriter::CheckpointWriter(const NetView &view, TrackData &data, bool protect)
	: view_(view), data_(data), protect_(protect)
{
	RTLIL::Design *design = view.design();
	tracked_cells_ = detail::trackedCells(design);
	for (RTLIL::Cell *cell : tracked_cells_)
		TrackData::last_id = std::max(TrackData::last_id, *detail::refIdOf(design, cell));
	pool<std::tuple<RTLIL::Module *, int, std::string>> seen_ids;
	pool<RTLIL::Module *> modules;
	for (RTLIL::Cell *cell : tracked_cells_) {
		std::string names = cell->get_string_attribute(ID::hdlname);
		if (!seen_ids.insert({cell->module, *detail::refIdOf(design, cell), names}).second)
			cell->attributes[design->twines().find(detail::ref_attr)] = RTLIL::Const(data.nextId(design));
		if (cell->type != ID($barrier))
			continue;
		barrier_by_cut_bit_[detail::cutBit(cell)] = cell;
		modules.insert(cell->module);
	}
	for (RTLIL::Module *module : modules)
		countCutUsers(module);
}

// the resolve knows the hdlname of each anchored cell, a copy with no anchor must not have its id
void detail::CheckpointWriter::dropUnusedIds()
{
	RTLIL::Design *design = view_.design();
	RTLIL::IdString ref = design->twines().find(detail::ref_attr);
	for (RTLIL::Cell *cell : tracked_cells_) {
		if (anchored_.count(cell))
			continue;
		if (cell->type == ID($barrier))
			cell->attributes[ref] = RTLIL::Const(data_.nextId(design));
		else
			cell->attributes.erase(ref);
	}
}

// a pass can put more pins on a cut wire, see ensureBarrierAtPin
void detail::CheckpointWriter::countCutUsers(RTLIL::Module *module)
{
	SigMap sigmap(module);
	dict<RTLIL::SigBit, RTLIL::SigBit> cut_bit_by_root;
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type == ID($barrier) && detail::refIdOf(module->design, cell))
			cut_bit_by_root[sigmap(detail::cutBit(cell))] = detail::cutBit(cell);
	}
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type == ID($barrier))
			continue;
		for (const auto &[port, sig] : cell->connections()) {
			for (const RTLIL::SigBit &bit : sigmap(sig)) {
				if (cut_bit_by_root.count(bit))
					cut_users_[cut_bit_by_root.at(bit)]++;
			}
		}
	}
}

// the first connected input of a driver stops opt_merge from merging a cell into it
void detail::CheckpointWriter::protectDriver(const Netlist::Pin *pin, uint32_t ref_index)
{
	for (const Netlist::Pin *input : pin->inst->pins) {
		if (input->dir() == RTLIL::PD_INPUT && ensureBarrierAtPin(input, ref_index) != nullptr)
			break;
	}
}

bool detail::CheckpointWriter::cutPin(const Netlist::Pin *pin, uint32_t ref_index)
{
	RTLIL::Cell *barrier = ensureBarrierAtPin(pin, ref_index);
	if (barrier == nullptr) {
		if (pin->dir() == RTLIL::PD_INOUT)
			keepCell(pin->inst); // an inout pin gets no barrier
		return false;
	}
	Anchor anchor = {.role = Anchor::Role::Barrier, .ref_index = ref_index, .port = pin->port().name};
	anchor.hier = !pin->inst->isLeaf();
	anchorIn(pin->inst, barrier, anchor);
	return true;
}

void detail::CheckpointWriter::keepCell(const Netlist::Instance *inst)
{
	detail::setOwnedAttribute(view_.design(), inst->cell, inst->isLeaf() ? ID::keep : ID::keep_hierarchy);
}

void detail::CheckpointWriter::protectCell(const Netlist::Instance *inst, uint32_t ref_index)
{
	if (!protect_)
		return;
	keepCell(inst);
	if (!inst->isLeaf())
		return;
	for (const Netlist::Pin *pin : inst->pins)
		cutPin(pin, ref_index);
}

// anchors the leaf and top port drivers of the net, below the top also the pins that stand in after flatten
void detail::CheckpointWriter::protectNet(const Netlist::Net *net, uint32_t ref_index)
{
	for (const Netlist::Net *connected : detail::connectedNets(net)) {
		for (const Netlist::Pin *pin : connected->pins) {
			if (pin->inst->isLeaf() && pin->isDriver())
				anchorPin(pin, ref_index);
		}
		for (const Netlist::Pin *pin : connected->boundary) {
			if (pin->inst->isTop() && pin->isDriver())
				anchorPin(pin, ref_index);
		}
	}
	if (!net->scope->isTop())
		anchorInnerPins(net, RTLIL::PD_INOUT, ref_index);
}

RTLIL::Cell *detail::CheckpointWriter::ensureBarrierAtPin(const Netlist::Pin *pin, uint32_t ref_index)
{
	RTLIL::Cell *cell = pin->inst->cell;
	RTLIL::IdString port = detail::escapedPortId(view_.design(), pin->inst, pin->port().name);
	if (!cell->hasPort(port) || pin->bit >= GetSize(cell->getPort(port)))
		return nullptr;
	RTLIL::SigSpec sig = cell->getPort(port);
	RTLIL::SigBit bit = sig[pin->bit];
	if (bit.wire == nullptr)
		return nullptr;
	if (pin->dir() == RTLIL::PD_INOUT) {
		data_.open_bits_by_ref.add(ref_index, {bit.wire->name.str(), bit.offset});
		return nullptr;
	}
	bool cut_on_a = pin->dir() == RTLIL::PD_OUTPUT; // a hierarchical output drives its net as a leaf driver does
	// a barrier whose cut wire has more pins stands for all of them, this pin gets its own
	RTLIL::Cell *existing = barrier_by_cut_bit_.at(bit, nullptr);
	if (existing != nullptr && detail::cutOnA(existing) == cut_on_a && cut_users_.at(bit, 1) == 1)
		return existing;
	RTLIL::Cell *barrier = createBarrierCell(cell->module, bit, cut_on_a);
	sig[pin->bit] = detail::cutBit(barrier);
	cell->setPort(port, sig);
	return barrier;
}

RTLIL::Cell *detail::CheckpointWriter::createBarrierCell(RTLIL::Module *module, RTLIL::SigBit bit, bool cut_on_a)
{
	RTLIL::Design *design = view_.design();
	RTLIL::Wire *cut = module->addWire(NEW_ID);
	cut->set_bool_attribute(design->twines().add(detail::cut_attr));
	RTLIL::SigBit a = bit, y = cut;
	if (cut_on_a)
		std::swap(a, y);
	RTLIL::Cell *barrier = module->addBarrier(NEW_ID, a, y);
	barrier->set_bool_attribute(ID::keep);
	barrier->attributes[design->twines().add(detail::ref_attr)] = RTLIL::Const(data_.nextId(design));
	barrier->set_bool_attribute(design->twines().add(detail::cut_on_a_attr), cut_on_a);
	barrier_by_cut_bit_[cut] = barrier;
	return barrier;
}

void detail::setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr)
{
	if (object->get_bool_attribute(attr))
		return;
	object->set_bool_attribute(attr);
	object->set_bool_attribute(design->twines().add(detail::ownedMarkerName(design, attr)));
}

void detail::removeOwnedKeeps(RTLIL::Design *design)
{
	for (RTLIL::IdString attr : {ID::keep, ID::keep_hierarchy}) {
		RTLIL::IdString marker = design->twines().find(detail::ownedMarkerName(design, attr));
		if (marker == RTLIL::IdString::Null)
			continue;
		for (RTLIL::Module *module : design->modules()) {
			for (RTLIL::Cell *cell : module->cells()) { // only a cell gets an owned keep
				if (!cell->get_bool_attribute(marker))
					continue;
				cell->attributes.erase(attr);
				cell->attributes.erase(marker);
			}
		}
	}
}

bool detail::cutOnA(const RTLIL::Cell *barrier)
{
	return barrier->get_bool_attribute(barrier->module->design->twines().find(detail::cut_on_a_attr));
}

RTLIL::SigBit detail::cutBit(const RTLIL::Cell *barrier)
{
	return barrier->getPort(detail::cutOnA(barrier) ? ID::A : ID::Y)[0];
}

std::vector<RTLIL::Cell *> detail::trackedCells(RTLIL::Design *design)
{
	std::vector<RTLIL::Cell *> cells;
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells()) {
			if (detail::refIdOf(design, cell))
				cells.push_back(cell);
		}
	}
	return cells;
}

YOSYS_NAMESPACE_END
