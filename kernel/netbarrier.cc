// BarrierWriter puts $barrier cells at the objects of the refs, their
// anchors are in the barrier store by the barrier id in their name, barriers at:
//   Pin       the leaf pin, or the port inside a hierarchical pin
//   Instance  each pin of a gate, the clock pins of a register
//   TopPort   a bit of a top bus port
//   Net       the leaf drivers
// A barrier cuts a pin off its net with a cut wire

#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

pool<const RTLIL::Cell *> NetTracker::barrierInstances(RTLIL::Design *design) const
{
	pool<const RTLIL::Cell *> barriers;
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells()) {
			if (cell->type == ID($barrier) && data_->barriers.marks(cell).keep_as_instance)
				barriers.insert(cell);
		}
	}
	return barriers;
}

int detail::BarrierStore::nextId() { return ++last_barrier_id; }

detail::BarrierMarks detail::BarrierStore::marks(const RTLIL::Cell *barrier) const
{
	std::optional<int> id = detail::barrierIdOf(barrier);
	if (!id)
		return {};
	return marks_by_barrier.at(*id, BarrierMarks());
}

void detail::BarrierStore::setMarks(const RTLIL::Cell *barrier, const BarrierMarks &marks)
{
	if (std::optional<int> id = detail::barrierIdOf(barrier))
		marks_by_barrier[*id] = marks;
}

RTLIL::IdString detail::BarrierStore::cutPort(const RTLIL::Cell *barrier) const
{
	if (marks(barrier).cut_on_a)
		return ID::A;
	return ID::Y;
}

void detail::BarrierStore::clearAnchors() { anchors_by_barrier.clear(); }

detail::BarrierWriter::BarrierWriter(const NetView &view, TrackData &data) : view_(view), data_(data)
{
	for (RTLIL::Module *module : view.design()->modules()) {
		if (view.scopes(module).empty())
			continue;
		for (RTLIL::Cell *cell : module->cells()) {
			if (cell->type == ID($barrier) && detail::barrierIdOf(cell))
				barrier_by_cut_bit_[cell->getPort(data.barriers.cutPort(cell))[0]] = cell;
		}
	}
}

void detail::BarrierWriter::protect(uint32_t ref_index, const TrackedRef &ref, size_t at)
{
	switch (ref.kind) {
	case TrackedRef::Kind::Pin:
		return protectPin(ref.pins[at], ref_index, ref);
	case TrackedRef::Kind::TopPort:
		return protectPort(ref.pins[at], ref_index);
	case TrackedRef::Kind::Instance:
		return protectCell(ref.instances[at], ref_index);
	case TrackedRef::Kind::Net:
		return protectNet(ref.nets[at], ref_index);
	}
}

bool detail::BarrierWriter::madeNewBarrierInstance() const { return made_new_barrier_instance_; }

void detail::BarrierWriter::protectPin(const Netlist::Pin *pin, uint32_t ref_index, const TrackedRef &ref)
{
	if (pin->inst->isTop())
		return;
	int outputs = 0;
	for (const Netlist::Pin *other : pin->inst->pins)
		outputs += other->isDriver();
	// Every path from an input of a cell with one output passes that output
	if (pin->inst->isLeaf() && ref.hints.keep_cell && outputs > 1)
		isolateCell(pin->inst);
	if (pin->inst->isLeaf())
		return protectLeafPin(pin, ref_index);
	protectHierPin(pin, ref_index, ref.hints.keep_as_instance);
}

// A driver also cuts its first input, so opt_merge merges no cell into it
void detail::BarrierWriter::protectLeafPin(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path)
{
	anchorPinBarrier(pin, ref_index, net_scope_path);
	if (!pin->isDriver())
		return;
	for (const Netlist::Pin *input : pin->inst->pins) {
		if (!input->isDriver()) {
			ensureBarrierAtPin(input);
			return;
		}
	}
}

void detail::BarrierWriter::protectHierPin(const Netlist::Pin *pin, uint32_t ref_index, bool keep_as_instance)
{
	RTLIL::Cell *barrier = ensureBarrierAtPort(pin);
	if (barrier == nullptr)
		return;
	BarrierMarks marks = data_.barriers.marks(barrier);
	if (keep_as_instance && !marks.keep_as_instance) {
		marks.keep_as_instance = true;
		data_.barriers.setMarks(barrier, marks);
		made_new_barrier_instance_ = true;
	}
	Anchor::Side cut_side = Anchor::Side::A;
	if (pin->dir() == Netlist::PortDir::Input)
		cut_side = Anchor::Side::Y;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", pin->port().name, pin->bit, "", false, cut_side};
	detail::recordBarrierAnchor(view_, data_.barriers, barrier, data_.snapshot.scopePath(view_, pin->inst), anchor);
}

void detail::BarrierWriter::protectPort(const Netlist::Pin *pin, uint32_t ref_index)
{
	const Netlist::Port &port = pin->port();
	if (port.scalar())
		return;
	RTLIL::Cell *barrier = ensureBarrierAtPort(pin);
	if (barrier == nullptr)
		return;
	Anchor::Side cut_side = Anchor::Side::Y;
	if (port.dir == Netlist::PortDir::Input)
		cut_side = Anchor::Side::A;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", port.name, pin->bit, "", false, cut_side};
	detail::recordBarrierAnchor(view_, data_.barriers, barrier, "", anchor);
}

void detail::BarrierWriter::protectCell(const Netlist::Instance *inst, uint32_t ref_index)
{
	if (inst->isLeaf() && view_.isRegister(inst)) {
		detail::setOwnedAttribute(view_.design(), view_.cell(inst), ID::keep);
		for (const Netlist::Pin *pin : inst->pins) {
			if (view_.isClockPin(pin))
				anchorPinBarrier(pin, ref_index);
		}
		return;
	}
	if (inst->isLeaf()) {
		isolateCell(inst);
		for (const Netlist::Pin *pin : inst->pins)
			anchorPinBarrier(pin, ref_index);
		return;
	}
	detail::setOwnedAttribute(view_.design(), view_.cell(inst), ID::keep_hierarchy);
}

void detail::BarrierWriter::protectNet(const Netlist::Net *net, uint32_t ref_index)
{
	markWiresKeep(net);
	pool<const Netlist::Net *> seen;
	std::vector<const Netlist::Pin *> drivers;
	collectLeafDrivers(net, seen, drivers);
	std::string path = data_.snapshot.scopePath(view_, net->scope);
	for (const Netlist::Pin *pin : drivers)
		protectLeafPin(pin, ref_index, path);
}

void detail::BarrierWriter::isolateCell(const Netlist::Instance *inst)
{
	detail::setOwnedAttribute(view_.design(), view_.cell(inst), ID::keep);
	for (const Netlist::Pin *pin : inst->pins)
		ensureBarrierAtPin(pin);
}

void detail::BarrierWriter::anchorPinBarrier(const Netlist::Pin *pin, uint32_t ref_index, const std::string &net_scope_path)
{
	RTLIL::Cell *barrier = ensureBarrierAtPin(pin);
	if (barrier == nullptr)
		return;
	Anchor::Side cut_side = Anchor::Side::Y;
	if (pin->isDriver())
		cut_side = Anchor::Side::A;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", pin->port().name, pin->bit, net_scope_path, false, cut_side};
	detail::recordBarrierAnchor(view_, data_.barriers, barrier, data_.snapshot.scopePath(view_, pin->inst->parent), anchor);
}

RTLIL::Cell *detail::BarrierWriter::ensureBarrierAtPin(const Netlist::Pin *pin)
{
	RTLIL::Cell *cell = view_.cell(pin->inst);
	RTLIL::IdString port = detail::escapedPortId(view_.design(), cell, nullptr, pin->port().name);
	if (cell == nullptr || !cell->hasPort(port) || pin->bit >= GetSize(cell->getPort(port)))
		return nullptr;
	RTLIL::SigSpec sig = cell->getPort(port);
	RTLIL::SigBit bit = sig[pin->bit];
	if (bit.wire == nullptr)
		return nullptr;
	// A port cut holds all uses of the bit, the pin takes its own barrier
	RTLIL::Cell *existing = barrier_by_cut_bit_.at(bit, nullptr);
	bool port_cut = existing != nullptr && data_.barriers.marks(existing).port_cut;
	if (detail::isCutWire(bit.wire) && !port_cut)
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(cell->module);
	RTLIL::Cell *barrier;
	if (pin->isDriver())
		barrier = createBarrierCell(cell->module, cut, bit, {.cut_on_a = true});
	else
		barrier = createBarrierCell(cell->module, bit, cut, {});
	sig[pin->bit] = cut;
	cell->setPort(port, sig);
	barrier_by_cut_bit_[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

RTLIL::Cell *detail::BarrierWriter::ensureBarrierAtPort(const Netlist::Pin *pin)
{
	RTLIL::Module *module = view_.module(pin->inst);
	if (module == nullptr)
		return nullptr;
	RTLIL::Wire *wire = module->wire(detail::escapedPortId(view_.design(), nullptr, module, pin->port().name));
	if (wire == nullptr || pin->bit >= wire->width || wire->port_input == wire->port_output)
		return nullptr;
	RTLIL::SigBit bit(wire, pin->bit);
	if (RTLIL::Cell *existing = findPortBarrier(module, bit))
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(module);
	detail::replaceBitInModule(module, bit, cut);
	RTLIL::Cell *barrier;
	if (wire->port_input)
		barrier = createBarrierCell(module, bit, cut, {.port_cut = true});
	else
		barrier = createBarrierCell(module, cut, bit, {.cut_on_a = true, .port_cut = true});
	barrier_by_cut_bit_[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

RTLIL::Cell *detail::BarrierWriter::findPortBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const
{
	Netlist::WalkTarget target = Netlist::WalkTarget::Loads;
	if (bit.wire->port_input)
		target = Netlist::WalkTarget::Drivers;
	RTLIL::IdString port = detail::barrierPortToward(target);
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type == ID($barrier) && data_.barriers.marks(cell).port_cut && cell->getPort(port) == RTLIL::SigSpec(bit))
			return cell;
	}
	return nullptr;
}

RTLIL::Cell *detail::BarrierWriter::createBarrierCell(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y, const BarrierMarks &marks)
{
	int id = data_.barriers.nextId();
	RTLIL::IdString name = module->twines().add(stringf("\\%s$%d", detail::anchor_prefix, id));
	RTLIL::Cell *barrier = module->addCell(name, ID($barrier));
	barrier->set_bool_attribute(ID::keep);
	detail::ensureScopename(barrier);
	barrier->attributes[detail::attrId(view_.design(), detail::anchor_attr, IdLookup::AddIfMissing)] = RTLIL::Const(id);
	barrier->setParam(ID::WIDTH, 1);
	barrier->setPort(ID::A, a);
	barrier->setPort(ID::Y, y);
	data_.barriers.marks_by_barrier[id] = marks;
	return barrier;
}

// Only one-bit wires, keep on a wide wire would hold its other bits too
void detail::BarrierWriter::markWiresKeep(const Netlist::Net *net)
{
	for (const RTLIL::SigBit &bit : view_.wireBits(net)) {
		if (bit.wire->width == 1 && !detail::isCutWire(bit.wire))
			detail::setOwnedAttribute(view_.design(), bit.wire, ID::keep);
	}
}

void detail::BarrierWriter::collectLeafDrivers(const Netlist::Net *net, pool<const Netlist::Net *> &seen, std::vector<const Netlist::Pin *> &drivers) const
{
	if (net == nullptr || !seen.insert(net).second)
		return;
	for (const Netlist::Pin *pin : net->pins) {
		if (pin->inst->isLeaf() && pin->isDriver())
			drivers.push_back(pin);
		else if (!pin->inst->isLeaf() && pin->term != nullptr)
			collectLeafDrivers(pin->term->net, seen, drivers);
	}
	for (const Netlist::Term *term : net->terms)
		collectLeafDrivers(term->pin->net, seen, drivers);
}

// netview_<attr> marks our attr
RTLIL::IdString detail::ownedMarkerId(RTLIL::Design *design, RTLIL::IdString attr, IdLookup lookup)
{
	std::string name = std::string(detail::owned_marker_prefix) + detail::unescapedName({design, attr});
	return detail::attrId(design, name, lookup);
}

void detail::setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr)
{
	if (object->get_bool_attribute(attr))
		return;
	object->set_bool_attribute(attr);
	object->set_bool_attribute(detail::ownedMarkerId(design, attr, IdLookup::AddIfMissing));
}

RTLIL::Wire *detail::addCutWire(RTLIL::Module *module)
{
	RTLIL::Wire *cut = module->addWire(NEW_ID);
	cut->set_bool_attribute(detail::attrId(module->design, detail::cut_attr, IdLookup::AddIfMissing));
	return cut;
}

// The attribute (rename -hide renames the barrier), else the name (abc9 renews it without attributes lol)
std::optional<int> detail::barrierIdOf(const RTLIL::Cell *barrier)
{
	RTLIL::IdString id = detail::attrId(barrier->module->design, detail::anchor_attr, IdLookup::FindOnly);
	if (barrier->has_attribute(id))
		return barrier->attributes.at(id).as_int();
	std::string marker = std::string(detail::anchor_prefix) + "$";
	std::string text = barrier->name.str();
	size_t at = text.find(marker);
	if (at == std::string::npos)
		return std::nullopt;
	return atoi(text.c_str() + at + marker.size());
}

void detail::recordBarrierAnchor(const NetView &view, BarrierStore &barriers, const RTLIL::Cell *barrier, const std::string &path, Anchor anchor)
{
	std::optional<int> id = detail::barrierIdOf(barrier);
	if (!id)
		return;
	anchor.scope_path = detail::barrierScopePath(path, barrier);
	anchor.in_shared_module = view.scopes(barrier->module).size() > 1;
	barriers.anchors_by_barrier.add(*id, anchor);
}

void detail::replaceBitInModule(RTLIL::Module *module, const RTLIL::SigBit &bit, const RTLIL::SigBit &other)
{
	for (RTLIL::Cell *cell : module->cells()) {
		std::vector<std::pair<RTLIL::IdString, RTLIL::SigSpec>> changed;
		for (const auto &[port, sig] : cell->connections()) {
			RTLIL::SigSpec next = sig;
			next.replace(bit, other);
			if (next != sig)
				changed.emplace_back(port, next);
		}
		for (const auto &[port, sig] : changed)
			cell->setPort(port, sig);
	}
	std::vector<RTLIL::SigSig> connections = module->connections();
	for (auto &[lhs, rhs] : connections) {
		lhs.replace(bit, other);
		rhs.replace(bit, other);
	}
	module->new_connections(connections);
}

RTLIL::IdString detail::barrierPortToward(Netlist::WalkTarget target)
{
	if (target == Netlist::WalkTarget::Drivers)
		return ID::A;
	return ID::Y;
}

// abc9 renews this as <prefix><anchor prefix>$<id>.bit[0].b
std::string detail::barrierScopePath(const std::string &path, const RTLIL::Cell *barrier)
{
	if (detail::hasOwnScope(barrier))
		return detail::withOwnScope(path, barrier);
	std::string name = barrier->name.str();
	std::string own = name.substr(1, name.find(std::string(detail::anchor_prefix) + "$") - 1);
	if (!own.empty())
		own.pop_back();
	std::replace(own.begin(), own.end(), '.', '/');
	return Netlist::joinPath({path, own});
}

YOSYS_NAMESPACE_END
