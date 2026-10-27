// The epoch end. EpochSnapshot takes the names that ScopePaths reads (R3).
// AnchorWriter puts the anchors of each object into the anchor store, the
// netview_ref attribute of a cell or wire holds the index of its anchors
// there. Roles:
//   Pin      on a cell      ref, scope, port, bit
//   Cell     on a cell      ref, scope
//   Net      on a wire      ref, scope, bit, net scope
//   Barrier  on a $barrier  ref, scope, port, bit, side
//
// BarrierWriter also puts barriers, their anchors are in the barrier store by
// the barrier id in their name. Barriers at:
//   Pin   the leaf pin, or the port inside a hierarchical pin
//   Cell  each pin of a gate, the clock pins of a register
//   Port  a bit of a top bus port
//   Net   the leaf drivers
#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

bool TrackedRef::AnchorFacts::isHierarchicalPin() const
{
	return hier_dir != Netlist::Dir::Unknown;
}

bool detail::BarrierMarks::has(BarrierMark mark) const
{
	return (bits & (1 << int(mark))) != 0;
}

void detail::BarrierMarks::add(BarrierMark mark)
{
	bits |= 1 << int(mark);
}

void NetView::closeEpoch(const std::vector<TrackedRef *> &refs, Protection protection)
{
	log_assert(valid());
	clearAnchors(design_);
	epoch_.snapshot.take(*this, records_.instances);
	detail::AnchorWriter anchors(*this, epoch_, walker_);
	detail::BarrierWriter barriers(*this, epoch_, hit_index_);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++) {
		TrackedRef &ref = *refs[ref_index];
		for (const void *object : ref.objects) {
			anchors.write(object, ref_index, ref, protection);
			if (protection == Protection::Barriers)
				barriers.protect(object, ref_index, ref);
		}
	}
	if (protection == Protection::Barriers && !barriers.madeNewImage())
		watch_.refresh(design_);
}

// abc9 renews a barrier, its old name stays in the new one
void NetView::unprotect(RTLIL::Design *design)
{
	Pass::call(design, stringf("optbarriers -remove t:$barrier n:*%s* %%i", detail::anchor_prefix));
	epoch_.barriers.clearMarks();
	RTLIL::IdString cut = detail::attrId(design, detail::cut_attr, detail::IdLookup::FindOnly);
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Wire *wire : module->wires()) {
			wire->attributes.erase(cut);
			detail::removeOwnedMarks(design, wire);
		}
		for (RTLIL::Cell *cell : module->cells())
			detail::removeOwnedMarks(design, cell);
	}
}

void NetView::clearAnchors(RTLIL::Design *design)
{
	epoch_.anchors.clear();
	epoch_.barriers.clearAnchors();
	RTLIL::IdString id = detail::refAttrId(design, detail::IdLookup::FindOnly);
	if (id == RTLIL::IdString::Null)
		return;
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells())
			cell->attributes.erase(id);
		for (RTLIL::Wire *wire : module->wires())
			wire->attributes.erase(id);
	}
}

void detail::EpochSnapshot::take(const NetView &view, const std::deque<Netlist::Instance> &instances)
{
	clear();
	for (const Netlist::Instance &inst : instances) {
		if (inst.parent == nullptr)
			continue;
		cell_names[view.cell(&inst)->hashidx_] = detail::ownInstanceName(&inst);
	}
}

void detail::EpochSnapshot::clear()
{
	cell_names.clear();
}

void detail::AnchorStore::append(RTLIL::Design *design, RTLIL::AttrObject *object, const Anchor &anchor)
{
	RTLIL::IdString id = detail::refAttrId(design, IdLookup::AddIfMissing);
	if (!object->has_attribute(id)) {
		object->attributes[id] = RTLIL::Const(int(anchors_by_ref_attr.size()));
		anchors_by_ref_attr.emplace_back();
	}
	anchors_by_ref_attr[object->attributes.at(id).as_int()].push_back(anchor);
}

const std::vector<detail::Anchor> &detail::AnchorStore::anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const
{
	static const std::vector<Anchor> none;
	if (anchors_by_ref_attr.empty())
		return none;
	RTLIL::IdString id = detail::refAttrId(design, IdLookup::FindOnly);
	if (!object->has_attribute(id))
		return none;
	size_t index = object->attributes.at(id).as_int();
	if (index >= anchors_by_ref_attr.size())
		return none;
	return anchors_by_ref_attr[index];
}

void detail::AnchorStore::clear()
{
	anchors_by_ref_attr.clear();
}

int detail::BarrierStore::nextId()
{
	return ++last_barrier_id;
}

void detail::BarrierStore::addMark(const RTLIL::Cell *barrier, BarrierMark mark)
{
	if (std::optional<int> id = detail::barrierIdOf(barrier))
		marks_by_barrier[*id].add(mark);
}

bool detail::BarrierStore::hasMark(const RTLIL::Cell *barrier, BarrierMark mark) const
{
	std::optional<int> id = detail::barrierIdOf(barrier);
	if (!id)
		return false;
	return marks_by_barrier.at(*id, BarrierMarks()).has(mark);
}

// The port that holds the cut wire
RTLIL::IdString detail::BarrierStore::cutPort(const RTLIL::Cell *barrier) const
{
	if (hasMark(barrier, BarrierMark::CutOnA))
		return ID::A;
	return ID::Y;
}

void detail::BarrierStore::clearMarks()
{
	marks_by_barrier.clear();
}

void detail::BarrierStore::clearAnchors()
{
	anchors_by_barrier.clear();
}

std::string detail::ScopePaths::scopePath(const Netlist::Instance *scope) const
{
	if (scope == nullptr || scope->parent == nullptr)
		return "";
	std::string own = snapshot.cell_names.at(view.cell(scope)->hashidx_, detail::ownInstanceName(scope));
	return detail::joinScopePath({scopePath(scope->parent), own});
}

std::string detail::ScopePaths::cellScopePath(const Netlist::Instance *inst) const
{
	const RTLIL::Cell *cell = view.cell(inst);
	if (detail::hasOwnScope(cell) || inst->hdlpath.size() < 2)
		return detail::withOwnScope(scopePath(inst->parent), cell);
	std::vector<std::string> own(inst->hdlpath.begin(), inst->hdlpath.end() - 1);
	return detail::joinScopePath({scopePath(inst->parent), detail::joinScopePath(own)});
}

detail::AnchorWriter::AnchorWriter(const NetView &view, EpochEndData &epoch, CutSideWalker &walker)
    : view_(view), epoch_(epoch), walker_(walker), paths_{view, epoch.snapshot}
{
}

void detail::AnchorWriter::write(const void *object, uint32_t ref_index, TrackedRef &ref, Protection protection)
{
	if (ref.kind == TrackedRef::ObjectKind::Net)
		return anchorWires(static_cast<const Netlist::Net *>(object), ref_index);
	if (ref.kind == TrackedRef::ObjectKind::Cell) {
		const Netlist::Instance *inst = static_cast<const Netlist::Instance *>(object);
		return anchorCell(inst, {Anchor::Role::Cell, ref_index, paths_.cellScopePath(inst), "", 0, "", false});
	}
	anchorPin(static_cast<const Netlist::Pin *>(object), ref_index, ref, protection);
}

void detail::AnchorWriter::anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, Protection protection)
{
	if (view_.isTop(pin->inst)) {
		if (pin->term != nullptr)
			anchorWires(pin->term->net, ref_index);
		return;
	}
	if (pin->inst->isImage())
		return anchorImagePin(pin, ref_index, ref, protection);
	if (!pin->inst->isLeaf()) {
		ref.facts.hier_dir = Netlist::Dir::Input;
		if (view_.dir(pin) == Netlist::Dir::Output)
			ref.facts.hier_dir = Netlist::Dir::Output;
	}
	anchorCell(pin->inst, {Anchor::Role::Pin, ref_index, paths_.cellScopePath(pin->inst), view_.shape(pin).name, pin->bit, "", false});
}

void detail::AnchorWriter::anchorImagePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, Protection protection)
{
	ref.facts.is_image_pin = true;
	if (protection == Protection::AnchorsOnly)
		return anchorDriversOfImage(pin, ref_index, ref);
	Anchor anchor = {Anchor::Role::Pin, ref_index, "", view_.shape(pin).name, pin->bit, "", false, Anchor::Side::Y};
	std::string path = paths_.scopePath(pin->inst->parent);
	detail::recordBarrierAnchor(view_, epoch_.barriers, view_.cell(pin->inst), path, anchor);
}

// unprotect removes the image, a ref of its A pin moves to the drivers, a ref
// of its Y pin takes no anchor
void detail::AnchorWriter::anchorDriversOfImage(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref)
{
	if (view_.dir(pin) != Netlist::Dir::Input)
		return;
	std::vector<const void *> drivers;
	walker_.pins(view_.cell(pin->inst), pin->inst->parent, Anchor::Side::A, drivers);
	for (const void *driver : drivers)
		write(driver, ref_index, ref, Protection::AnchorsOnly);
	ref.facts.moved_to_drivers = !drivers.empty();
}

void detail::AnchorWriter::anchorCell(const Netlist::Instance *inst, Anchor anchor)
{
	RTLIL::Cell *cell = view_.cell(inst);
	anchor.in_shared_module = markIfShared(cell, cell->module);
	epoch_.anchors.append(view_.design(), cell, anchor);
}

void detail::AnchorWriter::anchorWires(const Netlist::Net *net, uint32_t ref_index)
{
	if (net == nullptr || net->constant != Netlist::Net::Const::None)
		return;
	std::string path = paths_.scopePath(net->scope);
	for (const RTLIL::SigBit &bit : view_.wireBits(net)) {
		bool shared = markIfShared(bit.wire, bit.wire->module);
		Anchor anchor = {Anchor::Role::Net, ref_index, detail::withOwnScope(path, bit.wire), "", bit.offset, path, shared};
		epoch_.anchors.append(view_.design(), bit.wire, anchor);
	}
}

// An object of a shared module holds the anchors of all its occurrences, and so
// do its flattened copies. The scope picks the own one
bool detail::AnchorWriter::markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module)
{
	if (view_.scopes(module).size() < 2)
		return false;
	detail::ensureScopename(object);
	return true;
}

detail::BarrierWriter::BarrierWriter(const NetView &view, EpochEndData &epoch, HitIndex &hit_index)
    : view_(view), epoch_(epoch), hit_index_(hit_index), paths_{view, epoch.snapshot}
{
}

void detail::BarrierWriter::protect(const void *object, uint32_t ref_index, const TrackedRef &ref)
{
	switch (ref.kind) {
	case TrackedRef::ObjectKind::Pin: return protectPin(static_cast<const Netlist::Pin *>(object), ref_index, ref);
	case TrackedRef::ObjectKind::Port: return protectPort(static_cast<const Netlist::Pin *>(object), ref_index);
	case TrackedRef::ObjectKind::Cell: return protectCell(static_cast<const Netlist::Instance *>(object), ref_index);
	case TrackedRef::ObjectKind::Net: return protectNet(static_cast<const Netlist::Net *>(object), ref_index);
	}
}

bool detail::BarrierWriter::madeNewImage() const
{
	return made_new_image_;
}

void detail::BarrierWriter::protectPin(const Netlist::Pin *pin, uint32_t ref_index, const TrackedRef &ref)
{
	if (view_.isTop(pin->inst))
		return;
	if (pin->inst->isLeaf())
		return protectLeafPin(pin, ref_index);
	protectHierPin(pin, ref_index, ref.request.wants_image);
}

// A driver also cuts its first input, so opt_merge merges no cell into it
void detail::BarrierWriter::protectLeafPin(const Netlist::Pin *pin, uint32_t ref_index)
{
	anchorPinBarrier(pin, ref_index);
	if (!view_.isDriver(pin))
		return;
	for (const Netlist::Pin *input : pin->inst->pins) {
		if (!view_.isDriver(input)) {
			ensureBarrierAtPin(input);
			return;
		}
	}
}

// At the port inside the cell. Its cut side keeps the paths after flatten, an
// image also keeps the pin
void detail::BarrierWriter::protectHierPin(const Netlist::Pin *pin, uint32_t ref_index, bool wants_image)
{
	RTLIL::Cell *barrier = ensureBarrierAtPort(pin);
	if (barrier == nullptr)
		return;
	if (wants_image && !epoch_.barriers.hasMark(barrier, BarrierMark::Image)) {
		epoch_.barriers.addMark(barrier, BarrierMark::Image);
		made_new_image_ = true;
	}
	Anchor::Side cut_side = Anchor::Side::A;
	if (view_.dir(pin) == Netlist::Dir::Input)
		cut_side = Anchor::Side::Y;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", view_.shape(pin).name, pin->bit, "", false, cut_side};
	detail::recordBarrierAnchor(view_, epoch_.barriers, barrier, paths_.scopePath(pin->inst), anchor);
}

void detail::BarrierWriter::protectPort(const Netlist::Pin *pin, uint32_t ref_index)
{
	const Netlist::PortShape &port = view_.shape(pin);
	if (port.scalar())
		return;
	RTLIL::Cell *barrier = ensureBarrierAtPort(pin);
	if (barrier == nullptr)
		return;
	Anchor::Side cut_side = Anchor::Side::Y;
	if (port.dir == Netlist::Dir::Input)
		cut_side = Anchor::Side::A;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", port.name, pin->bit, "", false, cut_side};
	detail::recordBarrierAnchor(view_, epoch_.barriers, barrier, "", anchor);
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
	view_.cell(inst)->set_bool_attribute(ID::keep_hierarchy);
}

void detail::BarrierWriter::protectNet(const Netlist::Net *net, uint32_t ref_index)
{
	markWiresKeep(net);
	pool<const Netlist::Net *> seen;
	std::vector<const Netlist::Pin *> drivers;
	collectLeafDrivers(net, seen, drivers);
	for (const Netlist::Pin *pin : drivers)
		protectLeafPin(pin, ref_index);
}

void detail::BarrierWriter::isolateCell(const Netlist::Instance *inst)
{
	detail::setOwnedAttribute(view_.design(), view_.cell(inst), ID::keep);
	for (const Netlist::Pin *pin : inst->pins)
		ensureBarrierAtPin(pin);
}

void detail::BarrierWriter::anchorPinBarrier(const Netlist::Pin *pin, uint32_t ref_index)
{
	RTLIL::Cell *barrier = ensureBarrierAtPin(pin);
	if (barrier == nullptr)
		return;
	Anchor::Side cut_side = Anchor::Side::Y;
	if (view_.isDriver(pin))
		cut_side = Anchor::Side::A;
	Anchor anchor = {Anchor::Role::Barrier, ref_index, "", view_.shape(pin).name, pin->bit, "", false, cut_side};
	detail::recordBarrierAnchor(view_, epoch_.barriers, barrier, paths_.scopePath(pin->inst->parent), anchor);
}

// A constant stays, the view would see an open input
RTLIL::Cell *detail::BarrierWriter::ensureBarrierAtPin(const Netlist::Pin *pin)
{
	RTLIL::Cell *cell = view_.cell(pin->inst);
	RTLIL::IdString port = detail::escapedPortId(view_.design(), cell, nullptr, view_.shape(pin).name);
	if (cell == nullptr || !cell->hasPort(port) || pin->bit >= GetSize(cell->getPort(port)))
		return nullptr;
	RTLIL::SigSpec sig = cell->getPort(port);
	RTLIL::SigBit bit = sig[pin->bit];
	if (bit.wire == nullptr)
		return nullptr;
	// A port cut holds all uses of the bit, the pin takes its own barrier
	RTLIL::Cell *existing = hit_index_.barrier_by_cut_bit.at(bit, nullptr);
	bool port_cut = existing != nullptr && epoch_.barriers.hasMark(existing, BarrierMark::PortCut);
	if (detail::isCutWire(bit.wire) && !port_cut)
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(cell->module);
	RTLIL::Cell *barrier;
	if (view_.isDriver(pin)) {
		barrier = createBarrierCell(cell->module, cut, bit);
		epoch_.barriers.addMark(barrier, BarrierMark::CutOnA);
	} else {
		barrier = createBarrierCell(cell->module, bit, cut);
	}
	sig[pin->bit] = cut;
	cell->setPort(port, sig);
	hit_index_.barrier_by_cut_bit[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

RTLIL::Cell *detail::BarrierWriter::ensureBarrierAtPort(const Netlist::Pin *pin)
{
	RTLIL::Module *module = view_.module(pin->inst);
	if (module == nullptr)
		return nullptr;
	RTLIL::Wire *wire = module->wire(detail::escapedPortId(view_.design(), nullptr, module, view_.shape(pin).name));
	if (wire == nullptr || pin->bit >= wire->width || wire->port_input == wire->port_output)
		return nullptr;
	RTLIL::SigBit bit(wire, pin->bit);
	if (RTLIL::Cell *existing = findPortBarrier(module, bit))
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(module);
	detail::replaceBitInModule(module, bit, cut);
	RTLIL::Cell *barrier;
	if (wire->port_input) {
		barrier = createBarrierCell(module, bit, cut);
		epoch_.barriers.addMark(barrier, BarrierMark::PortCut);
	} else {
		barrier = createBarrierCell(module, cut, bit);
		epoch_.barriers.addMark(barrier, BarrierMark::PortCut);
		epoch_.barriers.addMark(barrier, BarrierMark::CutOnA);
	}
	hit_index_.barrier_by_cut_bit[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

RTLIL::Cell *detail::BarrierWriter::findPortBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const
{
	WalkTarget target = WalkTarget::Loads;
	if (bit.wire->port_input)
		target = WalkTarget::Drivers;
	RTLIL::IdString port = detail::barrierPortToward(target);
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type == ID($barrier) && epoch_.barriers.hasMark(cell, BarrierMark::PortCut) && cell->getPort(port) == RTLIL::SigSpec(bit))
			return cell;
	}
	return nullptr;
}

RTLIL::Cell *detail::BarrierWriter::createBarrierCell(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y)
{
	int id = epoch_.barriers.nextId();
	RTLIL::IdString name = module->twines().add(stringf("\\%s$%d", detail::anchor_prefix, id));
	RTLIL::Cell *barrier = module->addCell(name, ID($barrier));
	barrier->set_bool_attribute(ID::keep);
	detail::ensureScopename(barrier);
	barrier->attributes[detail::attrId(view_.design(), detail::anchor_attr, IdLookup::AddIfMissing)] = RTLIL::Const(id);
	barrier->setParam(ID::WIDTH, 1);
	barrier->setPort(ID::A, a);
	barrier->setPort(ID::Y, y);
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
		if (pin->inst->isLeaf() && view_.isDriver(pin))
			drivers.push_back(pin);
		else if (!pin->inst->isLeaf() && pin->term != nullptr)
			collectLeafDrivers(pin->term->net, seen, drivers);
	}
	for (const Netlist::Term *term : net->terms)
		collectLeafDrivers(term->pin->net, seen, drivers);
}

RTLIL::IdString detail::attrId(RTLIL::Design *design, std::string_view name, IdLookup lookup)
{
	if (lookup == IdLookup::AddIfMissing)
		return design->twines().add(name);
	return design->twines().find(name);
}

RTLIL::IdString detail::refAttrId(RTLIL::Design *design, IdLookup lookup)
{
	return detail::attrId(design, detail::ref_attr, lookup);
}

// netview_<attr> marks our attr, removeOwnedMarks removes only that one
RTLIL::IdString detail::ownedMarkerId(RTLIL::Design *design, RTLIL::IdString attr, IdLookup lookup)
{
	std::string name = std::string(detail::owned_marker_prefix) + detail::unescapedName({design, attr});
	return detail::attrId(design, name, lookup);
}

// Without -scopename, flatten extends the 'scopename' of a private object only if it has one
void detail::ensureScopename(RTLIL::AttrObject *object)
{
	if (!detail::hasOwnScope(object))
		object->attributes[ID::scopename] = RTLIL::Const(std::string());
}

void detail::setOwnedAttribute(RTLIL::Design *design, RTLIL::AttrObject *object, RTLIL::IdString attr)
{
	if (object->get_bool_attribute(attr))
		return;
	object->set_bool_attribute(attr);
	object->set_bool_attribute(detail::ownedMarkerId(design, attr, IdLookup::AddIfMissing));
}

void detail::removeOwnedMarks(RTLIL::Design *design, RTLIL::AttrObject *object)
{
	RTLIL::IdString marker = detail::ownedMarkerId(design, ID::keep, IdLookup::FindOnly);
	if (object->get_bool_attribute(marker)) {
		object->attributes.erase(ID::keep);
		object->attributes.erase(marker);
	}
	if (object->has_attribute(ID::scopename) && object->get_string_attribute(ID::scopename).empty())
		object->attributes.erase(ID::scopename);
}

RTLIL::Wire *detail::addCutWire(RTLIL::Module *module)
{
	RTLIL::Wire *cut = module->addWire(NEW_ID);
	cut->set_bool_attribute(detail::attrId(module->design, detail::cut_attr, IdLookup::AddIfMissing));
	return cut;
}

bool detail::isCutWire(const RTLIL::Wire *wire)
{
	return wire->get_bool_attribute(detail::attrId(wire->module->design, detail::cut_attr, IdLookup::FindOnly));
}

// The attribute (rename -hide renames the barrier), else the name (abc9 renews it without attributes)
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

void detail::recordBarrierAnchor(const NetView &view, BarrierStore &barriers, RTLIL::Cell *barrier, const std::string &path, Anchor anchor)
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

bool detail::hasOwnScope(const RTLIL::AttrObject *object)
{
	return object->has_attribute(ID::hdlname) || object->has_attribute(ID::scopename);
}

std::vector<std::string> detail::ownScopeParts(const RTLIL::AttrObject *object)
{
	if (object->has_attribute(ID::hdlname)) {
		std::vector<std::string> parts = object->get_hdlname_attribute();
		if (!parts.empty())
			parts.pop_back();
		return parts;
	}
	return split_tokens(object->get_string_attribute(ID::scopename), " ");
}

std::string detail::joinScopePath(const std::vector<std::string> &parts)
{
	std::string path;
	for (const std::string &part : parts) {
		if (!path.empty() && !part.empty())
			path += "/";
		path += part;
	}
	return path;
}

std::string detail::ownInstanceName(const Netlist::Instance *scope)
{
	if (scope->hdlpath.empty())
		return scope->name;
	return detail::joinScopePath(scope->hdlpath);
}

std::string detail::withOwnScope(const std::string &path, const RTLIL::AttrObject *object)
{
	return detail::joinScopePath({path, detail::joinScopePath(detail::ownScopeParts(object))});
}

// The scopename, else the prefix that flatten put before the name (. or /).
// abc9 renews it as <prefix><anchor prefix>$<id>.bit[0].b
std::string detail::barrierScopePath(const std::string &path, const RTLIL::Cell *barrier)
{
	if (detail::hasOwnScope(barrier))
		return detail::withOwnScope(path, barrier);
	std::string name = barrier->name.str();
	std::string own = name.substr(1, name.find(std::string(detail::anchor_prefix) + "$") - 1);
	if (!own.empty())
		own.pop_back();
	std::replace(own.begin(), own.end(), '.', '/');
	return detail::joinScopePath({path, own});
}

YOSYS_NAMESPACE_END
