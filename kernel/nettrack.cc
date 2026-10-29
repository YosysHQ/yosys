#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

bool TrackedRef::Origin::isHierarchicalPin() const { return hier_pin_dir != Netlist::PortDir::Unknown; }

bool TrackedRef::removedButLoadsKept() const { return kind == Kind::Instance && instances.empty() && !result.loads_beyond.empty(); }

NetTracker::NetTracker() : data_(std::make_unique<detail::TrackData>()) {}

NetTracker::~NetTracker() = default;

void NetTracker::checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, TrackMode mode)
{
	log_assert(view.upToDate());
	detail::TrackData &data = *data_;
	data.clearAnchors(view.design());
	data.snapshot.take(view);
	detail::CutSideWalker walker(view, data);
	detail::AnchorWriter anchors(view, data, walker);
	detail::BarrierWriter barriers(view, data);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++) {
		TrackedRef &ref = *refs[ref_index];
		for (size_t at = 0; at < detail::objectCount(ref); at++) {
			anchors.write(ref_index, ref, at, mode);
			if (mode == TrackMode::Barriers)
				barriers.protect(ref_index, ref, at);
		}
	}
	if (mode == TrackMode::Barriers && !barriers.madeNewBarrierInstance())
		view.markUpToDate();
}

void NetTracker::clear(RTLIL::Design *design) { data_->clearAnchors(design); }

size_t detail::objectCount(const TrackedRef &ref)
{
	switch (ref.kind) {
	case TrackedRef::Kind::Pin:
	case TrackedRef::Kind::TopPort:
		return ref.pins.size();
	case TrackedRef::Kind::Instance:
		return ref.instances.size();
	case TrackedRef::Kind::Net:
		return ref.nets.size();
	}
	return 0;
}

void detail::TrackData::clearAnchors(RTLIL::Design *design)
{
	anchors.clear();
	barriers.clearAnchors();
	top_ports_by_ref.clear();
	RTLIL::IdString id = detail::refAttrId(design, IdLookup::FindOnly);
	if (id == RTLIL::IdString::Null)
		return;
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells())
			cell->attributes.erase(id);
		for (RTLIL::Wire *wire : module->wires())
			wire->attributes.erase(id);
	}
}

void detail::Snapshot::take(const NetView &view)
{
	clear();
	takeScope(view, view.top());
}

void detail::Snapshot::takeScope(const NetView &view, const Netlist::Instance *scope)
{
	for (const Netlist::Instance *child : scope->children) {
		cell_names[view.cell(child)->hashidx_] = child->localName();
		cell_paths.insert(scopePath(view, child));
		takeScope(view, child);
	}
}

void detail::Snapshot::clear()
{
	cell_names.clear();
	cell_paths.clear();
}

std::string detail::Snapshot::scopePath(const NetView &view, const Netlist::Instance *scope) const
{
	if (scope == nullptr || scope->parent == nullptr)
		return "";
	std::string own = cell_names.at(view.cell(scope)->hashidx_, scope->localName());
	return Netlist::joinPath({scopePath(view, scope->parent), own});
}

std::string detail::Snapshot::cellScopePath(const NetView &view, const Netlist::Instance *inst) const
{
	const RTLIL::Cell *cell = view.cell(inst);
	if (detail::hasOwnScope(cell) || inst->hdlpath.size() < 2)
		return detail::withOwnScope(scopePath(view, inst->parent), cell);
	std::vector<std::string> own(inst->hdlpath.begin(), inst->hdlpath.end() - 1);
	return Netlist::joinPath({scopePath(view, inst->parent), Netlist::joinPath(own)});
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

void detail::AnchorStore::clear() { anchors_by_ref_attr.clear(); }

detail::AnchorWriter::AnchorWriter(const NetView &view, TrackData &data, CutSideWalker &walker) : view_(view), data_(data), walker_(walker) {}

void detail::AnchorWriter::write(uint32_t ref_index, TrackedRef &ref, size_t at, TrackMode mode)
{
	switch (ref.kind) {
	case TrackedRef::Kind::Net:
		return anchorWires(ref.nets[at], ref_index);
	case TrackedRef::Kind::Instance: {
		const Netlist::Instance *inst = ref.instances[at];
		return anchorCell(inst, {Anchor::Role::Cell, ref_index, data_.snapshot.cellScopePath(view_, inst), "", 0, "", false});
	}
	case TrackedRef::Kind::TopPort:
		data_.top_ports_by_ref.add(ref_index, {ref.pins[at]->port().name, ref.pins[at]->hdlIndex()});
		return anchorPin(ref.pins[at], ref_index, ref, mode);
	case TrackedRef::Kind::Pin:
		return anchorPin(ref.pins[at], ref_index, ref, mode);
	}
}

void detail::AnchorWriter::anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, TrackMode mode)
{
	if (pin->inst->isTop()) {
		if (pin->term != nullptr)
			anchorWires(pin->term->net, ref_index);
		return;
	}
	if (pin->inst->kind == Netlist::Instance::Kind::Barrier)
		return anchorBarrierInstancePin(pin, ref_index, ref, mode);
	if (!pin->inst->isLeaf()) {
		ref.origin.hier_pin_dir = Netlist::PortDir::Input;
		if (pin->dir() == Netlist::PortDir::Output)
			ref.origin.hier_pin_dir = Netlist::PortDir::Output;
	}
	Anchor anchor = {Anchor::Role::Pin, ref_index, data_.snapshot.cellScopePath(view_, pin->inst), pin->port().name, pin->bit, "", false};
	anchorCell(pin->inst, anchor);
}

void detail::AnchorWriter::anchorBarrierInstancePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, TrackMode mode)
{
	ref.origin.on_barrier_instance = true;
	if (mode == TrackMode::AnchorsOnly)
		return anchorDriversOfBarrierInstance(pin, ref_index, ref);
	Anchor anchor = {Anchor::Role::Pin, ref_index, "", pin->port().name, pin->bit, "", false, Anchor::Side::Y};
	std::string path = data_.snapshot.scopePath(view_, pin->inst->parent);
	detail::recordBarrierAnchor(view_, data_.barriers, view_.cell(pin->inst), path, anchor);
}

// unprotect removes the Barrier instance, a ref of its A pin moves to the drivers, a ref of its Y pin takes no anchor
void detail::AnchorWriter::anchorDriversOfBarrierInstance(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref)
{
	if (pin->dir() != Netlist::PortDir::Input)
		return;
	std::vector<const Netlist::Pin *> drivers;
	walker_.pins(view_.cell(pin->inst), pin->inst->parent, Anchor::Side::A, BufferRule::StopAtNewBuffer, drivers);
	for (const Netlist::Pin *driver : drivers)
		anchorPin(driver, ref_index, ref, TrackMode::AnchorsOnly);
	ref.origin.anchored_on_drivers = !drivers.empty();
}

void detail::AnchorWriter::anchorCell(const Netlist::Instance *inst, Anchor anchor)
{
	RTLIL::Cell *cell = view_.cell(inst);
	anchor.in_shared_module = markIfShared(cell, cell->module);
	data_.anchors.append(view_.design(), cell, anchor);
}

void detail::AnchorWriter::anchorWires(const Netlist::Net *net, uint32_t ref_index)
{
	if (net == nullptr || net->constant != Netlist::Net::Const::None)
		return;
	std::string path = data_.snapshot.scopePath(view_, net->scope);
	for (const RTLIL::SigBit &bit : view_.wireBits(net)) {
		bool shared = markIfShared(bit.wire, bit.wire->module);
		Anchor anchor = {Anchor::Role::Net, ref_index, detail::withOwnScope(path, bit.wire), "", bit.offset, path, shared};
		data_.anchors.append(view_.design(), bit.wire, anchor);
	}
}

bool detail::AnchorWriter::markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module)
{
	if (view_.scopes(module).size() < 2)
		return false;
	detail::ensureScopename(object);
	return true;
}

RTLIL::IdString detail::attrId(RTLIL::Design *design, std::string_view name, IdLookup lookup)
{
	if (lookup == IdLookup::AddIfMissing)
		return design->twines().add(name);
	return design->twines().find(name);
}

RTLIL::IdString detail::refAttrId(RTLIL::Design *design, IdLookup lookup) { return detail::attrId(design, detail::ref_attr, lookup); }

// Without -scopename, flatten extends the 'scopename' of a private object only if it has one
void detail::ensureScopename(RTLIL::AttrObject *object)
{
	if (!detail::hasOwnScope(object))
		object->attributes[ID::scopename] = RTLIL::Const(std::string());
}

bool detail::hasOwnScope(const RTLIL::AttrObject *object) { return object->has_attribute(ID::hdlname) || object->has_attribute(ID::scopename); }

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

std::string detail::withOwnScope(const std::string &path, const RTLIL::AttrObject *object)
{
	return Netlist::joinPath({path, Netlist::joinPath(detail::ownScopeParts(object))});
}

YOSYS_NAMESPACE_END
