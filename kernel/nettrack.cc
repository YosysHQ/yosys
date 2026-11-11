// checkpoint and clear, CheckpointWriter cuts each ref object, then anchors it
#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

bool TrackedRef::isBehindNewLogic() const
{
	pool<const Netlist::Pin *> own(result.own_pins.begin(), result.own_pins.end());
	return !own.empty() && own != pool<const Netlist::Pin *>(pins.begin(), pins.end());
}

bool TrackedRef::removedButLoadsKept() const
{
	return kind == Kind::Instance && instances.empty() && !result.loads_beyond.empty();
}

NetTracker::NetTracker() : data_(std::make_unique<detail::TrackData>()) {}

NetTracker::~NetTracker() = default;

void NetTracker::checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, bool with_barriers)
{
	detail::TrackData &data = *data_;
	data.bind(view.design());
	data.clearAnchors(view.design());
	if (with_barriers) {
		data.barriers.skipIdsInUse(view.design());
		detail::removeOwnedKeeps(view.design());
	}
	data.snapshot.take(view);
	detail::CheckpointWriter writer(view, data, with_barriers);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		writer.write(ref_index, *refs[ref_index]);
	if (with_barriers && !writer.finishBarriers())
		view.markUpToDate();
}

void NetTracker::clear(RTLIL::Design *design)
{
	data_->bind(design);
	data_->clearAnchors(design);
}

detail::TrackData::TrackData() : serial(++last_serial) { live_serials.insert(serial); }

detail::TrackData::~TrackData() { live_serials.erase(serial); }

void detail::TrackData::bind(RTLIL::Design *design) const
{
	int owner = design->scratchpad_get_int(std::string(detail::tracker_key), 0);
	if (owner != serial && live_serials.count(owner)) {
		const char *reason = "a second tracker would remove its anchors, keeps and barriers";
		log_error("NetTracker: the design has another tracker, %s.\n", reason);
	}
	design->scratchpad_set_int(std::string(detail::tracker_key), serial);
}

void detail::TrackData::clearAnchors(RTLIL::Design *design)
{
	anchors.anchors_by_ref_attr.clear();
	barriers.anchors_by_barrier.clear();
	barriers.used_barriers.clear();
	top_ports_by_ref.clear();
	RTLIL::IdString id = design->twines().find(detail::ref_attr);
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
	*this = Snapshot();
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

std::string detail::Snapshot::scopePath(const NetView &view, const Netlist::Instance *scope) const
{
	if (scope->isTop())
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
	RTLIL::IdString id = design->twines().add(detail::ref_attr);
	if (!object->has_attribute(id) || !anchors_by_ref_attr.count(object->attributes.at(id).as_int()))
		object->attributes[id] = RTLIL::Const(detail::newRefValue(design));
	anchors_by_ref_attr[object->attributes.at(id).as_int()].push_back(anchor);
}

const std::vector<detail::Anchor> &detail::AnchorStore::anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const
{
	static const std::vector<Anchor> none;
	if (anchors_by_ref_attr.empty())
		return none;
	RTLIL::IdString id = design->twines().find(detail::ref_attr);
	if (!object->has_attribute(id))
		return none;
	return anchors_by_ref_attr.at(object->attributes.at(id).as_int(), none);
}

int detail::newRefValue(RTLIL::Design *design)
{
	static int last_value = detail::keySeed(design);
	log_assert(last_value < INT_MAX);
	return ++last_value;
}

// hash of the first design, fixed for the process
// same commands give same values in each run
int detail::keySeed(RTLIL::Design *design)
{
	static std::optional<int> seed;
	if (seed)
		return *seed;
	uint64_t hash = 0;
	for (RTLIL::Module *module : design->modules()) {
		hash += detail::designModuleHash(module);
		for (RTLIL::Cell *cell : module->cells())
			hash += detail::cellHash(cell);
	}
	seed = int(hash >> 34); // 30 bits, 2^30 keys stay free below INT_MAX
	return *seed;
}

void detail::CheckpointWriter::write(uint32_t ref_index, TrackedRef &ref)
{
	switch (ref.kind) {
	case TrackedRef::Kind::Pin:
	case TrackedRef::Kind::TopPort:
		for (const Netlist::Pin *pin : ref.pins)
			anchorPin(pin, ref_index, ref, protectPin(pin, ref_index, ref));
		break;
	case TrackedRef::Kind::Instance:
		for (const Netlist::Instance *inst : ref.instances) {
			log_assert(!inst->isTop());
			if (with_barriers_)
				protectCell(inst, ref_index);
			std::string path = data_.snapshot.cellScopePath(view_, inst);
			anchorCell(inst, {.role = Anchor::Role::Cell, .ref_index = ref_index, .scope_path = path});
		}
		break;
	case TrackedRef::Kind::Net:
		for (const Netlist::Net *net : ref.nets) {
			if (with_barriers_)
				protectNet(net, ref_index);
			anchorWires(net, ref_index);
		}
		break;
	}
}

void detail::CheckpointWriter::anchorPin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref, PinCut cut)
{
	if (pin->inst->isTop()) {
		data_.top_ports_by_ref.add(ref_index, {pin->port().name, pin->hdlIndex()});
		anchorWires(pin->inner, ref_index);
		if (RTLIL::SigBit bit = detail::portBit(view_, pin); bit.wire != nullptr) {
			Anchor port_anchor = {.role = Anchor::Role::Port, .ref_index = ref_index, .bit = bit.offset};
			data_.anchors.append(view_.design(), bit.wire, port_anchor);
		}
		return;
	}
	if (pin->inst->kind == Netlist::Instance::Kind::Barrier)
		return anchorBarrierInstancePin(pin, ref_index, ref);
	if (!pin->inst->isLeaf()) {
		ref.origin.hier_pin_dir = Netlist::PortDir::Input;
		if (pin->dir() == Netlist::PortDir::Output)
			ref.origin.hier_pin_dir = Netlist::PortDir::Output;
	}
	Anchor anchor = {
		.role = Anchor::Role::Pin,
		.ref_index = ref_index,
		.scope_path = data_.snapshot.cellScopePath(view_, pin->inst),
		.port = pin->port().name,
		.bit = pin->bit,
		.uncut = cut == PinCut::Uncut
	};
	anchorCell(pin->inst, anchor);
}

// port wire bit in the instance's module, or empty
RTLIL::SigBit detail::portBit(const NetView &view, const Netlist::Pin *pin)
{
	RTLIL::Module *module = view.module(pin->inst);
	if (module == nullptr)
		return {};
	RTLIL::Wire *wire = module->wire(detail::escapedPortId(view.design(), nullptr, module, pin->port().name));
	if (wire == nullptr || pin->bit >= wire->width)
		return {};
	return {wire, pin->bit};
}

void detail::CheckpointWriter::anchorBarrierInstancePin(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref)
{
	ref.origin.on_barrier_instance = true;
	if (!with_barriers_)
		return anchorDriversOfBarrierInstance(pin, ref_index, ref);
	Anchor anchor = {
		.role = Anchor::Role::Pin,
		.ref_index = ref_index,
		.port = pin->port().name,
		.bit = pin->bit
	};
	std::string path = data_.snapshot.scopePath(view_, pin->inst->parent);
	recordBarrierAnchor(view_.cell(pin->inst), path, anchor);
}

// unprotect removes the Barrier instance, an A pin ref moves to its drivers
// a Y pin ref takes no anchor
void detail::CheckpointWriter::anchorDriversOfBarrierInstance(const Netlist::Pin *pin, uint32_t ref_index, TrackedRef &ref)
{
	if (pin->dir() != Netlist::PortDir::Input)
		return;
	std::vector<const Netlist::Pin *> drivers;
	AnchorHit barrier_hit = {.barrier = view_.cell(pin->inst), .barrier_scope = pin->inst->parent};
	walker_.pins(barrier_hit, Anchor::Side::A, BufferRule::StopAtNewBuffer, drivers);
	for (const Netlist::Pin *driver : drivers)
		anchorPin(driver, ref_index, ref, PinCut::Cut);
	ref.origin.anchored_on_drivers = !drivers.empty();
}

void detail::CheckpointWriter::anchorCell(const Netlist::Instance *inst, Anchor anchor)
{
	RTLIL::Cell *cell = view_.cell(inst);
	anchor.in_shared_module = markIfShared(cell, cell->module);
	data_.anchors.append(view_.design(), cell, anchor);
}

void detail::CheckpointWriter::anchorWires(const Netlist::Net *net, uint32_t ref_index)
{
	if (net == nullptr || net->constant != Netlist::Net::Const::None)
		return;
	std::string path = data_.snapshot.scopePath(view_, net->scope);
	for (const RTLIL::SigBit &bit : view_.wireBits(net)) {
		bool shared = markIfShared(bit.wire, bit.wire->module);
		Anchor anchor = {
			.role = Anchor::Role::Net,
			.ref_index = ref_index,
			.scope_path = detail::withOwnScope(path, bit.wire),
			.bit = bit.offset,
			.net_scope_path = path,
			.in_shared_module = shared
		};
		data_.anchors.append(view_.design(), bit.wire, anchor);
	}
}

bool detail::CheckpointWriter::markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module)
{
	if (view_.scopes(module).size() < 2)
		return false;
	detail::ensureScopename(object);
	return true;
}

// without -scopename, flatten extends a private object's 'scopename' only if present
void detail::ensureScopename(RTLIL::AttrObject *object)
{
	if (!detail::hasOwnScope(object))
		object->attributes[ID::scopename] = RTLIL::Const(std::string());
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

std::string detail::withOwnScope(const std::string &path, const RTLIL::AttrObject *object)
{
	return Netlist::joinPath({path, Netlist::joinPath(detail::ownScopeParts(object))});
}

YOSYS_NAMESPACE_END
