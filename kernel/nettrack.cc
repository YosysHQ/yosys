// checkpoint and clear, CheckpointWriter protects each ref object, then anchors it
#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

NetTracker::NetTracker() : data_(std::make_unique<detail::TrackData>()) {}

NetTracker::~NetTracker() = default;

void NetTracker::checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, bool protect)
{
	log_assert(view.upToDate());
	// a cell keeps its id, design -load can bring back a cell of an older checkpoint
	*data_ = {};
	detail::removeOwnedKeeps(view.design());
	detail::CheckpointWriter writer(view, *data_, protect);
	detail::makeScopeNamesUnique(view);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		writer.write(ref_index, *refs[ref_index]);
	writer.noteScopes();
	writer.dropUnusedIds();
	view.markUpToDate();
}

void NetTracker::clear(RTLIL::Design *design)
{
	*data_ = {};
	RTLIL::IdString id = design->twines().find(detail::ref_attr);
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells()) {
			if (cell->type != ID($barrier)) // a barrier keeps its id
				cell->attributes.erase(id);
		}
		for (RTLIL::Wire *wire : module->wires())
			wire->attributes.erase(id);
	}
}

void detail::makeScopeNamesUnique(const NetView &view)
{
	// a new name changes the names of the scopes below, so count again until no name changes
	for (bool changed = true; changed;) {
		changed = false;
		dict<std::string, int> scope_count;
		for (const Netlist::Instance &scope : view.instances()) {
			if (scope.isLeaf() || scope.isTop())
				continue;
			detail::ensureHdlname(scope.cell);
			scope_count[detail::scopeNames(&scope)]++;
		}
		// of two scopes with the same names one is a flatten copy with scope names in its hdlname
		for (const Netlist::Instance &scope : view.instances()) {
			if (scope.isLeaf() || scope.isTop())
				continue;
			bool has_scope_names = scope.cell->get_string_attribute(ID::hdlname).find(' ') != std::string::npos;
			if (!has_scope_names || scope_count[detail::scopeNames(&scope)]-- <= 1)
				continue;
			scope.cell->set_string_attribute(ID::hdlname, scope.cell->name.unescape());
			changed = true;
		}
	}
}

// each shorter list of the names is of a scope too, a known list has them all
void detail::TrackData::noteDissolved(std::string names)
{
	while (!names.empty() && scopes.emplace(names, Scope::Dissolved).second) {
		size_t space_before = names.rfind(' ', names.size() - 2);
		names.resize(space_before == std::string::npos ? 0 : space_before + 1);
	}
}

std::string detail::scopeNames(const Netlist::Instance *scope, const RTLIL::AttrObject *object)
{
	std::string names;
	if (object != nullptr)
		names = object->get_string_attribute(ID::hdlname);
	size_t last_space = names.rfind(' ');
	names.resize(last_space == std::string::npos ? 0 : last_space + 1); // without the name of the object
	for (; !scope->isTop(); scope = scope->parent)
		names = detail::hdlName(scope->cell) + " " + names;
	return names;
}

int detail::TrackData::nextId(RTLIL::Design *design)
{
	last_id = std::max(last_id, detail::keySeed(design));
	log_assert(last_id < INT_MAX);
	return ++last_id;
}

void detail::CheckpointWriter::append(RTLIL::AttrObject *object, const Anchor &anchor)
{
	RTLIL::Design *design = view_.design();
	std::optional<int> id = detail::refIdOf(design, object);
	if (!id) {
		id = data_.nextId(design);
		object->attributes[design->twines().add(detail::ref_attr)] = RTLIL::Const(*id);
	}
	data_.anchors_by_id.add(*id, anchor);
	anchored_.insert(object);
}

const detail::AnchorList &detail::TrackData::anchorsOf(RTLIL::Design *design, const RTLIL::AttrObject *object) const
{
	std::optional<int> id = detail::refIdOf(design, object);
	return id ? anchors_by_id.get(*id) : anchors_by_id.none;
}

std::optional<int> detail::refIdOf(RTLIL::Design *design, const RTLIL::AttrObject *object)
{
	RTLIL::IdString attr = design->twines().find(detail::ref_attr);
	if (!object->has_attribute(attr))
		return std::nullopt;
	return object->attributes.at(attr).as_int();
}

// hash of the first design, fixed for the process, so the same commands give the same ids in each run
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

void detail::CheckpointWriter::write(uint32_t ref_index, const TrackedRef &ref)
{
	for (const Netlist::Pin *pin : ref.pins)
		anchorPin(pin, ref_index);
	for (const Netlist::Pin *pin : ref.loads)
		anchorPin(pin, ref_index);
	for (const Netlist::Instance *inst : ref.instances) {
		log_assert(!inst->isTop());
		protectCell(inst, ref_index);
		anchorIn(inst, inst->cell, {.role = Anchor::Role::Cell, .ref_index = ref_index});
	}
	for (const Netlist::Net *net : ref.nets) {
		// the wire that names the net, none for a constant
		RTLIL::IdString wire_name = detail::escapedPortId(view_.design(), net->scope, net->name.wire);
		RTLIL::Wire *wire = net->scope->module->wire(wire_name);
		std::string dissolved = detail::scopeNames(view_.top(), wire);
		gone_scopes_by_module_[net->scope->module].insert(dissolved);
		bool on_port = !net->scope->isTop() && !net->boundary.empty();
		data_.net_places_by_ref.add(ref_index, {detail::scopeNames(net->scope), dissolved, on_port, net->name});
		int place = GetSize(data_.net_places_by_ref.get(ref_index)) - 1;
		if (wire != nullptr)
			append(wire, {.role = Anchor::Role::Net, .ref_index = ref_index, .net_place = place});
		protectNet(net, ref_index);
	}
}

detail::Anchor detail::pinAnchor(const Netlist::Pin *pin, uint32_t ref_index, Anchor::Role role)
{
	return {.role = role, .ref_index = ref_index, .port = pin->port().name, .bit = pin->bit,
	        .hdl_index = pin->hdlIndex()};
}

// a top port is found by its wire or name, a hierarchical pin by its barrier
// with no barrier by its instance and port name, else by the leaf pins below
void detail::CheckpointWriter::anchorPin(const Netlist::Pin *pin, uint32_t ref_index)
{
	const Netlist::Instance *inst = pin->inst;
	Anchor anchor = detail::pinAnchor(pin, ref_index);
	if (inst->isTop()) {
		data_.top_ports_by_ref.add(ref_index, anchor);
		RTLIL::Wire *wire = inst->module->wire(detail::escapedPortId(view_.design(), inst, pin->port().name));
		// a new id unless it has an anchor, a wire that design -load brings back then goes by its name
		if (!anchored_.count(wire))
			wire->attributes.erase(view_.design()->twines().find(detail::ref_attr));
		anchor.role = Anchor::Role::Port;
		append(wire, anchor);
		return;
	}
	bool cut = protect_ && cutPin(pin, ref_index);
	if (cut && !inst->isLeaf())
		return; // its barrier finds a hierarchical pin
	if (cut && pin->isDriver())
		protectDriver(pin, ref_index);
	if (!inst->isLeaf())
		anchorInnerPins(pin->inner, pin->dir(), ref_index);
	if (cut)
		anchor.role = Anchor::Role::CutPin;
	anchorIn(inst, inst->cell, anchor);
}

void detail::CheckpointWriter::anchorInnerPins(const Netlist::Net *net, RTLIL::PortDir dir, uint32_t ref_index)
{
	if (net == nullptr)
		return; // a port with nothing inside
	for (const Netlist::Pin *pin : detail::standInPins(net, dir))
		anchorIn(pin->inst, pin->inst->cell, detail::pinAnchor(pin, ref_index, Anchor::Role::StandIn));
}

detail::PinList detail::standInPins(const Netlist::Net *net, RTLIL::PortDir dir)
{
	PinList inside, loads_outside;
	bool has_load_inside = false, exact_outside = true;
	size_t scope_ports = 0;
	for (const Netlist::Net *connected : detail::connectedNets(net)) {
		const Netlist::Instance *scope = connected->scope;
		while (scope != nullptr && scope != net->scope)
			scope = scope->parent;
		for (const Netlist::Pin *pin : connected->pins) {
			bool wanted = dir == RTLIL::PD_INOUT || pin->isDriver() == (dir == RTLIL::PD_OUTPUT);
			if (!pin->inst->isLeaf())
				continue;
			if (scope != nullptr && wanted)
				inside.push_back(pin);
			if (scope == nullptr && !pin->isDriver())
				loads_outside.push_back(pin);
			has_load_inside = has_load_inside || (scope != nullptr && !pin->isDriver());
		}
		if (connected->scope == net->scope)
			scope_ports += connected->boundary.size();
		// a top output is a load with no leaf pin
		exact_outside = exact_outside && (!connected->scope->isTop() || connected->boundary.empty());
	}
	// a driver with a load inside would widen the ref to that load, the loads outside have just its paths
	if (dir == RTLIL::PD_OUTPUT && has_load_inside)
		inside = exact_outside ? loads_outside : PinList();
	// the leaf pins have the paths of a second port of the scope too, the ref is then lost with the scope
	if (dir != RTLIL::PD_INOUT && scope_ports > 1)
		inside.clear();
	return inside;
}

void detail::CheckpointWriter::anchorIn(const Netlist::Instance *inst, RTLIL::Cell *cell, Anchor anchor)
{
	detail::ensureHdlname(cell);
	// flatten keeps the scope names of a cell in its hdlname only below a scope with a public name
	// so a protected scope with a private name above the instance stays
	for (const Netlist::Instance *above = inst->parent; protect_ && !above->isTop(); above = above->parent) {
		if (!above->cell->name.isPublic())
			detail::setOwnedAttribute(view_.design(), above->cell, ID::keep_hierarchy);
	}
	anchor.scope = detail::scopeNames(inst->parent, cell);
	gone_scopes_by_module_[cell->module].insert(detail::scopeNames(view_.top(), cell));
	append(cell, anchor);
}

// the hdlname of an anchored cell names scopes that are gone, each scope of its module had them
void detail::CheckpointWriter::noteScopes()
{
	for (const Netlist::Instance &scope : view_.instances()) {
		if (scope.isLeaf())
			continue;
		std::string names = detail::scopeNames(&scope);
		data_.scopes[names] = TrackData::Scope::Live;
		for (const std::string &gone : gone_scopes_by_module_[scope.module])
			data_.noteDissolved(names + gone);
		if (scope.isTop())
			continue;
		std::string above = detail::scopeNames(scope.parent, scope.cell);
		data_.noteDissolved(above);
		Anchor anchor = {.role = Anchor::Role::Scope, .ref_index = 0, .scope = above};
		anchor.own_name = names.substr(above.size());
		append(scope.cell, anchor);
	}
	for (auto &[id, anchors] : data_.anchors_by_id.data)
		std::ranges::stable_sort(anchors, {}, &Anchor::scope); // noteHits looks up a scope
}

void detail::ensureHdlname(RTLIL::Cell *cell)
{
	if (cell->get_string_attribute(ID::hdlname).find(' ') == std::string::npos)
		cell->set_string_attribute(ID::hdlname, cell->name.unescape());
}

YOSYS_NAMESPACE_END
