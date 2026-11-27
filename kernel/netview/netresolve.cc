// resolve of NetTracker, see Resolver
#include "kernel/netview/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

void NetTracker::resolve(const NetView &view, const std::vector<TrackedRef *> &refs)
{
	if (refs.empty())
		return; // scope anchors alone need no walk
	detail::Resolver resolver(view, *data_);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		resolver.resolve(ref_index, *refs[ref_index]);
}

detail::Resolver::Resolver(const NetView &view, const TrackData &data) : view_(view), data_(data)
{
	scope_names_.resize(view.instances().size());
	enterScope(view.top(), "");
	// a taken scope adds candidates, so loop until no anchor takes one and no named scope waits
	bool progress = true;
	while (progress) {
		progress = takeCandidates(AnchorKind::Scopes);
		progress = progress || enterNamedScopes();
		progress = progress || takeCandidates(AnchorKind::Objects);
	}
}

// a scope with a Scope anchor waits for its hit, one named as a checkpoint scope for enterNamedScopes
void detail::Resolver::enterScope(const Netlist::Instance *scope, const std::string &names)
{
	scope_names_[scope->id] = names;
	live_scopes_.insert(names);
	for (const Netlist::Instance *child : scope->children) {
		noteHits(scope, child->cell);
		if (child->isLeaf())
			continue;
		const AnchorList &anchors = data_.anchorsOf(view_.design(), child->cell);
		if (std::ranges::find(anchors, Anchor::Role::Scope, &Anchor::role) != anchors.end())
			continue; // its anchor finds it
		// submod makes a new scope, chtype makes one of a leaf cell
		std::string child_names = names + detail::hdlName(child->cell) + " ";
		if (data_.scopes.count(child_names))
			named_scopes_.push_back(child);
		else
			enterScope(child, child_names);
	}
	for (const RTLIL::Cell *cell : scope->module->cells()) {
		if (cell->type == ID($barrier))
			noteHits(scope, cell);
	}
	noteWires(scope);
}

// an anchor of the cell with the scope names of this place is a hit, with names that align it is a candidate
void detail::Resolver::noteHits(const Netlist::Instance *scope, const RTLIL::Cell *cell)
{
	const AnchorList &anchors = data_.anchorsOf(view_.design(), cell);
	if (anchors.empty())
		return;
	std::string dissolved = detail::scopeNames(view_.top(), detail::hdlName(cell));
	std::string now = *scope_names_[scope->id] + dissolved;
	bool is_barrier = cell->type == ID($barrier);
	auto at_old_place = std::ranges::equal_range(anchors, now, {}, &Anchor::scope); // sorted, see noteScopes
	for (const Anchor &anchor : at_old_place) {
		if ((anchor.role == Anchor::Role::Barrier) == is_barrier)
			addHit({&anchor, scope, cell});
	}
	if (!at_old_place.empty())
		return; // a cell at its old place is of no other place
	int moved_before = moved_cell_count_[{&anchors, now}]++;
	if (moved_before >= detail::noted_twins)
		return; // two cells with the same id and names are twins, more of them add nothing
	for (const Anchor &anchor : anchors) {
		if ((anchor.role == Anchor::Role::Barrier) == is_barrier && namesAlign(anchor.scope, now))
			candidates_.add(&anchor, {&anchor, scope, cell, now});
	}
}

// a Scope hit names its scope by the checkpoint, a cell of two scopes is of the first
void detail::Resolver::addHit(const AnchorHit &hit)
{
	anchors_with_hit_.insert(hit.anchor);
	place_by_cell_.insert({{hit.scope, hit.cell}, hit.anchor});
	if (hit.anchor->role != Anchor::Role::Scope) {
		hits_by_ref_role_.add({hit.anchor->ref_index, hit.anchor->role}, hit);
		return;
	}
	const Netlist::Instance *inst = view_.instance(hit.cell, hit.scope);
	if (!inst->isLeaf() && !scope_names_[inst->id])
		enterScope(inst, hit.anchor->scope + hit.anchor->own_name);
}

// a scope with no anchor and the names of a checkpoint scope is that scope when the view has no other
// design -load brings cells with no id, submod can reuse the old name of a renamed scope, false when none
bool detail::Resolver::enterNamedScopes()
{
	InstanceList scopes = std::move(named_scopes_);
	named_scopes_.clear();
	for (const Netlist::Instance *scope : scopes) {
		const std::string &above = *scope_names_[scope->parent->id];
		std::string name = detail::hdlName(scope->cell) + " ";
		if (live_scopes_.count(above + name))
			name = detail::new_scope_mark + name;
		enterScope(scope, above + name);
	}
	return !scopes.empty();
}

// offset in old after the next scope that the view had at the checkpoint and has no more, else npos
// names of scopes that flatten dissolved before the checkpoint go with it, an hdlname has them
size_t detail::Resolver::goneScopeEnd(std::string_view old, size_t at) const
{
	while (at < old.size()) {
		at = old.find(' ', at) + 1;
		std::string scope(old.substr(0, at));
		if (data_.scopes.at(scope, TrackData::Scope::Dissolved) == TrackData::Scope::Live)
			return live_scopes_.count(scope) ? std::string::npos : at;
	}
	return std::string::npos;
}

// true when now can be the place of old, now lacks the names of gone scopes
// and has one more name for each scope that is new since the checkpoint, submod makes one
bool detail::Resolver::namesAlign(std::string_view old, std::string_view now) const
{
	size_t old_at = 0;
	for (size_t now_at = 0, next = 0; now_at < now.size(); now_at = next) {
		next = now.find(' ', now_at) + 1;
		std::string_view name = now.substr(now_at, next - now_at);
		if (name[0] == detail::new_scope_mark)
			continue;
		// name is the next of old, or one below scopes that are gone, else it is of a new scope
		size_t at = old_at;
		while (at != std::string::npos && !old.substr(at).starts_with(name)) {
			std::string other_scope = std::string(old.substr(0, at)) + std::string(name);
			if (data_.scopes.count(other_scope))
				return false; // of another scope of the checkpoint
			at = goneScopeEnd(old, at);
		}
		if (at != std::string::npos)
			old_at = at + name.size();
	}
	while (old_at < old.size())
		old_at = goneScopeEnd(old, old_at);
	return old_at == old.size();
}

// an anchor with no hit takes its one candidate, false when no anchor took one
bool detail::Resolver::takeCandidates(AnchorKind kind)
{
	markCandidateScopesLive();
	HitList wanted;
	dict<CellInScope, ScopeNameSet> old_places;
	for (const auto &[anchor, candidates] : candidates_.data) {
		bool is_scope = anchor->role == Anchor::Role::Scope;
		bool is_wanted_kind = is_scope == (kind == AnchorKind::Scopes);
		if (!is_wanted_kind || anchors_with_hit_.count(anchor))
			continue;
		const AnchorHit *candidate = onlyCandidate(candidates);
		if (candidate == nullptr)
			continue;
		wanted.push_back(*candidate);
		old_places[{candidate->scope, candidate->cell}].insert(anchor->scope);
	}
	bool took_one = false;
	for (const AnchorHit &hit : wanted) {
		if (old_places.at({hit.scope, hit.cell}).size() != 1)
			continue; // two anchors of other places want the cell
		addHit(hit); // enters its scope, that adds candidates
		took_one = true;
	}
	return took_one;
}

const detail::AnchorHit *detail::Resolver::onlyCandidate(const HitList &candidates) const
{
	HitPtrList aligned = alignedCandidates(candidates);
	if (aligned.size() != 1)
		return nullptr;
	const AnchorList &cell_anchors = data_.anchorsOf(view_.design(), aligned[0]->cell);
	if (moved_cell_count_.at({&cell_anchors, aligned[0]->now}) > detail::noted_twins)
		return nullptr; // noteHits did not note each of its twins
	return aligned[0];
}

// a scope with a candidate lives, also when a twin keeps it out
// a cell with no scope name is then no cell out of it, so they are all marked before an anchor takes one
void detail::Resolver::markCandidateScopesLive()
{
	for (const auto &[anchor, candidates] : candidates_.data) {
		bool waits = anchor->role == Anchor::Role::Scope && !anchors_with_hit_.count(anchor);
		if (waits && !alignedCandidates(candidates).empty())
			live_scopes_.insert(anchor->scope + anchor->own_name);
	}
}

// those with names that still align and a cell of no other old place
detail::HitPtrList detail::Resolver::alignedCandidates(const HitList &hits) const
{
	HitPtrList aligned;
	for (const AnchorHit &candidate : hits) {
		const Anchor *placed = place_by_cell_.at({candidate.scope, candidate.cell}, candidate.anchor);
		if (placed->scope == candidate.anchor->scope && namesAlign(candidate.anchor->scope, candidate.now))
			aligned.push_back(&candidate);
	}
	return aligned;
}

void detail::Resolver::noteWires(const Netlist::Instance *scope)
{
	for (RTLIL::Wire *wire : scope->module->wires()) {
		for (const Anchor &anchor : data_.anchorsOf(view_.design(), wire)) {
			if (anchor.role == Anchor::Role::Net)
				noteNamedNet(scope, wire, anchor);
			if (anchor.role != Anchor::Role::Port || !scope->isTop() || wire->port_id == 0)
				continue;
			if (const Netlist::Pin *pin = scope->findPin(wire->name.unescape(), anchor.bit))
				port_pin_by_place_[{anchor.ref_index, anchor.port, anchor.bit}] = pin;
		}
	}
}

// net that each anchored wire at its old place names, or none, a net on a port only in its old scope
void detail::Resolver::noteNamedNet(const Netlist::Instance *scope, const RTLIL::Wire *wire, const Anchor &anchor)
{
	const NetPlace &place = data_.net_places_by_ref.get(anchor.ref_index)[anchor.net_place];
	const std::string &names = *scope_names_[scope->id];
	std::string dissolved = detail::scopeNames(view_.top(), detail::hdlName(wire));
	bool at_old_place = names + dissolved == place.scope + place.dissolved;
	bool left_port_scope = place.on_port && names != place.scope;
	if (!at_old_place || left_port_scope)
		return;
	const NetsByName &nets = netsByName(scope);
	Netlist::NetName name_now = {
		.wire = wire->name.unescape(),
		.index = place.name.index,
		.scalar = place.name.scalar,
	};
	const Netlist::Net *named_net = nullptr;
	auto found = nets.find(name_now);
	if (found != nets.end())
		named_net = found->second;
	named_nets_by_place_.add(&place, named_net);
}

// first net of each name, made at the first Net anchor of the scope
const detail::NetsByName &detail::Resolver::netsByName(const Netlist::Instance *scope)
{
	NetsByName &nets = nets_by_scope_name_[scope->id];
	if (nets.empty()) {
		for (const Netlist::Net *net : scope->nets)
			nets.emplace(net->name, net);
	}
	return nets;
}

void detail::Resolver::resolve(uint32_t ref_index, TrackedRef &ref)
{
	ref.loads.clear();
	if (!data_.net_places_by_ref.get(ref_index).empty())
		ref.kind = TrackedRef::Kind::Net; // again for a rerun, see below
	switch (ref.kind) {
	case TrackedRef::Kind::Pin:
		ref.pins = resolvePin(ref_index);
		ref.gone = ref.pins.empty();
		for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier})) {
			if (ref.gone)
				std::ranges::copy(loadsBehind(hit), std::back_inserter(ref.loads));
		}
		break;
	case TrackedRef::Kind::Instance:
		resolveInstance(ref_index, ref);
		break;
	case TrackedRef::Kind::Net:
		ref.nets = resolveNet(ref_index);
		ref.pins.clear();
		// a net that is not found is its old pins from now on
		if (ref.nets.empty())
			ref.pins = detail::uniqueSorted(hitPins(ref_index, Anchor::Role::StandIn));
		ref.gone = ref.nets.empty() && ref.pins.empty();
		if (!ref.pins.empty())
			ref.kind = TrackedRef::Kind::Pin;
		break;
	}
	ref.loads = detail::uniqueSorted(ref.loads);
}

// cell, else the cells between its barriers, else the loads behind them
void detail::Resolver::resolveInstance(uint32_t ref_index, TrackedRef &ref)
{
	ref.port_cuts.clear();
	bool has_wired_output = false;
	for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier})) {
		bool is_output = detail::cutOnA(hit.cell);
		PinList cut_side = cutPins(hit, WalkReach::AllLoads);
		ref.port_cuts.push_back({hit.anchor->port, is_output, cut_side});
		has_wired_output = has_wired_output || (is_output && isWiredOutput(hit, cut_side));
	}
	ref.instances.clear();
	for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, Anchor::Role::Cell}))
		ref.instances.push_back(view_.instance(hit.cell, hit.scope));
	bool has_id = !ref.instances.empty();
	InstanceList new_drivers = detail::newDrivers(ref);
	InstanceList between;
	if (!has_id || !new_drivers.empty())
		between = cellsBetween(ref_index, has_id);
	// the id holds while only the id cells feed the new drivers, see _TECHMAP_REPLACE_
	bool is_bypassed = !has_id || !isFedOnlyBy(new_drivers, ref.instances, between);
	// with no other cell between, the id stays
	ref.gone = !has_id || (is_bypassed && !detail::isAllBetween(between, ref.instances));
	if (ref.gone)
		ref.instances = between;
	ref.partial = !ref.instances.empty() && (has_wired_output || (is_bypassed && !detail::newDrivers(ref).empty()));
	bool has_inout_pins = !data_.open_bits_by_ref.get(ref_index).empty();
	bool is_wire = ref.gone && ref.instances.empty() && !has_inout_pins;
	for (const TrackedRef::PortCut &cut : ref.port_cuts) {
		if (is_wire && cut.is_output)
			ref.loads.insert(ref.loads.end(), cut.pins.begin(), cut.pins.end());
	}
}

// an old output with loads and no leaf driver is a wire, a constant is none
bool detail::Resolver::isWiredOutput(const AnchorHit &hit, const PinList &cut_side)
{
	RTLIL::SigBit cut_bit = walkerOf(hit.scope->module).sigmap(detail::cutBit(hit.cell));
	bool has_driver = std::ranges::any_of(cut_side, detail::isLeafDriver);
	return cut_bit.wire != nullptr && !has_driver && !cut_side.empty();
}

bool detail::isLeafDriver(const Netlist::Pin *pin)
{
	return pin->inst->isLeaf() && pin->isDriver();
}

// no input pin, so no path into it
bool detail::isTieCell(const Netlist::Instance *inst)
{
	auto first_input = std::ranges::find(inst->pins, RTLIL::PD_INPUT, &Netlist::Pin::dir);
	return inst->isLeaf() && first_input == inst->pins.end();
}

// leaf drivers of the old outputs that are not ref cells or tie cells
detail::InstanceList detail::newDrivers(const TrackedRef &ref)
{
	InstanceList drivers;
	for (const TrackedRef::PortCut &cut : ref.port_cuts) {
		for (const Netlist::Pin *pin : cut.pins) {
			bool is_new_driver = cut.is_output && detail::isLeafDriver(pin) && !detail::isBetween(pin->inst, ref.instances);
			if (is_new_driver && !detail::isTieCell(pin->inst))
				drivers.push_back(pin->inst);
		}
	}
	return drivers;
}

// each path into todo starts at cells and stays between
bool detail::Resolver::isFedOnlyBy(InstanceList todo, const InstanceList &cells, const InstanceList &between)
{
	pool<const Netlist::Instance *> seen(todo.begin(), todo.end());
	while (!todo.empty()) {
		const Netlist::Instance *at = todo.back();
		todo.pop_back();
		for (const Netlist::Pin *input : at->pins) {
			if (!queueDriversBetween(input, cells, between, seen, todo))
				return false;
		}
	}
	return true;
}

// queues the drivers that are between, false for one outside like a top input
bool detail::Resolver::queueDriversBetween(const Netlist::Pin *input, const InstanceList &cells, const InstanceList &between, pool<const Netlist::Instance *> &seen, InstanceList &todo)
{
	// only a driven input brings a path
	bool is_input = input->dir() == RTLIL::PD_INPUT;
	if (!is_input || input->net == nullptr || input->net->constant != Netlist::Net::Const::None)
		return true;
	for (const Netlist::Instance *driver : driverCells(input->net)) {
		if (detail::isBetween(driver, cells))
			continue;
		if (!detail::isBetween(driver, between))
			return false;
		if (seen.insert(driver).second)
			todo.push_back(driver);
	}
	return true;
}

// drivers over the hierarchy, the top for a top input, cached since many refs read a clock
const detail::InstanceList &detail::Resolver::driverCells(const Netlist::Net *net)
{
	if (driver_cells_by_net_.count(net) != 0)
		return driver_cells_by_net_.at(net);
	NetList connected_nets = detail::connectedNets(net);
	InstanceList drivers;
	for (const Netlist::Net *connected : connected_nets) {
		for (const std::vector<Netlist::Pin *> *pins : {&connected->boundary, &connected->pins}) {
			for (const Netlist::Pin *pin : *pins) {
				if (pin->isDriver() && !detail::isTieCell(pin->inst))
					drivers.push_back(pin->inst);
			}
		}
	}
	for (const Netlist::Net *connected : connected_nets)
		driver_cells_by_net_[connected] = drivers;
	return driver_cells_by_net_.at(net);
}

// at or below one of between, a scope holds its cells
bool detail::isBetween(const Netlist::Instance *inst, const InstanceList &between)
{
	for (const Netlist::Instance *cell : between) {
		if (detail::isAtOrBelow(inst, cell))
			return true;
	}
	return false;
}

bool detail::isAllBetween(const InstanceList &cells, const InstanceList &between)
{
	for (const Netlist::Instance *cell : cells) {
		if (!detail::isBetween(cell, between))
			return false;
	}
	return true;
}

// a leaf pin with a barrier resolves to its cut side, a lost barrier gives the pin of the anchored cell
detail::PinList detail::Resolver::resolvePin(uint32_t ref_index)
{
	const HitList &barrier_hits = hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier});
	PinList pins = hitPins(ref_index, Anchor::Role::Pin);
	if (barrier_hits.empty())
		std::ranges::copy(hitPins(ref_index, Anchor::Role::CutPin), std::back_inserter(pins));
	// pin of a live scope wins, else the leaf pins below stand in
	if (std::ranges::all_of(pins, &Netlist::Instance::isLeaf, &Netlist::Pin::inst))
		std::ranges::copy(hitPins(ref_index, Anchor::Role::StandIn), std::back_inserter(pins));
	for (const AnchorHit &hit : barrier_hits)
		std::ranges::copy(cutPins(hit), std::back_inserter(pins));
	for (const Anchor &named : data_.top_ports_by_ref.get(ref_index)) {
		const Netlist::Pin *pin = port_pin_by_place_.at({ref_index, named.port, named.bit}, nullptr);
		if (pin == nullptr)
			pin = detail::findPortPin(view_.top(), named); // by name when no wire has the anchor
		if (pin != nullptr)
			pins.push_back(pin);
	}
	return detail::uniqueSorted(pins);
}

detail::PinList detail::Resolver::hitPins(uint32_t ref_index, Anchor::Role role)
{
	PinList pins;
	for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, role})) {
		const Netlist::Instance *inst = view_.instance(hit.cell, hit.scope);
		if (const Netlist::Pin *pin = detail::findPortPin(inst, *hit.anchor))
			pins.push_back(pin);
	}
	return pins;
}

const Netlist::Pin *detail::findPortPin(const Netlist::Instance *inst, const Anchor &anchor)
{
	const Netlist::Pin *pin = inst->findPin(anchor.port, anchor.bit);
	if (pin != nullptr || inst->isLeaf())
		return pin;
	// splitnets -ports names a bit port[index]
	std::string bit_port = stringf("%s[%d]", anchor.port, anchor.hdl_index);
	return inst->findPin(bit_port, 0);
}

// leaf pins on the cut wire of the barrier, the cut side has the drivers of a driver pin, else the loads
detail::PinList detail::Resolver::cutPins(const AnchorHit &hit, WalkReach reach)
{
	bool cut_on_a = detail::cutOnA(hit.cell);
	WalkTarget target = cut_on_a ? WalkTarget::Drivers : WalkTarget::Loads;
	CutWalk walk = {
		.reach = reach,
		.stop_at_scope = hit.anchor->hier,
	};
	walk.passed.insert({hit.scope, hit.cell, 0});
	if (!addCutPins(hit.scope, detail::cutBit(hit.cell), target, walk))
		walk.pins.clear();
	bool wants_loads_behind = reach == WalkReach::AllLoads && cut_on_a;
	if (wants_loads_behind && walk.pins.empty())
		walk.pins = loadsBehind(hit); // cell became a wire
	return detail::uniqueSorted(walk.pins);
}

const ModWalker &detail::Resolver::walkerOf(RTLIL::Module *module)
{
	return mod_walkers_.try_emplace(module, module->design, module).first->second;
}

// a pass can put another kind of user on the wire
bool detail::Resolver::addCutPins(const Netlist::Instance *scope, RTLIL::SigBit bit, WalkTarget target, CutWalk &walk)
{
	const ModWalker &walker = walkerOf(scope->module);
	RTLIL::SigBit root = walker.sigmap(bit);
	if (!walk.seen.insert({scope, root}).second)
		return true;
	if (!passPorts(scope, root, target, walk))
		return false;
	pool<PortBit> users;
	walker.get_drivers(users, root);
	walker.get_consumers(users, root);
	for (const PortBit &at : users) {
		if (!walk.passed.count({scope, at.cell, at.offset}) && !addUserPins(scope, at, target, walk))
			return false;
	}
	return true;
}

// an output port on the wire has loads outside the scope, an input port has a driver there
bool detail::Resolver::passPorts(const Netlist::Instance *scope, RTLIL::SigBit root, WalkTarget target, CutWalk &walk)
{
	const ModWalker &walker = walkerOf(scope->module);
	bool on_output = walker.signal_outputs.count(root);
	bool on_input = walker.signal_inputs.count(root);
	bool to_loads = target == WalkTarget::Loads;
	bool all_loads = walk.reach == WalkReach::AllLoads;
	// submod can move a barrier into a scope below its driver
	bool driver_above = !to_loads && !scope->isTop();
	bool leaves_scope = to_loads ? on_output : on_input;
	if (!all_loads && !driver_above && leaves_scope)
		return false;
	if (all_loads && on_output && !addPinsAbove(scope, root, WalkTarget::Loads, walk))
		return false;
	if (driver_above && on_input)
		return addPinsAbove(scope, root, target, walk);
	return true;
}

bool detail::Resolver::addUserPins(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	if (at.cell->type == ID($barrier))
		return passBarrier(scope, at, target, walk);
	if (at.cell->type == ID($input_port))
		return true;
	const Netlist::Instance *inst = view_.instance(at.cell, scope);
	if (inst == nullptr)
		return false;
	if (walk.exit_ports.count({inst, at.port, at.offset}))
		return true;
	if (!inst->isLeaf() && !walk.stop_at_scope)
		return addPinsBelow(inst, at, target, walk);
	std::string port_name = RTLIL::PooledName(at.cell->module, at.port).unescape();
	const Netlist::Pin *pin = inst->findPin(port_name, at.offset);
	if (pin == nullptr)
		return false;
	if (inst->isLeaf())
		return addLeafPin(pin, at, target, walk);
	walk.pins.push_back(pin);
	return true;
}

bool detail::Resolver::passBarrier(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	// driver below a dissolved scope can have its own barrier, else a pass joined the cut wire with another signal
	if (target == WalkTarget::Drivers) {
		if (!walk.stop_at_scope || at.port != ID::Y)
			return false;
		return passCell(scope, at, target, walk);
	}
	if (at.port != ID::A)
		return true; // on its Y the barrier is behind the walk
	// a barrier with anchors hides the loads behind it, their refs find them, a hierarchical pin is each load
	bool stops_at_anchors = walk.reach == WalkReach::CutSide && !walk.stop_at_scope;
	if (stops_at_anchors && !data_.anchorsOf(view_.design(), at.cell).empty())
		return true;
	return passCell(scope, at, target, walk);
}

// insbuf puts a buffer with no anchor before the loads, toward the drivers a new buffer can be the new driver
bool detail::Resolver::addLeafPin(const Netlist::Pin *pin, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	bool to_loads = target == WalkTarget::Loads;
	bool is_reader_of_old_output = walk.reach == WalkReach::AllLoads && !to_loads && !pin->isDriver();
	if (is_reader_of_old_output)
		return true; // new logic can read the old output on its cut wire
	if (pin->dir() != RTLIL::PD_INOUT && pin->isDriver() == to_loads)
		return false;
	bool is_buffer_before_loads = to_loads && pin->inst->type->is_buffer;
	if (is_buffer_before_loads && data_.anchorsOf(view_.design(), at.cell).empty())
		return passCell(pin->inst->parent, at, target, walk);
	walk.pins.push_back(pin);
	return true;
}

bool detail::Resolver::passCell(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	walk.passed.insert({scope, at.cell, at.offset});
	int width = GetSize(at.cell->getPort(at.port));
	for (const auto &[port, sig] : at.cell->connections()) {
		bool is_other_port = port != at.port && GetSize(sig) == width;
		if (is_other_port && !addCutPins(scope, sig[at.offset], target, walk))
			return false;
	}
	return true;
}

bool detail::Resolver::addPinsAbove(const Netlist::Instance *scope, RTLIL::SigBit root, WalkTarget target,
                                    CutWalk &walk)
{
	const ModWalker &walker = walkerOf(scope->module);
	for (RTLIL::IdString port : scope->module->ports) {
		RTLIL::Wire *wire = scope->module->wire(port);
		bool faces_target = target == WalkTarget::Loads ? wire->port_output : wire->port_input;
		for (int bit = 0; faces_target && bit < wire->width; bit++) {
			if (walker.sigmap(RTLIL::SigBit(wire, bit)) != root)
				continue;
			const Netlist::Pin *pin = scope->findPin(wire->name.unescape(), bit);
			if (scope->isTop() && pin != nullptr)
				walk.pins.push_back(pin);
			if (scope->isTop() || !scope->cell->hasPort(wire->name))
				continue;
			const RTLIL::SigSpec &outside_port = scope->cell->getPort(wire->name);
			if (bit >= GetSize(outside_port))
				continue;
			RTLIL::SigBit outside = outside_port[bit];
			walk.exit_ports.insert({scope, wire->name, bit});
			if (!addCutPins(scope->parent, outside, target, walk))
				return false;
		}
	}
	return true;
}

// submod puts a driver behind an output, AllLoads also takes the readers of the old output and passes other ports
bool detail::Resolver::addPinsBelow(const Netlist::Instance *inst, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	bool all_loads = walk.reach == WalkReach::AllLoads;
	RTLIL::Wire *wire = inst->module->wire(at.port);
	if (wire == nullptr || at.offset >= wire->width)
		return all_loads;
	RTLIL::SigBit inside(wire, at.offset);
	bool takes_loads = target == WalkTarget::Loads || all_loads;
	if (wire->port_input && takes_loads)
		return addCutPins(inst, inside, WalkTarget::Loads, walk);
	if (wire->port_output && target == WalkTarget::Drivers)
		return addCutPins(inst, inside, WalkTarget::Drivers, walk);
	return all_loads;
}

// an inout pin has no barrier, its old net ends the new logic, none when a pass removed that net
detail::InstanceList detail::Resolver::cellsBetween(uint32_t ref_index, bool has_id)
{
	const HitList &hits = hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier});
	if (hits.empty())
		return {};
	const Netlist::Instance *scope = hits[0].scope;
	const ModWalker &walker = walkerOf(scope->module);
	pool<RTLIL::SigBit> ends;
	for (const auto &[wire_name, offset] : data_.open_bits_by_ref.get(ref_index)) {
		RTLIL::Wire *wire = scope->module->wire(wire_name);
		if (wire == nullptr || offset >= wire->width)
			return {};
		ends.insert(walker.sigmap(RTLIL::SigBit(wire, offset)));
	}
	return cellsUpTo(hits, ends, has_id);
}

// cells on a path from an input cut wire to an output cut wire, a new cell can read a signal of other logic
// with cuts on one side or an inout pin there is no such path, a path of one direction is then enough
// a cell with its id needs no stand-in, it would take in the cone of other logic
detail::InstanceList detail::Resolver::cellsUpTo(const HitList &hits, const pool<RTLIL::SigBit> &ends, bool has_id)
{
	const Netlist::Instance *scope = hits[0].scope;
	size_t output_cuts = std::ranges::count_if(hits, detail::cutOnA, &AnchorHit::cell);
	bool one_direction = !has_id && (output_cuts == 0 || output_cuts == hits.size() || !ends.empty());
	CellSet after_inputs = cellsToward(hits, ends, WalkTarget::Loads);
	CellSet before_outputs = cellsToward(hits, ends, WalkTarget::Drivers);
	if (one_direction)
		after_inputs.insert(before_outputs.begin(), before_outputs.end());
	InstanceList cells;
	for (const RTLIL::Cell *cell : after_inputs) {
		const Netlist::Instance *inst = view_.instance(cell, scope);
		if (inst != nullptr && (one_direction || before_outputs.count(cell)))
			cells.push_back(inst);
	}
	return detail::uniqueSorted(cells);
}

// cells behind the input cut wires toward the loads, or behind the output cut wires toward the drivers
// a barrier or an end stops the walk
detail::CellSet detail::Resolver::cellsToward(const HitList &hits, const pool<RTLIL::SigBit> &ends, WalkTarget target)
{
	const ModWalker &walker = walkerOf(hits[0].scope->module);
	bool to_loads = target == WalkTarget::Loads;
	const auto &users_by_bit = to_loads ? walker.signal_consumers : walker.signal_drivers;
	const auto &next_bits_by_cell = to_loads ? walker.cell_outputs : walker.cell_inputs;
	std::vector<RTLIL::SigBit> todo;
	for (const AnchorHit &hit : hits) {
		if (detail::cutOnA(hit.cell) != to_loads)
			todo.push_back(detail::cutBit(hit.cell));
	}
	CellSet cells;
	while (!todo.empty()) {
		RTLIL::SigBit root = walker.sigmap(todo.back());
		todo.pop_back();
		auto users = users_by_bit.find(root);
		if (ends.count(root) || users == users_by_bit.end())
			continue;
		for (const PortBit &at : users->second) {
			if (at.cell->type == ID($barrier) || !cells.insert(at.cell).second)
				continue;
			auto next_bits = next_bits_by_cell.find(at.cell);
			if (next_bits != next_bits_by_cell.end())
				todo.insert(todo.end(), next_bits->second.begin(), next_bits->second.end());
		}
	}
	return cells;
}

// each path through the old cell goes into a load behind one of its output barriers
detail::PinList detail::Resolver::loadsBehind(const AnchorHit &hit)
{
	// a deleted cell drives nothing, a constant is a cell that a pass removed, a barrier at a load drives its cut wire
	const ModWalker &walker = walkerOf(hit.scope->module);
	RTLIL::SigBit cut = walker.sigmap(detail::cutBit(hit.cell));
	if (cut.wire != nullptr && !walker.has_drivers(RTLIL::SigSpec(cut)))
		return {};
	CutWalk walk = {.reach = WalkReach::AllLoads};
	walk.passed.insert({hit.scope, hit.cell, 0});
	if (!addCutPins(hit.scope, hit.cell->getPort(ID::Y)[0], WalkTarget::Loads, walk))
		return {};
	return walk.pins;
}

// nets at the anchored driver pins, else the one net that the anchored wire names
// a pass can move a driver to another net, so a named net with a load takes only its own drivers
detail::NetList detail::Resolver::resolveNet(uint32_t ref_index)
{
	NetList nets;
	PinList drivers = resolvePin(ref_index);
	for (const NetPlace &place : data_.net_places_by_ref.get(ref_index))
		addNetsAt(place, drivers, nets);
	return detail::uniqueSorted(nets);
}

void detail::Resolver::addNetsAt(const NetPlace &place, const PinList &drivers, NetList &nets) const
{
	const NetList &named = named_nets_by_place_.get(&place);
	const Netlist::Net *named_net = named.size() == 1 ? named[0] : nullptr; // two wires with the id are twins
	// a named net with no load is a dead stub of insbuf, each driver then tells the net
	bool has_load = false;
	if (named_net != nullptr) {
		bool only_drivers = std::ranges::all_of(named_net->pins, &Netlist::Pin::isDriver);
		has_load = !only_drivers || !named_net->boundary.empty();
	}
	size_t found = nets.size();
	for (const Netlist::Pin *pin : drivers) {
		if (!pin->isDriver())
			continue; // a stand-in load can be on another net now
		const Netlist::Net *pin_net = pin->inst->isTop() ? pin->inner : pin->net;
		const Netlist::Net *net = netInScope(pin_net, place);
		bool is_own_driver = !has_load || net == named_net;
		if (net != nullptr && is_own_driver)
			nets.push_back(net);
	}
	// insbuf can leave the wire on a dead stub, so it finds the net only when no driver does
	if (nets.size() == found && named_net != nullptr)
		nets.push_back(named_net);
}

// connected net in the deepest scope that is the old scope or above it, else in a new scope below
// flatten leaves the net of a dissolved scope in the scope above
const Netlist::Net *detail::Resolver::netInScope(const Netlist::Net *net, const NetPlace &old) const
{
	using NetsDeepestFirst = std::map<int, NetList, std::greater<int>>;
	NetsDeepestFirst found_by_depth;
	for (const Netlist::Net *connected : detail::connectedNets(net)) {
		const std::optional<std::string> &now = scope_names_[connected->scope->id];
		if (!now)
			continue;
		bool left_port_scope = old.on_port && *now != old.scope;
		// design -load brings back the scopes of a flat net
		bool at_flat_place = *now == old.scope + old.dissolved;
		if (left_port_scope || (!namesAlign(old.scope, *now) && !at_flat_place))
			continue;
		// submod moves a whole net into a new scope, the one nearest to the old scope has it
		int depth = now->size();
		if (!old.scope.starts_with(*now))
			depth = -depth;
		found_by_depth[depth].push_back(connected);
	}
	// a feedthrough module joins several nets of one scope, the name tells them apart, else the next scope has it
	for (const auto &[depth, found] : found_by_depth) {
		for (const Netlist::Net *candidate : found) {
			if (found.size() == 1 || candidate->name == old.name)
				return candidate;
		}
	}
	return nullptr;
}

YOSYS_NAMESPACE_END
