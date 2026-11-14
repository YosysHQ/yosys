// resolve of NetTracker, see Resolver
#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

void NetTracker::resolve(const NetView &view, const std::vector<TrackedRef *> &refs)
{
	if (refs.empty())
		return; // the scope anchors alone need no walk
	detail::Resolver resolver(view, *data_);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		resolver.resolve(ref_index, *refs[ref_index]);
}

detail::Resolver::Resolver(const NetView &view, const TrackData &data) : view_(view), data_(data)
{
	scope_names_.resize(view.instances().size());
	enterScope(view.top(), "");
	// a taken scope adds candidates, so go on until no anchor takes one and no named scope waits
	for (bool progress = true; progress;)
		progress = takeCandidates(AnchorKind::Scopes) || enterNamedScopes() || takeCandidates(AnchorKind::Objects);
}

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

void detail::Resolver::noteHits(const Netlist::Instance *scope, const RTLIL::Cell *cell)
{
	const AnchorList &anchors = data_.anchorsOf(view_.design(), cell);
	if (anchors.empty())
		return;
	std::string now = *scope_names_[scope->id] + detail::scopeNames(view_.top(), cell);
	bool is_barrier = cell->type == ID($barrier);
	auto at_old_place = std::ranges::equal_range(anchors, now, {}, &Anchor::scope); // sorted, see noteScopes
	for (const Anchor &anchor : at_old_place) {
		if ((anchor.role == Anchor::Role::Barrier) == is_barrier)
			addHit({&anchor, scope, cell});
	}
	if (!at_old_place.empty())
		return; // a cell at its old place is of no other place
	if (moved_cell_count_[{&anchors, now}]++ >= detail::noted_twins)
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

bool detail::Resolver::namesAlign(std::string_view old, std::string_view now) const
{
	size_t old_at = 0;
	for (size_t now_at = 0, next = 0; now_at < now.size(); now_at = next) {
		next = now.find(' ', now_at) + 1;
		std::string_view name = now.substr(now_at, next - now_at);
		if (name[0] == detail::new_scope_mark)
			continue;
		// the name is the next of old, or one below scopes that are gone, else it is of a new scope
		size_t at = old_at;
		while (at != std::string::npos && !old.substr(at).starts_with(name)) {
			if (data_.scopes.count(std::string(old.substr(0, at)) + std::string(name)))
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

bool detail::Resolver::takeCandidates(AnchorKind kind)
{
	markCandidateScopesLive();
	std::vector<AnchorHit> wanted;
	dict<std::pair<const Netlist::Instance *, const RTLIL::Cell *>, pool<std::string>> old_places;
	for (const auto &[anchor, candidates] : candidates_.data) {
		bool is_scope = anchor->role == Anchor::Role::Scope;
		if (is_scope != (kind == AnchorKind::Scopes) || anchors_with_hit_.count(anchor))
			continue;
		std::vector<const AnchorHit *> aligned = alignedCandidates(candidates);
		if (aligned.size() != 1)
			continue; // none fits, or two that fit are twins
		const AnchorList &cell_anchors = data_.anchorsOf(view_.design(), aligned[0]->cell);
		if (moved_cell_count_.at({&cell_anchors, aligned[0]->now}) > detail::noted_twins)
			continue; // noteHits did not note each of its twins
		wanted.push_back(*aligned[0]);
		old_places[{aligned[0]->scope, aligned[0]->cell}].insert(anchor->scope);
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

void detail::Resolver::markCandidateScopesLive()
{
	for (const auto &[anchor, candidates] : candidates_.data) {
		bool waits = anchor->role == Anchor::Role::Scope && !anchors_with_hit_.count(anchor);
		if (waits && !alignedCandidates(candidates).empty())
			live_scopes_.insert(anchor->scope + anchor->own_name);
	}
}

std::vector<const detail::AnchorHit *> detail::Resolver::alignedCandidates(const std::vector<AnchorHit> &hits) const
{
	std::vector<const AnchorHit *> aligned;
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

void detail::Resolver::noteNamedNet(const Netlist::Instance *scope, const RTLIL::Wire *wire, const Anchor &anchor)
{
	const NetPlace &place = data_.net_places_by_ref.get(anchor.ref_index)[anchor.net_place];
	const std::string &names = *scope_names_[scope->id];
	bool at_old_place = names + detail::scopeNames(view_.top(), wire) == place.scope + place.dissolved;
	if (!at_old_place || (place.on_port && names != place.scope))
		return;
	std::map<Netlist::NetName, const Netlist::Net *> &nets = nets_by_scope_name_[scope->id];
	if (nets.empty()) {
		for (const Netlist::Net *net : scope->nets)
			nets.emplace(net->name, net);
	}
	auto net = nets.find({wire->name.unescape(), place.name.index, place.name.scalar});
	named_nets_by_place_.add(&place, net != nets.end() ? net->second : nullptr);
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

// the cell, else the cells between its barriers, else the loads behind them
void detail::Resolver::resolveInstance(uint32_t ref_index, TrackedRef &ref)
{
	ref.port_cuts.clear();
	for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier}))
		ref.port_cuts.push_back({hit.anchor->port, detail::cutOnA(hit.cell), cutPins(hit, WalkReach::AllLoads)});
	ref.instances.clear();
	for (const AnchorHit &hit : hits_by_ref_role_.get({ref_index, Anchor::Role::Cell}))
		ref.instances.push_back(view_.instance(hit.cell, hit.scope));
	ref.gone = ref.instances.empty();
	if (ref.gone)
		ref.instances = cellsBetween(ref_index);
	bool has_inout_pins = !data_.open_bits_by_ref.get(ref_index).empty();
	bool is_wire = ref.gone && ref.instances.empty() && !has_inout_pins;
	for (const TrackedRef::PortCut &cut : ref.port_cuts) {
		if (is_wire && cut.is_output)
			ref.loads.insert(ref.loads.end(), cut.pins.begin(), cut.pins.end());
	}
}

// a leaf pin with a barrier resolves to its cut side, a lost barrier gives the pin of the anchored cell
detail::PinList detail::Resolver::resolvePin(uint32_t ref_index)
{
	const std::vector<AnchorHit> &barrier_hits = hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier});
	PinList pins = hitPins(ref_index, Anchor::Role::Pin);
	if (barrier_hits.empty())
		std::ranges::copy(hitPins(ref_index, Anchor::Role::CutPin), std::back_inserter(pins));
	// the pin of a live scope wins, else the leaf pins below stand in
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
		if (const Netlist::Pin *pin = detail::findPortPin(view_.instance(hit.cell, hit.scope), *hit.anchor))
			pins.push_back(pin);
	}
	return pins;
}

const Netlist::Pin *detail::findPortPin(const Netlist::Instance *inst, const Anchor &anchor)
{
	const Netlist::Pin *pin = inst->findPin(anchor.port, anchor.bit);
	if (pin == nullptr && !inst->isLeaf())
		pin = inst->findPin(stringf("%s[%d]", anchor.port, anchor.hdl_index), 0);
	return pin;
}

// the cut side has the drivers of a driver pin, else the loads
detail::PinList detail::Resolver::cutPins(const AnchorHit &hit, WalkReach reach)
{
	bool cut_on_a = detail::cutOnA(hit.cell);
	WalkTarget target = cut_on_a ? WalkTarget::Drivers : WalkTarget::Loads;
	CutWalk walk = {.reach = reach, .stop_at_scope = hit.anchor->hier};
	walk.passed.insert({hit.scope, hit.cell});
	if (!addCutPins(hit.scope, detail::cutBit(hit.cell), target, walk))
		walk.pins.clear();
	if (reach == WalkReach::AllLoads && walk.pins.empty() && cut_on_a)
		walk.pins = loadsBehind(hit); // the cell became a wire
	return detail::uniqueSorted(walk.pins);
}

const ModWalker &detail::Resolver::walkerOf(RTLIL::Module *module)
{
	return mod_walkers_.try_emplace(module, module->design, module).first->second;
}

// false if a pass put another kind of user on the wire, the ref is then lost
bool detail::Resolver::addCutPins(const Netlist::Instance *scope, RTLIL::SigBit bit, WalkTarget target, CutWalk &walk)
{
	const ModWalker &walker = walkerOf(scope->module);
	RTLIL::SigBit root = walker.sigmap(bit);
	if (!walk.seen.insert({scope, root}).second)
		return true;
	// an output port on the wire has loads outside the scope, an input port has a driver there
	const pool<RTLIL::SigBit> &outside = target == WalkTarget::Loads ? walker.signal_outputs : walker.signal_inputs;
	bool all_loads = walk.reach == WalkReach::AllLoads;
	if (!all_loads && outside.count(root))
		return false;
	if (all_loads && walker.signal_outputs.count(root) && !addLoadsAbove(scope, root, walk))
		return false;
	pool<PortBit> users;
	walker.get_drivers(users, root);
	walker.get_consumers(users, root);
	for (const PortBit &at : users) {
		if (!walk.passed.count({scope, at.cell}) && !addUserPins(scope, at, target, walk))
			return false;
	}
	return true;
}

bool detail::Resolver::addUserPins(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	if (at.cell->type == ID($barrier))
		return passBarrier(scope, at, target, walk);
	const Netlist::Instance *inst = view_.instance(at.cell, scope);
	if (inst == nullptr)
		return false;
	if (!inst->isLeaf() && !walk.stop_at_scope)
		return addPinsBelow(inst, at, target, walk);
	const Netlist::Pin *pin = inst->findPin(RTLIL::PooledName(at.cell->module, at.port).unescape(), at.offset);
	if (pin == nullptr)
		return false;
	if (inst->isLeaf())
		return addLeafPin(pin, at, target, walk);
	walk.pins.push_back(pin);
	return true;
}

bool detail::Resolver::passBarrier(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	// the driver below a dissolved scope can have its own barrier, else a pass joined the cut wire with another signal
	if (target == WalkTarget::Drivers)
		return walk.stop_at_scope && at.port == ID::Y && passCell(scope, at, target, walk);
	if (at.port != ID::A)
		return true; // on its Y the barrier is behind the walk
	// a barrier with anchors hides the loads behind it, their refs find them, a hierarchical pin is each load
	if (walk.reach == WalkReach::CutSide && !walk.stop_at_scope && !data_.anchorsOf(view_.design(), at.cell).empty())
		return true;
	return passCell(scope, at, target, walk);
}

// insbuf puts a buffer with no anchor before the loads, toward the drivers a new buffer can be the new driver
bool detail::Resolver::addLeafPin(const Netlist::Pin *pin, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	bool to_loads = target == WalkTarget::Loads;
	if (walk.reach == WalkReach::AllLoads && !to_loads && !pin->isDriver())
		return true; // new logic can read the old output on its cut wire
	if (pin->dir() != RTLIL::PD_INOUT && pin->isDriver() == to_loads)
		return false;
	if (to_loads && pin->inst->type->is_buffer && data_.anchorsOf(view_.design(), at.cell).empty())
		return passCell(pin->inst->parent, at, target, walk);
	walk.pins.push_back(pin);
	return true;
}

bool detail::Resolver::passCell(const Netlist::Instance *scope, const PortBit &at, WalkTarget target, CutWalk &walk)
{
	walk.passed.insert({scope, at.cell});
	for (const auto &[port, sig] : at.cell->connections()) {
		if (port != at.port && GetSize(sig) == 1 && !addCutPins(scope, sig[0], target, walk))
			return false;
	}
	return true;
}

bool detail::Resolver::addLoadsAbove(const Netlist::Instance *scope, RTLIL::SigBit root, CutWalk &walk)
{
	const ModWalker &walker = walkerOf(scope->module);
	for (RTLIL::IdString port : scope->module->ports) {
		RTLIL::Wire *wire = scope->module->wire(port);
		for (int bit = 0; wire->port_output && bit < wire->width; bit++) {
			if (walker.sigmap(RTLIL::SigBit(wire, bit)) != root)
				continue;
			const Netlist::Pin *pin = scope->findPin(wire->name.unescape(), bit);
			if (scope->isTop() && pin != nullptr)
				walk.pins.push_back(pin);
			if (scope->isTop() || !scope->cell->hasPort(wire->name) || bit >= GetSize(scope->cell->getPort(wire->name)))
				continue;
			RTLIL::SigBit outside = scope->cell->getPort(wire->name)[bit];
			if (!addCutPins(scope->parent, outside, WalkTarget::Loads, walk))
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
	bool in_range = wire != nullptr && at.offset < wire->width;
	if (in_range && wire->port_input && (target == WalkTarget::Loads || all_loads))
		return addCutPins(inst, RTLIL::SigBit(wire, at.offset), WalkTarget::Loads, walk);
	if (in_range && wire->port_output && target == WalkTarget::Drivers)
		return addCutPins(inst, RTLIL::SigBit(wire, at.offset), WalkTarget::Drivers, walk);
	return all_loads;
}

// an inout pin has no barrier, its old net ends the new logic, none when a pass removed that net
detail::InstanceList detail::Resolver::cellsBetween(uint32_t ref_index)
{
	const std::vector<AnchorHit> &hits = hits_by_ref_role_.get({ref_index, Anchor::Role::Barrier});
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
	return cellsUpTo(hits, ends);
}

detail::InstanceList detail::Resolver::cellsUpTo(const std::vector<AnchorHit> &hits, const pool<RTLIL::SigBit> &ends)
{
	const Netlist::Instance *scope = hits[0].scope;
	const ModWalker &walker = walkerOf(scope->module);
	std::vector<RTLIL::SigBit> todo;
	for (const AnchorHit &hit : hits)
		todo.push_back(detail::cutBit(hit.cell));
	pool<const RTLIL::Cell *> seen;
	InstanceList cells;
	while (!todo.empty()) {
		RTLIL::SigBit root = walker.sigmap(todo.back());
		todo.pop_back();
		if (ends.count(root))
			continue;
		pool<PortBit> users;
		walker.get_drivers(users, root);
		walker.get_consumers(users, root);
		for (const PortBit &at : users) {
			if (at.cell->type == ID($barrier) || !seen.insert(at.cell).second)
				continue;
			if (const Netlist::Instance *inst = view_.instance(at.cell, scope))
				cells.push_back(inst);
			for (const auto &[port, sig] : at.cell->connections()) {
				for (const RTLIL::SigBit &bit : sig)
					todo.push_back(bit); // a constant has no users
			}
		}
	}
	return detail::uniqueSorted(cells);
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
	walk.passed.insert({hit.scope, hit.cell});
	if (!addCutPins(hit.scope, hit.cell->getPort(ID::Y)[0], WalkTarget::Loads, walk))
		return {};
	return walk.pins;
}

// the nets at the anchored driver pins, else the one net that the anchored wire names
detail::NetList detail::Resolver::resolveNet(uint32_t ref_index)
{
	NetList nets;
	PinList drivers = resolvePin(ref_index);
	for (const NetPlace &place : data_.net_places_by_ref.get(ref_index)) {
		size_t found = nets.size();
		for (const Netlist::Pin *pin : drivers) {
			if (!pin->isDriver())
				continue; // a stand-in load can be on another net now
			const Netlist::Net *driven = pin->inst->isTop() ? pin->inner : pin->net;
			if (const Netlist::Net *net = netInScope(driven, place))
				nets.push_back(net);
		}
		// insbuf can leave the wire on a dead stub, so it finds the net only when no driver does
		const NetList &named = named_nets_by_place_.get(&place);
		if (nets.size() == found && named.size() == 1 && named[0] != nullptr) // two wires with the id are twins
			nets.push_back(named[0]);
	}
	return detail::uniqueSorted(nets);
}

// the connected net in the deepest scope that is the old scope or above it, else in a new scope below
// flatten leaves the net of a dissolved scope in the scope above
const Netlist::Net *detail::Resolver::netInScope(const Netlist::Net *net, const NetPlace &old) const
{
	std::map<int, NetList> found_by_depth;
	for (const Netlist::Net *connected : detail::connectedNets(net)) {
		const std::optional<std::string> &now = scope_names_[connected->scope->id];
		if (!now || (old.on_port && *now != old.scope))
			continue;
		// design -load brings back the scopes of a flat net
		if (!namesAlign(old.scope, *now) && *now != old.scope + old.dissolved)
			continue;
		// submod moves a whole net into a new scope, the one nearest to the old scope has it
		int depth = now->size();
		if (!old.scope.starts_with(*now))
			depth = -depth;
		found_by_depth[depth].push_back(connected);
	}
	if (found_by_depth.empty())
		return nullptr;
	// a feedthrough module joins several nets of one scope, the name tells them apart
	const NetList &found = found_by_depth.rbegin()->second;
	for (const Netlist::Net *candidate : found) {
		if (found.size() == 1 || candidate->name == old.name)
			return candidate;
	}
	return nullptr;
}

YOSYS_NAMESPACE_END
