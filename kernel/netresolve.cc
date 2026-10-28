#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

void detail::HitIndex::noteInstance(const NetView &view, const EpochEndData &epoch, const Netlist::Instance *inst)
{
	ScopePaths paths = {view, epoch.snapshot};
	for (const Anchor &anchor : epoch.anchors.anchorsOf(view.design(), view.cell(inst))) {
		bool in_own_scope = anchor.scope_path == paths.cellScopePath(inst);
		hits_by_ref[anchor.ref_index].push_back({anchor, inst, nullptr, in_own_scope});
	}
}

void detail::HitIndex::noteWireBit(const NetView &view, const EpochEndData &epoch, const Netlist::Net *net, const RTLIL::SigBit &bit)
{
	ScopePaths paths = {view, epoch.snapshot};
	for (const Anchor &anchor : epoch.anchors.anchorsOf(view.design(), bit.wire)) {
		if (anchor.bit != bit.offset)
			continue;
		bool in_own_scope = anchor.scope_path == detail::withOwnScope(paths.scopePath(net->scope), bit.wire);
		hits_by_ref[anchor.ref_index].push_back({anchor, nullptr, net, in_own_scope});
	}
}

void detail::HitIndex::noteBarrier(const NetView &view, const EpochEndData &epoch, RTLIL::Cell *cell, const Netlist::Instance *scope)
{
	if (cell->type != ID($barrier))
		return;
	std::optional<int> id = detail::barrierIdOf(cell);
	if (!id)
		return;
	barrier_by_cut_bit[cell->getPort(epoch.barriers.cutPort(cell))[0]] = cell;
	ScopePaths paths = {view, epoch.snapshot};
	std::string path = detail::barrierScopePath(paths.scopePath(scope), cell);
	for (const Anchor &anchor : epoch.barriers.anchors_by_barrier.get(*id)) {
		bool pin_role = anchor.role == Anchor::Role::Pin;
		const Netlist::Instance *inst = nullptr;
		if (pin_role)
			inst = view.instance(cell, scope);
		if (!pin_role || inst != nullptr)
			hits_by_ref[anchor.ref_index].push_back({anchor, inst, nullptr, anchor.scope_path == path, cell, scope});
	}
}

const std::vector<detail::AnchorHit> &detail::HitIndex::hitsOf(uint32_t ref_index) const
{
	return hits_by_ref.get(ref_index);
}

void detail::HitIndex::clear()
{
	hits_by_ref.clear();
	barrier_by_cut_bit.clear();
}

detail::CutSideWalker::CutSideWalker(const NetView &view, const BarrierStore &barriers) : view_(view), barriers_(barriers) {}

// A cut side ends at the cut side of another barrier
void detail::CutSideWalker::pins(const RTLIL::Cell *barrier, const Netlist::Instance *scope, Anchor::Side side, std::vector<const void *> &out)
{
	WalkTarget target = WalkTarget::Loads;
	if (side == Anchor::Side::A)
		target = WalkTarget::Drivers;
	CutSideWalkState walk = {scope, target, out};
	walkBarrier(walk, barrier);
}

void detail::CutSideWalker::clear()
{
	mod_walkers_.clear();
	top_port_pin_by_bit_.clear();
}

void detail::CutSideWalker::walkBarrier(CutSideWalkState &walk, const RTLIL::Cell *barrier)
{
	CutWireSide cut_side = CutWireSide::OffCutWire;
	if ((walk.target == WalkTarget::Drivers) == barriers_.hasMark(barrier, BarrierMark::CutOnA))
		cut_side = CutWireSide::OnCutWire;
	RTLIL::SigBit start = barrier->getPort(detail::barrierPortToward(walk.target))[0];
	walkSignal(walk, barrier, start, cut_side);
}

void detail::CutSideWalker::walkSignal(CutSideWalkState &walk, const RTLIL::Cell *from, const RTLIL::SigBit &bit, CutWireSide cut_side)
{
	RTLIL::Module *module = from->module;
	const ModWalker &walker = mod_walkers_.try_emplace(module, module->design, module).first->second;
	if (const Netlist::Pin *port = topPortPinOf(bit, walker)) {
		walk.reached_pins.push_back(port);
		return;
	}
	pool<ModWalker::PortBit> users;
	walker.get_drivers(users, walker.sigmap(bit));
	walker.get_consumers(users, walker.sigmap(bit));
	for (const ModWalker::PortBit &at : users) {
		if (at.cell == from)
			continue;
		if (at.cell->type != ID($barrier))
			walkUser(walk, at);
		else if (entersBarrier(walk, at, cut_side))
			walkBarrier(walk, at.cell);
	}
}

// Toward the target, and not into the cut wire of a barrier from the cut wire
bool detail::CutSideWalker::entersBarrier(const CutSideWalkState &walk, const ModWalker::PortBit &at, CutWireSide cut_side) const
{
	bool at_a = at.port == ID::A;
	if (at_a == (walk.target == WalkTarget::Drivers))
		return false;
	return !(cut_side == CutWireSide::OnCutWire && at_a == barriers_.hasMark(at.cell, BarrierMark::CutOnA));
}

void detail::CutSideWalker::walkUser(CutSideWalkState &walk, const ModWalker::PortBit &at)
{
	const Netlist::Instance *inst = view_.instance(at.cell, walk.scope);
	if (inst == nullptr)
		return;
	const Netlist::Pin *pin = view_.pin(inst, detail::unescapedName({at.cell->module, at.port}), at.offset);
	if (pin == nullptr)
		return;
	bool toward_target = view_.isDriver(pin) == (walk.target == WalkTarget::Drivers);
	if (pin->inst->isLeaf() && toward_target)
		walk.reached_pins.push_back(pin);
	else if (!pin->inst->isLeaf() && pin->term != nullptr)
		view_.innerPins(pin->term->net, walk.target, walk.reached_pins);
}

const Netlist::Pin *detail::CutSideWalker::topPortPinOf(const RTLIL::SigBit &bit, const ModWalker &walker)
{
	const Netlist::Instance *top = view_.top();
	if (bit.wire == nullptr || walker.module != view_.module(top))
		return nullptr;
	if (bit.wire->port_id != 0)
		return view_.pin(top, detail::unescapedName(bit.wire->name), bit.offset);
	if (top_port_pin_by_bit_.empty()) {
		for (const Netlist::Pin *port : top->pins) {
			RTLIL::IdString port_id = detail::escapedPortId(view_.design(), nullptr, walker.module, view_.shape(port).name);
			RTLIL::Wire *wire = walker.module->wire(port_id);
			top_port_pin_by_bit_.emplace(walker.sigmap(RTLIL::SigBit(wire, port->bit)), port);
		}
	}
	return top_port_pin_by_bit_.at(walker.sigmap(bit), nullptr);
}

void NetView::resolve(const std::vector<TrackedRef *> &refs)
{
	log_assert(valid());
	detail::Resolver resolver(*this, epoch_, hit_index_, walker_);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		resolver.resolve(ref_index, *refs[ref_index]);
}

// submod and extract can put a new hierarchical cell on the cut side
void NetView::innerPins(const Net *net, WalkTarget target, std::vector<const void *> &out) const
{
	for (const Pin *pin : net->pins) {
		if (!detail::pinMatchesTarget(*this, pin, target))
			continue;
		if (pin->inst->isLeaf())
			out.push_back(pin);
		else if (pin->term != nullptr)
			innerPins(pin->term->net, target, out);
	}
}

detail::Resolver::Resolver(const NetView &view, const EpochEndData &epoch, const HitIndex &hit_index, CutSideWalker &walker)
    : view_(view), hit_index_(hit_index), walker_(walker), paths_{view, epoch.snapshot}
{
}

void detail::Resolver::resolve(uint32_t ref_index, TrackedRef &ref)
{
	ref.result = {};
	const std::vector<AnchorHit> &hits = hit_index_.hitsOf(ref_index);
	collectLoadsBeyondAndImagePins(hits, ref);
	ref.objects = resolveObjects(hits, ref);
	bool hier = ref.facts.isHierarchicalPin() && !ref.objects.empty();
	ref.result.found_as_leaf_pins = hier && static_cast<const Netlist::Pin *>(ref.objects[0])->inst->isLeaf();
	if (ref.kind == TrackedRef::ObjectKind::Cell)
		ref.result.port_renames = portRenames(hits, ref.objects);
}

std::vector<const void *> detail::Resolver::resolveObjects(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	switch (ref.kind) {
	case TrackedRef::ObjectKind::Pin: return resolvePin(hits, ref);
	case TrackedRef::ObjectKind::Cell: return resolveCell(hits);
	case TrackedRef::ObjectKind::Port: return resolvePort(hits, ref.request.top_port_pin);
	case TrackedRef::ObjectKind::Net: return resolveNet(hits, ref);
	}
	return {};
}

std::vector<const void *> detail::Resolver::cutSidePinsOfHits(const std::vector<AnchorHit> &hits)
{
	std::vector<const void *> pins;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier))
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, pins);
	return pins;
}

// The loads beyond the barrier of a hierarchical pin, or of the outputs of a cell
void detail::Resolver::collectLoadsBeyondAndImagePins(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	bool of_cell = ref.kind == TrackedRef::ObjectKind::Cell;
	if (!ref.facts.isHierarchicalPin() && !of_cell)
		return;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		if (of_cell && hit->anchor.side != Anchor::Side::A)
			continue;
		walker_.pins(hit->barrier, hit->barrier_scope, Anchor::Side::Y, ref.result.loads_beyond);
		const Netlist::Instance *inst = view_.instance(hit->barrier, hit->barrier_scope);
		if (inst == nullptr || inst->isLeaf())
			continue;
		ref.result.image_a_pins.push_back(view_.pin(inst, "A", 0));
		ref.result.image_y_pins.push_back(view_.pin(inst, "Y", 0));
	}
}

std::vector<const void *> detail::Resolver::resolvePin(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	std::vector<const void *> pins;
	std::vector<const Netlist::Instance *> renamed, renamed_leaves;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Pin)) {
		const Netlist::Pin *pin = view_.pin(hit->instance, hit->anchor.port, hit->anchor.bit);
		if (pin == nullptr && hit->instance->isLeaf())
			renamed_leaves.push_back(hit->instance);
		else if (pin == nullptr)
			renamed.push_back(hit->instance);
		else if (hit->instance->isLeaf())
			ref.result.exact_pins.push_back(pin);
		else
			pins.push_back(pin);
	}
	if (!ref.result.image_a_pins.empty())
		pins.clear();
	if (!pins.empty())
		return pins;
	pins = cutSidePinsOfHits(hits);
	if (!renamed_leaves.empty())
		ref.result.exact_pins = pinsBehindNewLogic(renamed_leaves, pins);
	if (!renamed.empty())
		return detail::hierPinsAbove(renamed, pins);
	if (pins.empty())
		return ref.result.exact_pins;
	return detail::uniqueSorted(pins);
}

// Leaf cells whose port a pass renamed (dfflibmap maps C to CK)
std::vector<const void *> detail::Resolver::pinsBehindNewLogic(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &cut) const
{
	std::vector<const void *> found;
	std::vector<const void *> todo = cut;
	pool<const Netlist::Instance *> seen;
	while (!todo.empty()) {
		const Netlist::Pin *pin = static_cast<const Netlist::Pin *>(todo.back());
		todo.pop_back();
		if (std::find(insts.begin(), insts.end(), pin->inst) != insts.end())
			found.push_back(pin);
		else if (pin->inst->isLeaf() && !view_.isRegister(pin->inst) && seen.insert(pin->inst).second)
			addOutputLoads(pin->inst, todo);
	}
	return detail::uniqueSorted(found);
}

void detail::Resolver::addOutputLoads(const Netlist::Instance *inst, std::vector<const void *> &loads) const
{
	for (const Netlist::Pin *out : inst->pins) {
		if (out->net != nullptr && view_.dir(out) == Netlist::Dir::Output)
			loads.insert(loads.end(), out->net->pins.begin(), out->net->pins.end());
	}
}

std::vector<const void *> detail::Resolver::resolveCell(const std::vector<AnchorHit> &hits)
{
	std::vector<const void *> cells;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Cell))
		cells.push_back(hit->instance);
	if (!cells.empty())
		return cells;
	for (const void *pin : cutSidePinsOfHits(hits))
		cells.push_back(static_cast<const Netlist::Pin *>(pin)->inst);
	return detail::uniqueSorted(cells);
}

std::vector<const void *> detail::Resolver::resolvePort(const std::vector<AnchorHit> &hits, const void *top_port_pin)
{
	std::vector<const void *> nets;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net))
		nets.push_back(hit->net);
	std::vector<const void *> pins;
	if (nets.empty()) {
		for (const void *object : cutSidePinsOfHits(hits)) {
			const Netlist::Pin *pin = static_cast<const Netlist::Pin *>(object);
			if (view_.isTop(pin->inst))
				pins.push_back(pin);
			else
				nets.push_back(pin->net);
		}
	}
	for (const void *net : detail::uniqueSorted(nets))
		collectTopPorts(static_cast<const Netlist::Net *>(net), pins);
	pins = detail::uniqueSorted(pins);
	bool agrees = pins.empty() || std::find(pins.begin(), pins.end(), top_port_pin) != pins.end();
	if (top_port_pin != nullptr && agrees)
		return {top_port_pin};
	return pins;
}

void detail::Resolver::collectTopPorts(const Netlist::Net *net, std::vector<const void *> &pins) const
{
	if (net == nullptr)
		return;
	for (const Netlist::Term *term : net->terms) {
		if (view_.isTop(term->pin->inst))
			pins.push_back(term->pin);
		else
			collectTopPorts(term->pin->net, pins);
	}
}

std::vector<const void *> detail::Resolver::leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const
{
	std::vector<const void *> pins;
	for (const Netlist::Pin *pin : net->pins) {
		std::string path = paths_.cellScopePath(pin->inst);
		bool under = scope_path.empty() || path == scope_path || path.starts_with(scope_path + "/");
		if (pin->inst->isLeaf() && under)
			pins.push_back(pin);
	}
	return pins;
}

const Netlist::Net *detail::Resolver::netInScope(const Netlist::Net *net, const std::string &scope_path) const
{
	pool<const Netlist::Net *> seen;
	std::vector<const Netlist::Net *> todo = {net};
	while (!todo.empty()) {
		const Netlist::Net *at = todo.back();
		todo.pop_back();
		if (at == nullptr || !seen.insert(at).second)
			continue;
		if (paths_.scopePath(at->scope) == scope_path)
			return at;
		for (const Netlist::Term *term : at->terms)
			todo.push_back(term->pin->net);
		for (const Netlist::Pin *pin : at->pins) {
			if (pin->term != nullptr)
				todo.push_back(pin->term->net);
		}
	}
	return net;
}

std::vector<const void *> detail::Resolver::resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	std::vector<const void *> nets;
	pool<const void *> outer;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net)) {
		nets.push_back(hit->net);
		bool in_old_scope = paths_.scopePath(hit->net->scope) == hit->anchor.net_scope_path;
		if (in_old_scope || !outer.insert(hit->net).second)
			continue;
		std::vector<const void *> inside = leafPinsUnderScope(hit->net, hit->anchor.net_scope_path);
		std::vector<const void *> &through_pins = ref.result.through_pins;
		if (inside.size() < hit->net->pins.size())
			through_pins.insert(through_pins.end(), inside.begin(), inside.end());
	}
	if (!nets.empty())
		return detail::uniqueSorted(nets);
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		std::vector<const void *> pins;
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, pins);
		for (const void *pin : pins)
			nets.push_back(netInScope(static_cast<const Netlist::Pin *>(pin)->net, hit->anchor.net_scope_path));
	}
	return detail::uniqueSorted(nets);
}

// dfflibmap renames C to CK, abc swaps inputs
std::vector<PortRename> detail::Resolver::portRenames(const std::vector<AnchorHit> &hits, const std::vector<const void *> &cells)
{
	std::vector<PortRename> renames;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		std::vector<const void *> pins;
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, pins);
		for (const void *object : pins) {
			const Netlist::Pin *pin = static_cast<const Netlist::Pin *>(object);
			if (std::find(cells.begin(), cells.end(), pin->inst) != cells.end())
				renames.push_back({hit->anchor.port, view_.shape(pin).name, pin->inst});
		}
	}
	return renames;
}

Netlist::Dir detail::pinDirOfTarget(WalkTarget target)
{
	if (target == WalkTarget::Drivers)
		return Netlist::Dir::Output;
	return Netlist::Dir::Input;
}

RTLIL::IdString detail::barrierPortToward(WalkTarget target)
{
	if (target == WalkTarget::Drivers)
		return ID::A;
	return ID::Y;
}

bool detail::pinMatchesTarget(const Netlist &netlist, const Netlist::Pin *pin, WalkTarget target)
{
	if (pin->inst->isLeaf())
		return netlist.isDriver(pin) == (target == WalkTarget::Drivers);
	return netlist.dir(pin) == detail::pinDirOfTarget(target);
}

std::vector<const detail::AnchorHit *> detail::hitsOfRole(const std::vector<AnchorHit> &hits, Anchor::Role role)
{
	std::vector<const AnchorHit *> own, all;
	bool shared = false;
	for (const AnchorHit &hit : hits) {
		if (hit.anchor.role != role)
			continue;
		all.push_back(&hit);
		shared = shared || hit.anchor.in_shared_module;
		if (hit.in_own_scope)
			own.push_back(&hit);
	}
	if (!own.empty())
		return own;
	if (!shared)
		return all;
	return {};
}

std::vector<const void *> detail::uniqueSorted(std::vector<const void *> objects)
{
	std::sort(objects.begin(), objects.end());
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

// Hierarchical pins whose port splitnets -ports renamed, up from the leaf pins
std::vector<const void *> detail::hierPinsAbove(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &leaves)
{
	std::vector<const void *> found;
	for (const void *leaf : leaves) {
		const Netlist::Net *net = static_cast<const Netlist::Pin *>(leaf)->net;
		while (net != nullptr && !net->terms.empty()) {
			const Netlist::Pin *outer = net->terms.front()->pin;
			if (std::find(insts.begin(), insts.end(), outer->inst) != insts.end()) {
				found.push_back(outer);
				break;
			}
			net = outer->net;
		}
	}
	return detail::uniqueSorted(found);
}

YOSYS_NAMESPACE_END
