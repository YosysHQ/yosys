// Resolve. HitIndex finds the anchors in the view in build order, Resolver
// turns the hits of each ref into objects.
#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

void NetTracker::resolve(const NetView &view, const std::vector<TrackedRef *> &refs)
{
	detail::HitIndex hit_index(view, *data_);
	detail::CutSideWalker walker(view, *data_);
	detail::Resolver resolver(view, *data_, hit_index, walker);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		resolver.resolve(ref_index, *refs[ref_index]);
}

bool detail::isNewBuffer(const NetView &view, const Snapshot &snapshot, const Netlist::Instance *inst)
{
	if (!inst->isLeaf() || snapshot.cell_names.count(view.cell(inst)->hashidx_))
		return false;
	return view.isBuffer(inst) && !snapshot.cell_paths.count(snapshot.scopePath(view, inst));
}

detail::HitIndex::HitIndex(const NetView &view, const TrackData &data) : view_(view), data_(data) { noteScope(view.top()); }

const std::vector<detail::AnchorHit> &detail::HitIndex::hitsOf(uint32_t ref_index) const { return hits_by_ref_.get(ref_index); }

void detail::HitIndex::noteScope(const Netlist::Instance *scope)
{
	for (const Netlist::Instance *child : scope->children) {
		noteInstance(child);
		if (child->kind == Netlist::Instance::Kind::Module)
			noteScope(child);
	}
	for (const RTLIL::Cell *cell : view_.module(scope)->cells())
		noteBarrier(cell, scope);
	noteWires(scope);
}

void detail::HitIndex::noteInstance(const Netlist::Instance *inst)
{
	for (const Anchor &anchor : data_.anchors.anchorsOf(view_.design(), view_.cell(inst))) {
		if (anchor.role != Anchor::Role::Cell && anchor.role != Anchor::Role::Pin)
			continue;
		bool in_own_scope = anchor.scope_path == data_.snapshot.cellScopePath(view_, inst);
		hits_by_ref_[anchor.ref_index].push_back({anchor, inst, nullptr, in_own_scope});
	}
}

void detail::HitIndex::noteBarrier(const RTLIL::Cell *cell, const Netlist::Instance *scope)
{
	if (cell->type != ID($barrier))
		return;
	std::optional<int> id = detail::barrierIdOf(cell);
	if (!id)
		return;
	std::string path = detail::barrierScopePath(data_.snapshot.scopePath(view_, scope), cell);
	for (const Anchor &anchor : data_.barriers.anchors_by_barrier.get(*id)) {
		bool pin_role = anchor.role == Anchor::Role::Pin;
		const Netlist::Instance *inst = nullptr;
		if (pin_role)
			inst = view_.instance(cell, scope);
		if (!pin_role || inst != nullptr)
			hits_by_ref_[anchor.ref_index].push_back({anchor, inst, nullptr, anchor.scope_path == path, cell, scope});
	}
}

void detail::HitIndex::noteWires(const Netlist::Instance *scope)
{
	dict<RTLIL::SigBit, const Netlist::Net *> net_of_bit;
	for (RTLIL::Wire *wire : view_.module(scope)->wires()) {
		if (data_.anchors.anchorsOf(view_.design(), wire).empty())
			continue;
		if (net_of_bit.empty())
			net_of_bit = netsOfWireBits(scope);
		for (int offset = 0; offset < wire->width; offset++) {
			RTLIL::SigBit bit(wire, offset);
			if (const Netlist::Net *net = net_of_bit.at(bit, nullptr))
				noteWireBit(net, bit);
		}
	}
}

dict<RTLIL::SigBit, const Netlist::Net *> detail::HitIndex::netsOfWireBits(const Netlist::Instance *scope) const
{
	dict<RTLIL::SigBit, const Netlist::Net *> net_of_bit;
	for (const Netlist::Net *net : view_.nets(scope)) {
		for (const RTLIL::SigBit &bit : view_.wireBits(net))
			net_of_bit[bit] = net;
	}
	return net_of_bit;
}

void detail::HitIndex::noteWireBit(const Netlist::Net *net, const RTLIL::SigBit &bit)
{
	for (const Anchor &anchor : data_.anchors.anchorsOf(view_.design(), bit.wire)) {
		if (anchor.role != Anchor::Role::Net || anchor.bit != bit.offset)
			continue;
		bool in_own_scope = anchor.scope_path == detail::withOwnScope(data_.snapshot.scopePath(view_, net->scope), bit.wire);
		hits_by_ref_[anchor.ref_index].push_back({anchor, nullptr, net, in_own_scope});
	}
}

detail::Resolver::Resolver(const NetView &view, const TrackData &data, const HitIndex &hit_index, CutSideWalker &walker)
    : view_(view), data_(data), hit_index_(hit_index), walker_(walker)
{
}

void detail::Resolver::resolve(uint32_t ref_index, TrackedRef &ref)
{
	ref.result = {};
	const std::vector<AnchorHit> &hits = hit_index_.hitsOf(ref_index);
	collectLoadsBeyondAndBarrierPins(hits, ref);
	switch (ref.kind) {
	case TrackedRef::Kind::Pin: {
		ResolvedPin resolved = resolvePin(hits, ref);
		ref.pins = std::move(resolved.pins);
		ref.result.own_pins = std::move(resolved.own_pins);
		addTopPins(hits, ref_index, ref);
		break;
	}
	case TrackedRef::Kind::TopPort:
		ref.pins = resolvePort(hits, ref_index);
		break;
	case TrackedRef::Kind::Instance:
		ref.instances = resolveCell(hits);
		ref.result.port_renames = portRenames(hits, ref.instances);
		break;
	case TrackedRef::Kind::Net:
		ref.nets = resolveNet(hits, ref);
		break;
	}
	bool any_leaf = false, any_hier = false;
	for (const Netlist::Pin *pin : ref.pins) {
		any_leaf = any_leaf || pin->inst->isLeaf();
		any_hier = any_hier || (!pin->inst->isLeaf() && !pin->inst->isTop());
	}
	ref.result.flattened_hier_pin = ref.origin.isHierarchicalPin() && any_leaf && !any_hier;
}

std::vector<const Netlist::Pin *> detail::Resolver::cutSidePinsOfHits(const std::vector<AnchorHit> &hits)
{
	std::vector<const Netlist::Pin *> pins;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier))
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, BufferRule::PassNewBuffer, pins);
	return pins;
}

// The loads beyond the barrier of a hierarchical pin, or of the outputs of a cell
void detail::Resolver::collectLoadsBeyondAndBarrierPins(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	bool of_cell = ref.kind == TrackedRef::Kind::Instance;
	if (!ref.origin.isHierarchicalPin() && !of_cell)
		return;
	std::vector<const AnchorHit *> barrier_hits = detail::hitsOfRole(hits, Anchor::Role::Barrier);
	bool port_cuts = false;
	for (const AnchorHit *hit : barrier_hits)
		port_cuts = port_cuts || data_.barriers.marks(hit->barrier).port_cut;
	for (const AnchorHit *hit : barrier_hits) {
		if (of_cell && hit->anchor.side != Anchor::Side::A)
			continue;
		if (!of_cell && port_cuts && !data_.barriers.marks(hit->barrier).port_cut)
			continue;
		walker_.pins(hit->barrier, hit->barrier_scope, Anchor::Side::Y, BufferRule::StopAtNewBuffer, ref.result.loads_beyond);
		const Netlist::Instance *inst = view_.instance(hit->barrier, hit->barrier_scope);
		if (inst == nullptr)
			continue;
		ref.result.barrier_a_pins.push_back(inst->findPin("A", 0));
		ref.result.barrier_y_pins.push_back(inst->findPin("Y", 0));
	}
}

detail::ResolvedPin detail::Resolver::resolvePin(const std::vector<AnchorHit> &hits, const TrackedRef &ref)
{
	std::vector<const Netlist::Pin *> own_pins, hier_pins, uncut;
	std::vector<const Netlist::Instance *> renamed, renamed_leaves;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Pin)) {
		const Netlist::Pin *pin = hit->instance->findPin(hit->anchor.port, hit->anchor.bit);
		if (pin == nullptr && hit->instance->isLeaf())
			renamed_leaves.push_back(hit->instance);
		else if (pin == nullptr)
			renamed.push_back(hit->instance);
		else if (hit->instance->isLeaf())
			own_pins.push_back(pin);
		else
			hier_pins.push_back(pin);
		if (pin != nullptr && hit->anchor.uncut)
			uncut.push_back(pin);
	}
	bool beside_barrier_instance = !ref.result.barrier_a_pins.empty();
	// beside a Barrier instance, hierarchical pins take the leaf rules
	if (beside_barrier_instance) {
		hier_pins.clear();
		renamed.clear();
	}
	InstanceList hier_insts = renamed;
	for (const Netlist::Pin *pin : hier_pins)
		hier_insts.push_back(pin->inst);
	auto [cut, flattened, inside] = leafCutSides(hits, hier_insts);
	if (!renamed.empty()) {
		PinList above = detail::hierPinsAbove(renamed, inside, ref.origin.hier_pin_dir);
		hier_pins.insert(hier_pins.end(), above.begin(), above.end());
	}
	// a leaf pin with a barrier resolves to its cut side
	// without barriers the own pins are the result
	std::vector<const Netlist::Pin *> pins = uncut;
	if (cut.empty())
		pins = own_pins;
	pins.insert(pins.end(), cut.begin(), cut.end());
	pins.insert(pins.end(), hier_pins.begin(), hier_pins.end());
	own_pins.insert(own_pins.end(), hier_pins.begin(), hier_pins.end());
	own_pins.insert(own_pins.end(), flattened.begin(), flattened.end());
	if (!renamed_leaves.empty()) {
		std::vector<const Netlist::Pin *> behind = pinsBehindNewLogic(renamed_leaves, cut);
		own_pins.insert(own_pins.end(), behind.begin(), behind.end());
	}
	return {detail::uniqueSorted(pins), detail::uniqueSorted(own_pins)};
}

// cut sides of the leaf pins of the ref
// port cuts in its hierarchical instances lead to ports splitnets -ports renamed
// other port cuts hold a flattened pin or one a Barrier instance keeps
detail::LeafCutSides detail::Resolver::leafCutSides(const std::vector<AnchorHit> &hits, const InstanceList &hier_insts)
{
	LeafCutSides sides;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		std::vector<const Netlist::Pin *> *out = &sides.cut;
		BarrierMarks marks = data_.barriers.marks(hit->barrier);
		bool in_hier_pin = std::find(hier_insts.begin(), hier_insts.end(), hit->barrier_scope) != hier_insts.end();
		if (in_hier_pin && marks.port_cut)
			out = &sides.inside;
		else if (marks.port_cut)
			out = &sides.flattened;
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, BufferRule::StopAtNewBuffer, *out);
	}
	sides.cut.insert(sides.cut.end(), sides.flattened.begin(), sides.flattened.end());
	return sides;
}

detail::PinList detail::Resolver::pinsBehindNewLogic(const InstanceList &insts, const PinList &cut) const
{
	std::vector<const Netlist::Pin *> found;
	std::vector<const Netlist::Pin *> todo = cut;
	pool<const Netlist::Instance *> seen;
	while (!todo.empty()) {
		const Netlist::Pin *pin = todo.back();
		todo.pop_back();
		if (std::find(insts.begin(), insts.end(), pin->inst) != insts.end())
			found.push_back(pin);
		else if (pin->inst->isLeaf() && !view_.isRegister(pin->inst) && seen.insert(pin->inst).second)
			addOutputLoads(pin->inst, todo);
	}
	return detail::uniqueSorted(found);
}

void detail::Resolver::addOutputLoads(const Netlist::Instance *inst, std::vector<const Netlist::Pin *> &loads) const
{
	for (const Netlist::Pin *out : inst->pins) {
		if (out->net != nullptr && (out->dir() == Netlist::PortDir::Output || out->dir() == Netlist::PortDir::Inout))
			loads.insert(loads.end(), out->net->pins.begin(), out->net->pins.end());
	}
}

std::vector<const Netlist::Instance *> detail::Resolver::resolveCell(const std::vector<AnchorHit> &hits)
{
	std::vector<const Netlist::Instance *> cells;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Cell))
		cells.push_back(hit->instance);
	if (!cells.empty())
		return cells;
	for (const Netlist::Pin *pin : cutSidePinsOfHits(hits))
		cells.push_back(pin->inst);
	return detail::uniqueSorted(cells);
}

std::vector<const Netlist::Pin *> detail::Resolver::resolvePort(const std::vector<AnchorHit> &hits, uint32_t ref_index)
{
	std::vector<const Netlist::Net *> nets;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net))
		nets.push_back(hit->net);
	std::vector<const Netlist::Pin *> pins;
	if (nets.empty()) {
		for (const Netlist::Pin *pin : cutSidePinsOfHits(hits)) {
			if (pin->inst->isTop())
				pins.push_back(pin);
			else
				nets.push_back(pin->net);
		}
	}
	for (const Netlist::Net *net : nets)
		collectTopPorts(net, pins);
	pins = checkpointedPorts(detail::uniqueSorted(pins), ref_index);
	std::vector<const Netlist::Pin *> named = namedTopPins(ref_index);
	bool agrees = true;
	for (const Netlist::Pin *pin : named)
		agrees = agrees && std::find(pins.begin(), pins.end(), pin) != pins.end();
	if (!named.empty() && (pins.empty() || agrees))
		return detail::uniqueSorted(named);
	return pins;
}

void detail::Resolver::addTopPins(const std::vector<AnchorHit> &hits, uint32_t ref_index, TrackedRef &ref)
{
	std::vector<const Netlist::Pin *> ports = topPinsOfRef(hits, ref_index);
	ref.pins.insert(ref.pins.end(), ports.begin(), ports.end());
	ref.result.own_pins.insert(ref.result.own_pins.end(), ports.begin(), ports.end());
	ref.pins = detail::uniqueSorted(ref.pins);
	ref.result.own_pins = detail::uniqueSorted(ref.result.own_pins);
}

// A name moved if a name finds no pin or a named pin is on a net with no anchor (a constant net has none)
detail::PinList detail::Resolver::topPinsOfRef(const std::vector<AnchorHit> &hits, uint32_t ref_index) const
{
	std::vector<const Netlist::Pin *> named = namedTopPins(ref_index);
	pool<const Netlist::Net *> anchored, named_nets;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net))
		anchored.insert(hit->net);
	std::vector<const Netlist::Pin *> on_anchors;
	for (const Netlist::Pin *pin : named) {
		bool unchecked = pin->inner == nullptr || pin->inner->constant != Netlist::Net::Const::None;
		if (pin->inner != nullptr)
			named_nets.insert(pin->inner);
		if (unchecked || anchored.count(pin->inner))
			on_anchors.push_back(pin);
	}
	std::vector<const Netlist::Pin *> lost_names;
	for (const Netlist::Net *net : anchored) {
		if (!named_nets.count(net))
			collectTopPorts(net, lost_names);
	}
	lost_names = checkpointedPorts(lost_names, ref_index);
	if (on_anchors.size() == data_.top_ports_by_ref.get(ref_index).size() || lost_names.empty())
		return named;
	on_anchors.insert(on_anchors.end(), lost_names.begin(), lost_names.end());
	return on_anchors;
}

std::vector<const Netlist::Pin *> detail::Resolver::namedTopPins(uint32_t ref_index) const
{
	std::vector<const Netlist::Pin *> pins;
	for (const TopPortName &name : data_.top_ports_by_ref.get(ref_index)) {
		if (const Netlist::Pin *pin = detail::findTopPort(view_.top(), name))
			pins.push_back(pin);
	}
	return pins;
}

void detail::Resolver::collectTopPorts(const Netlist::Net *net, std::vector<const Netlist::Pin *> &pins) const
{
	for (const Netlist::Net *above : detail::connectedNets(net, false)) {
		for (const Netlist::Pin *port : above->boundary) {
			if (port->inst->isTop())
				pins.push_back(port);
		}
	}
}

// ports whose wire bit has a ref Port anchor, else all
detail::PinList detail::Resolver::checkpointedPorts(const PinList &ports, uint32_t ref_index) const
{
	std::vector<const Netlist::Pin *> on_wire;
	for (const Netlist::Pin *top_pin : ports) {
		RTLIL::SigBit bit = detail::portBit(view_, top_pin);
		if (bit.wire == nullptr)
			continue;
		for (const Anchor &anchor : data_.anchors.anchorsOf(view_.design(), bit.wire)) {
			bool same_ref_bit = anchor.ref_index == ref_index && anchor.bit == bit.offset;
			if (anchor.role == Anchor::Role::Port && same_ref_bit) {
				on_wire.push_back(top_pin);
				break;
			}
		}
	}
	if (on_wire.empty())
		return ports;
	return on_wire;
}

detail::PinList detail::Resolver::leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const
{
	std::vector<const Netlist::Pin *> pins;
	for (const Netlist::Pin *pin : net->pins) {
		std::string path = data_.snapshot.cellScopePath(view_, pin->inst);
		bool under = scope_path.empty() || path == scope_path || path.starts_with(scope_path + "/");
		if (pin->inst->isLeaf() && under)
			pins.push_back(pin);
	}
	return pins;
}

const Netlist::Net *detail::Resolver::netInScope(const Netlist::Net *net, const std::string &scope_path) const
{
	for (const Netlist::Net *connected : detail::connectedNets(net, true)) {
		if (data_.snapshot.scopePath(view_, connected->scope) == scope_path)
			return connected;
	}
	return net;
}

const Netlist::Net *detail::Resolver::newBufferInput(const Netlist::Net *net) const
{
	for (const Netlist::Pin *pin : net->pins) {
		if (!detail::isNewBuffer(view_, data_.snapshot, pin->inst) || !pin->isDriver())
			continue;
		for (const Netlist::Pin *input : pin->inst->pins) {
			if (input != pin && input->net != nullptr)
				return input->net;
		}
	}
	return nullptr;
}

const Netlist::Net *detail::Resolver::newBufferRoot(const Netlist::Net *net) const
{
	pool<const Netlist::Net *> seen = {net};
	while (const Netlist::Net *input = newBufferInput(net)) {
		if (!seen.insert(input).second)
			break;
		net = input;
	}
	return net;
}

// insbuf splits a net with buffers, so the parts that no other part drives keep its meaning, and the part that drives them all when there are several
std::vector<const Netlist::Net *> detail::Resolver::bufferSplitRoots(const pool<const Netlist::Net *> &parts) const
{
	std::vector<const Netlist::Net *> roots;
	for (const Netlist::Net *part : parts) {
		if (!parts.count(newBufferInput(part)))
			roots.push_back(part);
	}
	if (roots.size() < 2)
		return roots;
	for (const Netlist::Net *&root : roots)
		root = newBufferRoot(root);
	return detail::uniqueSorted(roots);
}

std::vector<const Netlist::Net *> detail::Resolver::resolveNet(const std::vector<AnchorHit> &hits, TrackedRef &ref)
{
	pool<const Netlist::Net *> outer;
	pool<const Netlist::Net *> parts;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net)) {
		parts.insert(hit->net);
		bool in_old_scope = data_.snapshot.scopePath(view_, hit->net->scope) == hit->anchor.net_scope_path;
		if (in_old_scope || !outer.insert(hit->net).second)
			continue;
		std::vector<const Netlist::Pin *> inside = leafPinsUnderScope(hit->net, hit->anchor.net_scope_path);
		std::vector<const Netlist::Pin *> &old_scope_pins = ref.result.old_scope_pins;
		if (inside.size() < hit->net->pins.size())
			old_scope_pins.insert(old_scope_pins.end(), inside.begin(), inside.end());
	}
	if (!parts.empty())
		return bufferSplitRoots(parts);
	std::vector<const Netlist::Net *> nets;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		std::vector<const Netlist::Pin *> pins;
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, BufferRule::PassNewBuffer, pins);
		for (const Netlist::Pin *pin : pins)
			nets.push_back(netInScope(pin->net, hit->anchor.net_scope_path));
	}
	return detail::uniqueSorted(nets);
}

// dfflibmap renames C to CK, abc swaps inputs
std::vector<PortRename> detail::Resolver::portRenames(const std::vector<AnchorHit> &hits, const InstanceList &insts)
{
	bool same_cells = !detail::hitsOfRole(hits, Anchor::Role::Cell).empty();
	std::vector<PortRename> renames;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Barrier)) {
		std::vector<const Netlist::Pin *> pins;
		walker_.pins(hit->barrier, hit->barrier_scope, hit->anchor.side, BufferRule::PassNewBuffer, pins);
		for (const Netlist::Pin *pin : pins) {
			bool identity = same_cells && pin->port().name == hit->anchor.port && pin->bit == hit->anchor.bit;
			if (!identity && std::find(insts.begin(), insts.end(), pin->inst) != insts.end())
				renames.push_back({hit->anchor.port, hit->anchor.bit, pin});
		}
	}
	return renames;
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

// Hierarchical pins of dir or inout whose port splitnets -ports renamed, up from the leaf pins through all boundaries (a feedthrough has both)
detail::PinList detail::hierPinsAbove(const InstanceList &insts, const PinList &leaves, Netlist::PortDir dir)
{
	std::vector<const Netlist::Pin *> found;
	std::vector<const Netlist::Net *> todo;
	for (const Netlist::Pin *leaf : leaves)
		todo.push_back(leaf->net);
	pool<const Netlist::Net *> seen;
	while (!todo.empty()) {
		const Netlist::Net *net = todo.back();
		todo.pop_back();
		if (net == nullptr || !seen.insert(net).second)
			continue;
		for (const Netlist::Pin *outer : net->boundary) {
			bool target = std::find(insts.begin(), insts.end(), outer->inst) != insts.end();
			if (!target)
				todo.push_back(outer->net);
			else if (outer->dir() == dir || outer->dir() == Netlist::PortDir::Inout)
				found.push_back(outer);
		}
	}
	return detail::uniqueSorted(found);
}

const Netlist::Pin *detail::findTopPort(const Netlist::Instance *top, const TopPortName &name)
{
	for (const Netlist::Pin *pin : top->pins) {
		if (pin->port().name == name.port && pin->hdlIndex() == name.index)
			return pin;
	}
	return nullptr;
}

YOSYS_NAMESPACE_END
