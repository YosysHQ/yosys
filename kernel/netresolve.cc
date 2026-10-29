// Resolve. HitIndex finds the anchors in the view in build order, Resolver
// turns the hits of each ref into objects.
#include "kernel/nettrack_internal.h"

YOSYS_NAMESPACE_BEGIN

void NetTracker::resolve(const NetView &view, const std::vector<TrackedRef *> &refs)
{
	log_assert(view.upToDate());
	detail::HitIndex hit_index(view, *data_);
	detail::Resolver resolver(view, *data_, hit_index);
	for (uint32_t ref_index = 0; ref_index < refs.size(); ref_index++)
		resolver.resolve(ref_index, *refs[ref_index]);
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
	noteWires(scope);
}

void detail::HitIndex::noteInstance(const Netlist::Instance *inst)
{
	for (const Anchor &anchor : data_.anchors.anchorsOf(view_.design(), view_.cell(inst))) {
		bool in_own_scope = anchor.scope_path == data_.snapshot.cellScopePath(view_, inst);
		hits_by_ref_[anchor.ref_index].push_back({anchor, inst, nullptr, in_own_scope});
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
		if (anchor.bit != bit.offset)
			continue;
		bool in_own_scope = anchor.scope_path == detail::withOwnScope(data_.snapshot.scopePath(view_, net->scope), bit.wire);
		hits_by_ref_[anchor.ref_index].push_back({anchor, nullptr, net, in_own_scope});
	}
}

detail::Resolver::Resolver(const NetView &view, const TrackData &data, const HitIndex &hit_index) : view_(view), data_(data), hit_index_(hit_index) {}

void detail::Resolver::resolve(uint32_t ref_index, TrackedRef &ref)
{
	ref.result = {};
	const std::vector<AnchorHit> &hits = hit_index_.hitsOf(ref_index);
	switch (ref.kind) {
	case TrackedRef::Kind::Pin:
		ref.pins = resolvePin(hits);
		break;
	case TrackedRef::Kind::TopPort:
		ref.pins = resolvePort(hits, ref_index);
		break;
	case TrackedRef::Kind::Instance:
		ref.instances = resolveCell(hits);
		break;
	case TrackedRef::Kind::Net:
		ref.nets = resolveNet(hits, ref);
		break;
	}
}

std::vector<const Netlist::Pin *> detail::Resolver::resolvePin(const std::vector<AnchorHit> &hits)
{
	std::vector<const Netlist::Pin *> pins;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Pin)) {
		if (const Netlist::Pin *pin = hit->instance->findPin(hit->anchor.port, hit->anchor.bit))
			pins.push_back(pin);
	}
	return pins;
}

std::vector<const Netlist::Instance *> detail::Resolver::resolveCell(const std::vector<AnchorHit> &hits)
{
	std::vector<const Netlist::Instance *> cells;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Cell))
		cells.push_back(hit->instance);
	return cells;
}

std::vector<const Netlist::Pin *> detail::Resolver::resolvePort(const std::vector<AnchorHit> &hits, uint32_t ref_index)
{
	std::vector<const Netlist::Net *> nets;
	for (const AnchorHit *hit : detail::hitsOfRole(hits, Anchor::Role::Net))
		nets.push_back(hit->net);
	std::vector<const Netlist::Pin *> pins;
	for (const Netlist::Net *net : detail::uniqueSorted(nets))
		collectTopPorts(net, pins);
	pins = detail::uniqueSorted(pins);
	std::vector<const Netlist::Pin *> named = namedTopPins(ref_index);
	bool agrees = true;
	for (const Netlist::Pin *pin : named)
		agrees = agrees && std::find(pins.begin(), pins.end(), pin) != pins.end();
	if (!named.empty() && (pins.empty() || agrees))
		return detail::uniqueSorted(named);
	return pins;
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
	if (net == nullptr)
		return;
	for (const Netlist::Term *term : net->terms) {
		if (term->pin->inst->isTop())
			pins.push_back(term->pin);
		else
			collectTopPorts(term->pin->net, pins);
	}
}

std::vector<const Netlist::Pin *> detail::Resolver::leafPinsUnderScope(const Netlist::Net *net, const std::string &scope_path) const
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
	return detail::uniqueSorted(std::vector<const Netlist::Net *>(parts.begin(), parts.end()));
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

const Netlist::Pin *detail::findTopPort(const Netlist::Instance *top, const TopPortName &name)
{
	for (const Netlist::Pin *pin : top->pins) {
		if (pin->port().name == name.port && pin->hdlIndex() == name.index)
			return pin;
	}
	return nullptr;
}

YOSYS_NAMESPACE_END
