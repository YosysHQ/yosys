// Anchors find the objects of refs again after passes. anchor() puts the
// anchors of each object into the anchor table, the netview_ref attribute of a
// cell or wire holds the index of its anchors there. Roles:
//   Pin   on a cell  ref, scope, port, bit
//   Cell  on a cell  ref, scope
//   Net   on a wire  ref, scope, bit, wire scope
#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

void NetView::anchor(const std::vector<Found *> &refs)
{
	log_assert(valid());
	clearAnchors(design_);
	for (uint32_t ref = 0; ref < refs.size(); ref++) {
		const Found &found = *refs[ref];
		for (const void *object : found.objects)
			anchorRef(object, ref, found.kind);
	}
}

RTLIL::IdString detail::refId(RTLIL::Design *design, bool add)
{
	if (add)
		return design->twines().add("\\netview_ref");
	return design->twines().find("\\netview_ref");
}

void NetView::addAnchor(RTLIL::AttrObject *object, const detail::Anchor &anchor)
{
	std::vector<std::vector<detail::Anchor>> &table = anchor_table_;
	RTLIL::IdString id = detail::refId(design_, true);
	if (!object->has_attribute(id)) {
		object->attributes[id] = RTLIL::Const(int(table.size()));
		table.emplace_back();
	}
	table[object->attributes.at(id).as_int()].push_back(anchor);
}

// An object of a shared module holds the anchors of all its occurrences, and so
// do its flattened copies. The scope picks the own one
bool NetView::markIfShared(RTLIL::AttrObject *object, RTLIL::Module *module)
{
	if (scopes(module).size() < 2)
		return false;
	detail::markScope(object);
	return true;
}

// Without -scopename, flatten extends the 'scopename' of a private object only
// if it has one
void detail::markScope(RTLIL::AttrObject *object)
{
	if (!object->has_attribute(ID::hdlname) && !object->has_attribute(ID(scopename)))
		object->attributes[ID(scopename)] = RTLIL::Const(std::string());
}

void NetView::anchorCell(const Instance *inst, detail::Anchor anchor)
{
	RTLIL::Cell *cell = this->cell(inst);
	anchor.in_shared_module = markIfShared(cell, cell->module);
	addAnchor(cell, anchor);
}

void NetView::anchorWires(const Net *net, uint32_t ref)
{
	if (net == nullptr || net->constant != Net::Const::None)
		return;
	std::string path = detail::scopePath(net->scope);
	for (const RTLIL::SigBit &bit : wireBits(net)) {
		bool shared = markIfShared(bit.wire, bit.wire->module);
		addAnchor(bit.wire, {detail::Anchor::Role::Net, ref, detail::withOwnScope(path, bit.wire), "", bit.offset, path, shared});
	}
}

void NetView::anchorRef(const void *object, uint32_t ref, Found::Kind kind)
{
	if (kind == Found::Kind::Net)
		return anchorWires(static_cast<const Net *>(object), ref);
	if (kind == Found::Kind::Cell) {
		const Instance *inst = static_cast<const Instance *>(object);
		return anchorCell(inst, {detail::Anchor::Role::Cell, ref, cellScope(inst), "", 0, "", false});
	}
	const Pin *pin = static_cast<const Pin *>(object);
	if (isTop(pin->inst)) {
		if (pin->term != nullptr)
			anchorWires(pin->term->net, ref);
		return;
	}
	anchorCell(pin->inst, {detail::Anchor::Role::Pin, ref, cellScope(pin->inst), shape(pin).name, pin->bit, "", false});
}

void NetView::clearAnchors(RTLIL::Design *design)
{
	anchor_table_.clear();
	RTLIL::IdString id = detail::refId(design, false);
	if (id == RTLIL::IdString::Null)
		return;
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Cell *cell : module->cells())
			cell->attributes.erase(id);
		for (RTLIL::Wire *wire : module->wires())
			wire->attributes.erase(id);
	}
}

const std::vector<detail::Anchor> &NetView::anchorsOf(const RTLIL::AttrObject *object) const
{
	static const std::vector<detail::Anchor> none;
	const std::vector<std::vector<detail::Anchor>> &table = anchor_table_;
	if (table.empty())
		return none;
	RTLIL::IdString id = detail::refId(design_, false);
	if (!object->has_attribute(id))
		return none;
	size_t index = object->attributes.at(id).as_int();
	return index < table.size() ? table[index] : none;
}

void NetView::addNetHits(const Net *net, const RTLIL::SigBit &bit)
{
	for (const detail::Anchor &anchor : anchorsOf(bit.wire)) {
		if (anchor.bit != bit.offset)
			continue;
		bool in_own_scope = anchor.scope == detail::withOwnScope(detail::scopePath(net->scope), bit.wire);
		hits_[anchor.ref].push_back({anchor, nullptr, net, in_own_scope});
	}
}

// The hits of a role in their own scope, else all of them, but none if one is
// of a shared module
std::vector<const detail::Hit *> detail::pick(const std::vector<Hit> &hits, Anchor::Role role)
{
	std::vector<const Hit *> own, all;
	bool shared = false;
	for (const Hit &hit : hits) {
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

std::vector<const void *> NetView::resolvePin(const std::vector<detail::Hit> &hits)
{
	std::vector<const void *> pins;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Pin)) {
		const Pin *pin = this->pin(hit->inst, hit->anchor.port, hit->anchor.bit);
		if (pin != nullptr)
			pins.push_back(pin);
	}
	return pins;
}

std::vector<const void *> NetView::resolveCell(const std::vector<detail::Hit> &hits)
{
	std::vector<const void *> cells;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Cell))
		cells.push_back(hit->inst);
	return cells;
}

std::vector<const void *> detail::unique(std::vector<const void *> objects)
{
	std::sort(objects.begin(), objects.end());
	objects.erase(std::unique(objects.begin(), objects.end()), objects.end());
	return objects;
}

// The leaf pins of a net in a scope or below
std::vector<const void *> NetView::pinsUnder(const Net *net, const std::string &scope) const
{
	std::vector<const void *> pins;
	for (const Pin *pin : net->pins) {
		std::string path = cellScope(pin->inst);
		if (pin->inst->leaf && (scope.empty() || path == scope || path.starts_with(scope + "/")))
			pins.push_back(pin);
	}
	return pins;
}

std::vector<const void *> NetView::resolveNet(const std::vector<detail::Hit> &hits, Found &ref)
{
	std::vector<const void *> nets;
	pool<const void *> outer;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Net)) {
		nets.push_back(hit->net);
		if (detail::scopePath(hit->net->scope) == hit->anchor.wire_scope || !outer.insert(hit->net).second)
			continue;
		std::vector<const void *> inside = pinsUnder(hit->net, hit->anchor.wire_scope);
		if (inside.size() < hit->net->pins.size())
			ref.through_pins.insert(ref.through_pins.end(), inside.begin(), inside.end());
	}
	return detail::unique(nets);
}

void NetView::topPorts(const Net *net, std::vector<const void *> &pins) const
{
	if (net == nullptr)
		return;
	for (const Term *term : net->terms) {
		if (isTop(term->pin->inst))
			pins.push_back(term->pin);
		else
			topPorts(term->pin->net, pins);
	}
}

std::vector<const void *> NetView::resolvePort(const std::vector<detail::Hit> &hits, const void *top_pin)
{
	std::vector<const void *> nets;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Net))
		nets.push_back(hit->net);
	std::vector<const void *> pins;
	for (const void *net : detail::unique(nets))
		topPorts(static_cast<const Net *>(net), pins);
	pins = detail::unique(pins);
	// The port by its old name, unless the anchors find other ports: a rename
	// gave the name to another port
	bool agrees = pins.empty() || std::find(pins.begin(), pins.end(), top_pin) != pins.end();
	if (top_pin != nullptr && agrees)
		return {top_pin};
	return pins;
}

void NetView::resolve(const std::vector<Found *> &refs)
{
	log_assert(valid());
	for (size_t i = 0; i < refs.size(); i++) {
		Found &ref = *refs[i];
		ref = {ref.kind, ref.top_pin};
		const std::vector<detail::Hit> &hits = hits_.get(i);
		if (ref.kind == Found::Kind::Pin)
			ref.objects = resolvePin(hits);
		else if (ref.kind == Found::Kind::Cell)
			ref.objects = resolveCell(hits);
		else if (ref.kind == Found::Kind::Port)
			ref.objects = resolvePort(hits, ref.top_pin);
		else
			ref.objects = resolveNet(hits, ref);
	}
}

std::vector<std::string> detail::ownScope(const RTLIL::AttrObject *object)
{
	if (object->has_attribute(ID::hdlname)) {
		std::vector<std::string> parts = object->get_hdlname_attribute();
		if (!parts.empty())
			parts.pop_back();
		return parts;
	}
	return split_tokens(object->get_string_attribute(ID(scopename)), " ");
}

std::string detail::joinScope(const std::vector<std::string> &parts)
{
	std::string path;
	for (const std::string &part : parts)
		path += (path.empty() || part.empty() ? "" : "/") + part;
	return path;
}

std::string detail::scopePath(const Netlist::Instance *scope)
{
	if (scope == nullptr || scope->parent == nullptr)
		return "";
	std::string own = scope->hdlpath.empty() ? scope->name : detail::joinScope(scope->hdlpath);
	return detail::joinScope({detail::scopePath(scope->parent), own});
}

std::string detail::withOwnScope(const std::string &path, const RTLIL::AttrObject *object)
{
	return detail::joinScope({path, detail::joinScope(detail::ownScope(object))});
}

std::string NetView::cellScope(const Instance *inst) const
{
	const RTLIL::Cell *cell = this->cell(inst);
	bool has_own_scope = cell->has_attribute(ID::hdlname) || cell->has_attribute(ID(scopename));
	if (has_own_scope || inst->hdlpath.size() < 2)
		return detail::withOwnScope(detail::scopePath(inst->parent), cell);
	std::vector<std::string> own(inst->hdlpath.begin(), inst->hdlpath.end() - 1);
	return detail::joinScope({detail::scopePath(inst->parent), detail::joinScope(own)});
}

YOSYS_NAMESPACE_END
