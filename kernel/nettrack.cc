// Anchors find the objects of refs again after passes. anchor() puts the
// anchors of each object into the anchor table, the netview_ref attribute of a
// cell or wire holds the index of its anchors there. Roles:
//   Pin      on a cell      ref, scope, port, bit
//   Cell     on a cell      ref, scope
//   Net      on a wire      ref, scope, bit, wire scope
//   Barrier  on a $barrier  ref, scope, port, bit, side
//
// protect() also puts barriers, their anchors are in the barrier table by the
// anchor id in their name. Barriers at:
//   Pin   the leaf pin, or the port inside a hierarchical pin
//   Cell  each pin of a gate, the clock pins of a register
//   Port  a bit of a top bus port
//   Net   the leaf drivers
#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

void NetView::anchor(const std::vector<Found *> &refs)
{
	log_assert(valid());
	clearAnchors(design_);
	markEpochEnd();
	for (uint32_t ref = 0; ref < refs.size(); ref++) {
		Found &found = *refs[ref];
		for (const void *object : found.objects)
			anchorRef(object, ref, found, false);
	}
}

void NetView::protect(const std::vector<Found *> &refs)
{
	log_assert(valid());
	clearAnchors(design_);
	markEpochEnd();
	for (uint32_t ref = 0; ref < refs.size(); ref++) {
		Found &found = *refs[ref];
		for (const void *object : found.objects) {
			anchorRef(object, ref, found, true);
			protectObject(object, ref, found);
		}
	}
	if (!new_images_)
		watch_.refresh(design_);
	new_images_ = false;
}

void NetView::protectObject(const void *object, uint32_t ref, const Found &found)
{
	if (found.kind == Found::Kind::Pin)
		protectPin(static_cast<const Pin *>(object), ref, found);
	else if (found.kind == Found::Kind::Port)
		protectPort(static_cast<const Pin *>(object), ref);
	else if (found.kind == Found::Kind::Cell)
		protectCell(static_cast<const Instance *>(object), ref);
	else
		protectNet(static_cast<const Net *>(object), ref);
}

// abc9 renews a barrier, its old name stays in the new one
void NetView::unprotect(RTLIL::Design *design)
{
	Pass::call(design, stringf("optbarriers -remove t:$barrier n:*%s* %%i", detail::anchor_prefix));
	barrier_marks_.clear();
	RTLIL::IdString cut = detail::attrId(design, "\\netview_cut", false);
	for (RTLIL::Module *module : design->modules()) {
		for (RTLIL::Wire *wire : module->wires()) {
			wire->attributes.erase(cut);
			detail::unmark(design, wire);
		}
		for (RTLIL::Cell *cell : module->cells())
			detail::unmark(design, cell);
	}
}

// Our keep and an empty scopename go
void detail::unmark(RTLIL::Design *design, RTLIL::AttrObject *object)
{
	RTLIL::IdString keep = detail::attrId(design, "\\netview_keep", false);
	if (object->get_bool_attribute(keep)) {
		object->attributes.erase(ID::keep);
		object->attributes.erase(keep);
	}
	if (object->has_attribute(ID(scopename)) && object->get_string_attribute(ID(scopename)).empty())
		object->attributes.erase(ID(scopename));
}

// netview_cut: it never names a net
RTLIL::Wire *detail::addCutWire(RTLIL::Module *module)
{
	RTLIL::Wire *cut = module->addWire(NEW_ID);
	cut->set_bool_attribute(detail::attrId(module->design, "\\netview_cut", true));
	return cut;
}

bool detail::isCutWire(const RTLIL::Wire *wire)
{
	return wire->get_bool_attribute(detail::attrId(wire->module->design, "\\netview_cut", false));
}

// The name holds the anchor id: abc9 renews a barrier without attributes.
// Public, so autoname leaves it
RTLIL::Cell *NetView::addBarrier(RTLIL::Module *module, const RTLIL::SigBit &a, const RTLIL::SigBit &y)
{
	RTLIL::IdString name = module->twines().add(stringf("\\%s$%d", detail::anchor_prefix, ++barrier_count_));
	RTLIL::Cell *barrier = module->addCell(name, ID($barrier));
	barrier->set_bool_attribute(ID::keep);
	detail::markScope(barrier);
	barrier->attributes[detail::attrId(design_, "\\netview_anchor", true)] = RTLIL::Const(barrier_count_);
	barrier->setParam(ID::WIDTH, 1);
	barrier->setPort(ID::A, a);
	barrier->setPort(ID::Y, y);
	return barrier;
}

bool NetView::hasMark(const RTLIL::Cell *barrier, int mark) const
{
	return (barrier_marks_.at(detail::anchorNumber(barrier), 0) & mark) != 0;
}

// A constant stays, the view would see an open input
RTLIL::Cell *NetView::cutPin(const Pin *pin)
{
	RTLIL::Cell *cell = this->cell(pin->inst);
	RTLIL::IdString port = detail::escapedPortId(design_, cell, nullptr, shape(pin).name);
	if (cell == nullptr || !cell->hasPort(port) || pin->bit >= GetSize(cell->getPort(port)))
		return nullptr;
	RTLIL::SigSpec sig = cell->getPort(port);
	RTLIL::SigBit bit = sig[pin->bit];
	if (bit.wire == nullptr)
		return nullptr;
	// A port cut holds all uses of the bit, the pin takes its own barrier
	RTLIL::Cell *existing = cuts_.at(bit, nullptr);
	bool port_cut = existing != nullptr && hasMark(existing, detail::MarkPortCut);
	if (detail::isCutWire(bit.wire) && !port_cut)
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(cell->module);
	RTLIL::Cell *barrier;
	if (isDriver(pin)) {
		barrier = addBarrier(cell->module, cut, bit);
		barrier_marks_[barrier_count_] |= detail::MarkCutA;
	} else {
		barrier = addBarrier(cell->module, bit, cut);
	}
	sig[pin->bit] = cut;
	cell->setPort(port, sig);
	cuts_[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

void NetView::anchorBarrier(const Pin *pin, uint32_t ref)
{
	RTLIL::Cell *barrier = cutPin(pin);
	if (barrier == nullptr)
		return;
	detail::Anchor::Side side = isDriver(pin) ? detail::Anchor::Side::A : detail::Anchor::Side::Y;
	detail::Anchor anchor = {detail::Anchor::Role::Barrier, ref, "", shape(pin).name, pin->bit, "", false, side};
	addBarrierAnchor(barrier, scopePath(pin->inst->parent), anchor);
}

void NetView::addBarrierAnchor(RTLIL::Cell *barrier, const std::string &path, detail::Anchor anchor)
{
	anchor.scope = detail::barrierScope(path, barrier);
	anchor.in_shared_module = scopes(barrier->module).size() > 1;
	barrier_table_[detail::anchorNumber(barrier)].push_back(anchor);
}

// The attribute (rename -hide renames the barrier), else the name (abc9 renews
// it without attributes). -1 for none
int detail::anchorNumber(const RTLIL::Cell *barrier)
{
	RTLIL::IdString id = detail::attrId(barrier->module->design, "\\netview_anchor", false);
	if (barrier->has_attribute(id))
		return barrier->attributes.at(id).as_int();
	std::string marker = std::string(anchor_prefix) + "$";
	std::string text = barrier->name.str();
	size_t at = text.find(marker);
	if (at == std::string::npos)
		return -1;
	return atoi(text.c_str() + at + marker.size());
}

// The scopename, else the prefix that flatten put before the name (. or /).
// abc9 renews it as <prefix><anchor prefix>$<id>.bit[0].b
std::string detail::barrierScope(const std::string &path, const RTLIL::Cell *barrier)
{
	if (barrier->has_attribute(ID::hdlname) || barrier->has_attribute(ID(scopename)))
		return detail::withOwnScope(path, barrier);
	std::string name = barrier->name.str();
	std::string own = name.substr(1, name.find(std::string(anchor_prefix) + "$") - 1);
	if (!own.empty())
		own.pop_back();
	std::replace(own.begin(), own.end(), '.', '/');
	return detail::joinScope({path, own});
}

// A driver also cuts its first input, so opt_merge merges no cell into it
void NetView::protectLeafPin(const Pin *pin, uint32_t ref)
{
	anchorBarrier(pin, ref);
	if (!isDriver(pin))
		return;
	for (const Pin *input : pin->inst->pins) {
		if (!isDriver(input)) {
			cutPin(input);
			return;
		}
	}
}

void NetView::isolateCell(const Instance *inst)
{
	detail::markKeep(design_, cell(inst));
	for (const Pin *pin : inst->pins)
		cutPin(pin);
}

bool NetView::onSide(const Pin *pin, bool drivers) const
{
	if (pin->inst->isLeaf())
		return isDriver(pin) == drivers;
	return dir(pin) == (drivers ? Dir::Output : Dir::Input);
}

// netview_keep marks our keep, unprotect removes only that one
void detail::markKeep(RTLIL::Design *design, RTLIL::AttrObject *object)
{
	if (object->get_bool_attribute(ID::keep))
		return;
	object->set_bool_attribute(ID::keep);
	object->set_bool_attribute(detail::attrId(design, "\\netview_keep", true));
}

// Only one-bit wires, keep on a wide wire would hold its other bits too
void NetView::keepWires(const Net *net)
{
	for (const RTLIL::SigBit &bit : wireBits(net)) {
		if (bit.wire->width == 1 && !detail::isCutWire(bit.wire))
			detail::markKeep(design_, bit.wire);
	}
}

// splitnets -ports renames only bus bits, the barrier finds them again
void NetView::protectPort(const Pin *pin, uint32_t ref)
{
	const PortShape &port = shape(pin);
	if (port.scalar())
		return;
	RTLIL::Cell *barrier = cutPort(pin);
	if (barrier == nullptr)
		return;
	detail::Anchor::Side side = port.dir == Dir::Input ? detail::Anchor::Side::A : detail::Anchor::Side::Y;
	addBarrierAnchor(barrier, "", {detail::Anchor::Role::Barrier, ref, "", port.name, pin->bit, "", false, side});
}

RTLIL::Cell *NetView::cutPort(const Pin *pin)
{
	RTLIL::Module *module = this->module(pin->inst);
	if (module == nullptr)
		return nullptr;
	RTLIL::Wire *wire = module->wire(detail::escapedPortId(design_, nullptr, module, shape(pin).name));
	if (wire == nullptr || pin->bit >= wire->width || wire->port_input == wire->port_output)
		return nullptr;
	RTLIL::SigBit bit(wire, pin->bit);
	if (RTLIL::Cell *existing = portBarrier(module, bit))
		return existing;
	RTLIL::Wire *cut = detail::addCutWire(module);
	detail::replaceBit(module, bit, cut);
	RTLIL::Cell *barrier;
	if (wire->port_input) {
		barrier = addBarrier(module, bit, cut);
		barrier_marks_[barrier_count_] = detail::MarkPortCut;
	} else {
		barrier = addBarrier(module, cut, bit);
		barrier_marks_[barrier_count_] = detail::MarkPortCut | detail::MarkCutA;
	}
	cuts_[RTLIL::SigBit(cut)] = barrier;
	return barrier;
}

RTLIL::Cell *NetView::portBarrier(RTLIL::Module *module, const RTLIL::SigBit &bit) const
{
	RTLIL::IdString port = bit.wire->port_input ? ID::A : ID::Y;
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type == ID($barrier) && hasMark(cell, detail::MarkPortCut) && cell->getPort(port) == RTLIL::SigSpec(bit))
			return cell;
	}
	return nullptr;
}

void detail::replaceBit(RTLIL::Module *module, const RTLIL::SigBit &bit, const RTLIL::SigBit &other)
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

void NetView::protectPin(const Pin *pin, uint32_t ref, const Found &found)
{
	if (isTop(pin->inst))
		return;
	if (pin->inst->isLeaf())
		return protectLeafPin(pin, ref);
	protectHierPin(pin, ref, found.image);
}

// At the port inside the cell. Its cut side keeps the paths after flatten, an
// image also keeps the pin
void NetView::protectHierPin(const Pin *pin, uint32_t ref, bool image)
{
	RTLIL::Cell *barrier = cutPort(pin);
	if (barrier == nullptr)
		return;
	if (image && !hasMark(barrier, detail::MarkImage)) {
		barrier_marks_[detail::anchorNumber(barrier)] |= detail::MarkImage;
		new_images_ = true;
	}
	detail::Anchor::Side side = dir(pin) == Dir::Input ? detail::Anchor::Side::Y : detail::Anchor::Side::A;
	detail::Anchor anchor = {detail::Anchor::Role::Barrier, ref, "", shape(pin).name, pin->bit, "", false, side};
	addBarrierAnchor(barrier, scopePath(pin->inst), anchor);
}

bool NetView::isRegister(const Instance *inst) const
{
	if (model_ != nullptr && model_->isRegister(*inst))
		return true;
	return StaticCellTypes::categories.is_ff(cell(inst)->type);
}

bool NetView::isClockPin(const Pin *pin) const
{
	if (model_ != nullptr && model_->isClockPin(*pin))
		return true;
	const std::string &name = shape(pin).name;
	return StaticCellTypes::categories.is_ff(cell(pin->inst)->type) && (name == "C" || name == "CLK");
}

// No pass maps a register with other cells, it takes cuts at its clock pins only
void NetView::protectCell(const Instance *inst, uint32_t ref)
{
	if (inst->isLeaf() && isRegister(inst)) {
		detail::markKeep(design_, cell(inst));
		for (const Pin *pin : inst->pins) {
			if (isClockPin(pin))
				anchorBarrier(pin, ref);
		}
		return;
	}
	if (inst->isLeaf()) {
		isolateCell(inst);
		for (const Pin *pin : inst->pins)
			anchorBarrier(pin, ref);
		return;
	}
	cell(inst)->set_bool_attribute(ID::keep_hierarchy);
}

// The driver barriers find the net when splitnets drops its wire attributes
void NetView::protectNet(const Net *net, uint32_t ref)
{
	keepWires(net);
	pool<const Net *> seen;
	std::vector<const Pin *> drivers;
	leafDrivers(net, seen, drivers);
	for (const Pin *pin : drivers)
		protectLeafPin(pin, ref);
}

void NetView::leafDrivers(const Net *net, pool<const Net *> &seen, std::vector<const Pin *> &drivers) const
{
	if (net == nullptr || !seen.insert(net).second)
		return;
	for (const Pin *pin : net->pins) {
		if (pin->inst->isLeaf() && isDriver(pin))
			drivers.push_back(pin);
		else if (!pin->inst->isLeaf() && pin->term != nullptr)
			leafDrivers(pin->term->net, seen, drivers);
	}
	for (const Term *term : net->terms)
		leafDrivers(term->pin->net, seen, drivers);
}

RTLIL::IdString detail::attrId(RTLIL::Design *design, const std::string &name, bool add)
{
	if (add)
		return design->twines().add(name);
	return design->twines().find(name);
}

RTLIL::IdString detail::refId(RTLIL::Design *design, bool add)
{
	return detail::attrId(design, "\\netview_ref", add);
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
	std::string path = scopePath(net->scope);
	for (const RTLIL::SigBit &bit : wireBits(net)) {
		bool shared = markIfShared(bit.wire, bit.wire->module);
		addAnchor(bit.wire, {detail::Anchor::Role::Net, ref, detail::withOwnScope(path, bit.wire), "", bit.offset, path, shared});
	}
}

void NetView::anchorRef(const void *object, uint32_t ref, Found &found, bool barriers)
{
	if (found.kind == Found::Kind::Net)
		return anchorWires(static_cast<const Net *>(object), ref);
	if (found.kind == Found::Kind::Cell) {
		const Instance *inst = static_cast<const Instance *>(object);
		return anchorCell(inst, {detail::Anchor::Role::Cell, ref, cellScope(inst), "", 0, "", false});
	}
	const Pin *pin = static_cast<const Pin *>(object);
	if (isTop(pin->inst)) {
		if (pin->term != nullptr)
			anchorWires(pin->term->net, ref);
		return;
	}
	if (isBarrier(pin->inst))
		return anchorImagePin(pin, ref, found, barriers);
	if (!pin->inst->isLeaf())
		found.hier = dir(pin) == Dir::Output ? Dir::Output : Dir::Input;
	anchorCell(pin->inst, {detail::Anchor::Role::Pin, ref, cellScope(pin->inst), shape(pin).name, pin->bit, "", false});
}

void NetView::anchorImagePin(const Pin *pin, uint32_t ref, Found &found, bool barriers)
{
	found.image_pin = true;
	if (!barriers)
		return anchorDrivers(pin, ref, found);
	detail::Anchor anchor = {detail::Anchor::Role::Pin, ref, "", shape(pin).name, pin->bit, "", false, detail::Anchor::Side::Y};
	addBarrierAnchor(cell(pin->inst), scopePath(pin->inst->parent), anchor);
}

// unprotect removes the image: a ref of its A pin moves to the drivers, a ref
// of its Y pin takes no anchor
void NetView::anchorDrivers(const Pin *pin, uint32_t ref, Found &found)
{
	if (dir(pin) != Dir::Input)
		return;
	std::vector<const void *> drivers;
	cutPins(cell(pin->inst), pin->inst->parent, detail::Anchor::Side::A, drivers);
	for (const void *driver : drivers)
		anchorRef(driver, ref, found, false);
	found.unprotected = !drivers.empty();
}

void NetView::clearAnchors(RTLIL::Design *design)
{
	anchor_table_.clear();
	barrier_table_.clear();
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
		bool in_own_scope = anchor.scope == detail::withOwnScope(scopePath(net->scope), bit.wire);
		hits_[anchor.ref].push_back({anchor, nullptr, net, in_own_scope});
	}
}

void NetView::indexBarrier(RTLIL::Cell *cell, const Instance *scope)
{
	if (cell->type != ID($barrier))
		return;
	int id = detail::anchorNumber(cell);
	if (id < 0)
		return;
	cuts_[cell->getPort(hasMark(cell, detail::MarkCutA) ? ID::A : ID::Y)[0]] = cell;
	if (!barrier_table_.count(id))
		return;
	std::string path = detail::barrierScope(scopePath(scope), cell);
	for (const detail::Anchor &anchor : barrier_table_.at(id)) {
		bool pin_role = anchor.role == detail::Anchor::Role::Pin;
		const Instance *inst = pin_role ? instance(cell, scope) : nullptr;
		if (!pin_role || inst != nullptr)
			hits_[anchor.ref].push_back({anchor, inst, nullptr, anchor.scope == path, cell, scope});
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

// The leaf pins on the cut side, across a chain of barriers
void NetView::cutPins(const RTLIL::Cell *barrier, const Instance *scope, detail::Anchor::Side side, std::vector<const void *> &found)
{
	bool drivers = side == detail::Anchor::Side::A;
	RTLIL::SigBit cut = barrier->getPort(drivers ? ID::A : ID::Y)[0];
	if (const Pin *port = topPortPin(barrier, cut)) {
		found.push_back(port);
		return;
	}
	RTLIL::Module *module = barrier->module;
	const ModWalker &walker = walkers_.try_emplace(module, module->design, module).first->second;
	pool<ModWalker::PortBit> users;
	walker.get_drivers(users, walker.sigmap(cut));
	walker.get_consumers(users, walker.sigmap(cut));
	for (const ModWalker::PortBit &at : users) {
		if (at.cell == barrier)
			continue;
		if (at.cell->type != ID($barrier))
			addCutUser(at, scope, drivers, found);
		else if ((at.port == ID::A) != drivers)
			cutPins(at.cell, scope, side, found);
	}
}

void NetView::addCutUser(const ModWalker::PortBit &at, const Instance *scope, bool drivers, std::vector<const void *> &found) const
{
	const Instance *inst = instance(at.cell, scope);
	if (inst == nullptr)
		return;
	const Pin *pin = this->pin(inst, detail::unescapedName({at.cell->module, at.port}), at.offset);
	if (pin != nullptr && pin->inst->isLeaf() && isDriver(pin) == drivers)
		found.push_back(pin);
	else if (pin != nullptr && !pin->inst->isLeaf() && pin->term != nullptr)
		innerPins(pin->term->net, drivers, found);
}

const NetView::Pin *NetView::topPortPin(const RTLIL::Cell *barrier, const RTLIL::SigBit &bit) const
{
	if (bit.wire == nullptr || bit.wire->port_id == 0 || barrier->module != module(top_))
		return nullptr;
	return pin(top_, detail::unescapedName(bit.wire->name), bit.offset);
}

// submod and extract can put a new hierarchical cell on the cut side
void NetView::innerPins(const Net *net, bool drivers, std::vector<const void *> &found) const
{
	for (const Pin *pin : net->pins) {
		if (!onSide(pin, drivers))
			continue;
		if (pin->inst->isLeaf())
			found.push_back(pin);
		else if (pin->term != nullptr)
			innerPins(pin->term->net, drivers, found);
	}
}

std::vector<const void *> NetView::barrierCutPins(const std::vector<detail::Hit> &hits)
{
	std::vector<const void *> pins;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Barrier))
		cutPins(hit->barrier, hit->barrier_scope, hit->anchor.side, pins);
	return pins;
}

void NetView::barrierPins(const std::vector<detail::Hit> &hits, Found &ref)
{
	if (ref.hier == Dir::Unknown)
		return;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Barrier)) {
		cutPins(hit->barrier, hit->barrier_scope, detail::Anchor::Side::Y, ref.beyond);
		const Instance *inst = instance(hit->barrier, hit->barrier_scope);
		if (inst == nullptr || inst->isLeaf())
			continue;
		ref.image_a.push_back(pin(inst, "A", 0));
		ref.image_y.push_back(pin(inst, "Y", 0));
	}
}

std::vector<const void *> NetView::resolvePin(const std::vector<detail::Hit> &hits, Found &ref)
{
	std::vector<const void *> pins;
	std::vector<const Instance *> renamed;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Pin)) {
		const Pin *pin = this->pin(hit->inst, hit->anchor.port, hit->anchor.bit);
		if (pin != nullptr)
			pins.push_back(pin);
		else if (!hit->inst->isLeaf())
			renamed.push_back(hit->inst);
	}
	if (!ref.image_a.empty())
		pins.clear();
	if (!pins.empty())
		return pins;
	pins = barrierCutPins(hits);
	if (!renamed.empty())
		return detail::pinsOf(renamed, pins);
	return detail::unique(pins);
}

// Hierarchical pins whose port splitnets -ports renamed, up from the leaf pins
std::vector<const void *> detail::pinsOf(const std::vector<const Netlist::Instance *> &insts, const std::vector<const void *> &leaves)
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
	return detail::unique(found);
}

// The cell, else the cells between its barriers (abc put them in its place)
std::vector<const void *> NetView::resolveCell(const std::vector<detail::Hit> &hits)
{
	std::vector<const void *> cells;
	for (const detail::Hit *hit : detail::pick(hits, detail::Anchor::Role::Cell))
		cells.push_back(hit->inst);
	if (!cells.empty())
		return cells;
	for (const void *pin : barrierCutPins(hits))
		cells.push_back(static_cast<const Pin *>(pin)->inst);
	return detail::unique(cells);
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
		if (pin->inst->isLeaf() && (scope.empty() || path == scope || path.starts_with(scope + "/")))
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
		if (scopePath(hit->net->scope) == hit->anchor.wire_scope || !outer.insert(hit->net).second)
			continue;
		std::vector<const void *> inside = pinsUnder(hit->net, hit->anchor.wire_scope);
		if (inside.size() < hit->net->pins.size())
			ref.through_pins.insert(ref.through_pins.end(), inside.begin(), inside.end());
	}
	if (nets.empty()) {
		for (const void *pin : barrierCutPins(hits))
			nets.push_back(static_cast<const Pin *>(pin)->net);
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
	if (nets.empty()) {
		for (const void *object : barrierCutPins(hits)) {
			const Pin *pin = static_cast<const Pin *>(object);
			if (isTop(pin->inst))
				pins.push_back(pin);
			else
				nets.push_back(pin->net);
		}
	}
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
		ref = {ref.kind, ref.hier, ref.image, ref.image_pin, ref.unprotected, ref.top_pin};
		const std::vector<detail::Hit> &hits = hits_.get(i);
		barrierPins(hits, ref);
		if (ref.kind == Found::Kind::Pin)
			ref.objects = resolvePin(hits, ref);
		else if (ref.kind == Found::Kind::Cell)
			ref.objects = resolveCell(hits);
		else if (ref.kind == Found::Kind::Port)
			ref.objects = resolvePort(hits, ref.top_pin);
		else
			ref.objects = resolveNet(hits, ref);
		bool hier = ref.hier != Dir::Unknown && !ref.objects.empty();
		ref.inside = hier && static_cast<const Pin *>(ref.objects[0])->inst->isLeaf();
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

std::string detail::ownName(const Netlist::Instance *scope)
{
	if (scope->hdlpath.empty())
		return scope->name;
	return detail::joinScope(scope->hdlpath);
}

// By the names at the epoch end: rename -hide renames an occurrence. A copy that
// flatten made is a new cell, its hdlname holds the source path
std::string NetView::scopePath(const Instance *scope) const
{
	if (scope == nullptr || scope->parent == nullptr)
		return "";
	std::string own = epoch_names_.at(cell(scope)->hashidx_, detail::ownName(scope));
	return detail::joinScope({scopePath(scope->parent), own});
}

// The own names of the cells at the epoch end
void NetView::markEpochEnd()
{
	epoch_names_.clear();
	for (const Instance &inst : records_.instances) {
		if (inst.parent != nullptr)
			epoch_names_[cell(&inst)->hashidx_] = detail::ownName(&inst);
	}
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
		return detail::withOwnScope(scopePath(inst->parent), cell);
	std::vector<std::string> own(inst->hdlpath.begin(), inst->hdlpath.end() - 1);
	return detail::joinScope({scopePath(inst->parent), detail::joinScope(own)});
}

YOSYS_NAMESPACE_END
