#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

detail::ViewBuilder::ViewBuilder(NetView &view) : view_(view) {}

void detail::ViewBuilder::build(RTLIL::Module *top)
{
	view_.top_ = newInstance(nullptr, top, nullptr);
	makePins(view_.top_);
	buildScope(top, view_.top_);
}

bool detail::ViewBuilder::hostPortShapes(const Netlist::Instance *inst, std::vector<Netlist::PortShape> &out) const
{
	RTLIL::Module *mod;
	if (view_.isTop(inst))
		mod = view_.module(inst);
	else
		mod = view_.design_->module(view_.cell(inst)->type);
	if (mod != nullptr) {
		detail::moduleShapes(mod, out);
		return true;
	}
	return detail::cellTypePortShapes(view_.cell(inst), out);
}

const NetView::PortShapes *detail::ViewBuilder::portShapesFor(Netlist::Instance *inst, RTLIL::Module *sub)
{
	PortShapeCache &cache = view_.shapes_;
	// Library leaf shapes are shared per type, internal cells differ in width
	bool shared = inst->kind == Netlist::Instance::Kind::LibraryLeaf;
	if (shared) {
		if (const NetView::PortShapes *cached = cache.shapes_by_leaf_type.at(inst->type, nullptr))
			return cached;
	}

	NetView::PortShapes &shapes = cache.shape_store.emplace_back();
	Netlist::LeafCellModel *model = view_.leaf_model_;
	if (sub != nullptr)
		detail::moduleShapes(sub, shapes);
	else if (model == nullptr && !hostPortShapes(inst, shapes))
		log_cmd_error("NetView: no port model for cell type %s (cell %s).\n", inst->type, inst->name);
	else if (model != nullptr && !model->ports(*inst, shapes)) {
		hostPortShapes(inst, shapes);
		cache.unmodeled_leaf_types.insert(inst->type);
	}

	if (shared)
		cache.shapes_by_leaf_type[inst->type] = &shapes;
	return &shapes;
}

Netlist::Instance *detail::ViewBuilder::newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent)
{
	Netlist::Instance *inst = view_.records_.newInstance();

	// The top has no cell, it is named after its module
	RTLIL::IdString name, type;
	if (cell != nullptr) {
		name = cell->name;
		type = cell->type;
	} else {
		name = module->name;
		type = module->name;
	}
	inst->name = detail::unescapedName({view_.design_, name});
	inst->type = detail::unescapedName({view_.design_, type});

	// A uniquified module keeps its original name in hdlname
	inst->master = inst->type;
	if (module != nullptr && module->has_attribute(ID::hdlname))
		inst->master = module->get_string_attribute(ID::hdlname);

	inst->parent = parent;
	inst->netlist = &view_;

	// Leaves open no scope (module is nullptr)
	inst->kind = Netlist::Instance::Kind::Hierarchy;
	if (module == nullptr && detail::isInternalType(type))
		inst->kind = Netlist::Instance::Kind::InternalLeaf;
	else if (module == nullptr)
		inst->kind = Netlist::Instance::Kind::LibraryLeaf;
	inst->ports = nullptr;

	RtlilIndex &index = view_.index_;
	index.instance_rtlil[inst->id] = {cell, module};
	if (cell != nullptr) {
		inst->hdlpath = detail::sourcePath(cell, cell->name.str());
		index.instances_by_cell.add(cell->hashidx_, inst);
		view_.hit_index_.noteInstance(view_, view_.epoch_, inst);
	}
	if (module != nullptr)
		index.scopes_by_module.add(module, inst);
	if (parent != nullptr)
		parent->children.push_back(inst);
	return inst;
}

void detail::ViewBuilder::buildScope(RTLIL::Module *module, Netlist::Instance *scope)
{
	for (RTLIL::Cell *cell : detail::statementOrder(module)) {
		if (cell->type == ID($barrier) && view_.epoch_.barriers.hasMark(cell, BarrierMark::Image)) {
			addImageInstance(cell, scope);
			continue;
		}
		if (detail::isTransparentType(cell->type))
			continue;
		Netlist::Instance *inst = newInstance(cell, detail::childModule(view_.design_, cell), scope);
		makePins(inst);
		if (!inst->isLeaf())
			buildScope(view_.module(inst), inst);
	}
	for (RTLIL::Cell *cell : module->cells())
		view_.hit_index_.noteBarrier(view_, view_.epoch_, cell, scope);
	registerWires(module, scope);
}

void detail::ViewBuilder::makePins(Netlist::Instance *inst)
{
	RTLIL::Cell *c = view_.cell(inst);
	RTLIL::Module *sub = view_.module(inst);
	inst->ports = portShapesFor(inst, sub);
	for (uint32_t p = 0; p < inst->ports->size(); p++) {
		const Netlist::PortShape &shape = (*inst->ports)[p];
		RTLIL::IdString port_id = detail::escapedPortId(view_.design_, c, sub, shape.name);
		RTLIL::SigSpec sig;
		if (c != nullptr && c->hasPort(port_id))
			sig = c->getPort(port_id);
		RTLIL::Wire *inner_wire = nullptr;
		if (sub != nullptr)
			inner_wire = sub->wire(port_id);
		for (int b = 0; b < shape.width; b++) {
			Netlist::Net *net = nullptr;
			if (b < sig.size())
				net = findOrMakeNet(inst->parent, sig[b]);
			Netlist::Pin *pin = makePin(inst, p, b, net);
			if (inner_wire == nullptr || b >= inner_wire->width)
				continue;
			Netlist::Net *inner_net = findOrMakeNet(inst, RTLIL::SigBit(inner_wire, b));
			if (inner_net != nullptr)
				makeTerm(pin, inner_net);
		}
	}
}

// An image: an instance with no module, a net per bit joins A and Y
void detail::ViewBuilder::addImageInstance(RTLIL::Cell *cell, Netlist::Instance *scope)
{
	Netlist::Instance *inst = newInstance(cell, nullptr, scope);
	inst->kind = Netlist::Instance::Kind::Image;
	NetView::PortShapes &shapes = view_.shapes_.shape_store.emplace_back();
	detail::cellTypePortShapes(cell, shapes);
	inst->ports = &shapes;
	int width = GetSize(cell->getPort(ID::Y));
	std::vector<Netlist::Net *> inner;
	for (int b = 0; b < width; b++)
		inner.push_back(newImageNet(inst, b, width == 1));
	for (uint32_t p = 0; p < shapes.size(); p++) {
		RTLIL::SigSpec sig = cell->getPort(detail::escapedPortId(view_.design_, cell, nullptr, shapes[p].name));
		for (int b = 0; b < width && b < sig.size(); b++) {
			Netlist::Pin *pin = makePin(inst, p, b, findOrMakeNet(scope, sig[b]));
			makeTerm(pin, inner[b]);
		}
	}
}

// A net of an image, named Y
Netlist::Net *detail::ViewBuilder::newImageNet(Netlist::Instance *scope, int bit, bool scalar)
{
	Netlist::Net *net = view_.records_.newNet();
	net->scope = scope;
	net->constant = Netlist::Net::Const::None;
	view_.index_.net_rtlil[net->id].name = {"Y", bit, scalar};
	view_.scope_contents_[scope].nets.push_back(net);
	return net;
}

Netlist::Pin *detail::ViewBuilder::makePin(Netlist::Instance *inst, uint32_t port, int bit, Netlist::Net *net)
{
	Netlist::Pin *pin = view_.records_.newPin();
	pin->inst = inst;
	pin->net = net;
	pin->term = nullptr;
	pin->port = port;
	pin->bit = bit;
	inst->pins.push_back(pin);
	if (net != nullptr)
		net->pins.push_back(pin);
	return pin;
}

void detail::ViewBuilder::makeTerm(Netlist::Pin *pin, Netlist::Net *inner_net)
{
	Netlist::Term *term = view_.records_.newTerm();
	term->pin = pin;
	term->net = inner_net;
	pin->term = term;
	inner_net->terms.push_back(term);
}

Netlist::Net *detail::ViewBuilder::newNet(Netlist::Instance *scope, const RTLIL::SigBit &bit)
{
	Netlist::Net *net = view_.records_.newNet();
	net->scope = scope;
	net->constant = Netlist::Net::Const::None;
	if (bit.wire == nullptr && bit.data == RTLIL::State::S1)
		net->constant = Netlist::Net::Const::One;
	else if (bit.wire == nullptr)
		net->constant = Netlist::Net::Const::Zero;
	view_.index_.net_rtlil[net->id].bit = bit;
	if (bit.wire != nullptr)
		setNameBit(net, bit);
	view_.scope_contents_[scope].nets.push_back(net);
	return net;
}

void detail::ViewBuilder::registerWires(RTLIL::Module *module, Netlist::Instance *scope)
{
	SigMap &sigmap = sigmapFor(module);
	for (RTLIL::Wire *wire : module->wires()) {
		bool pub = wire->name.isPublic();
		for (int b = 0; b < wire->width; b++) {
			RTLIL::SigBit bit(wire, b);
			RTLIL::SigBit canon = sigmap(bit);
			Netlist::Net *net = nullptr;
			if (canon.wire != nullptr)
				net = view_.index_.nets_by_scope_bit.get(scope, canon);
			else if (pub)
				net = findOrMakeNet(scope, canon);
			if (net == nullptr)
				continue;
			if (canon.wire != nullptr) {
				view_.index_.net_rtlil[net->id].wire_bits.push_back(bit);
				view_.hit_index_.noteWireBit(view_, view_.epoch_, net, bit);
			}
			if (!pub)
				continue;

			// Public wires collapsed into another wire's net (assign aliases)
			// stay reachable under their own names
			view_.scope_contents_[scope].aliases.push_back({detail::netName(bit, wireOrigin(bit.wire)), net});

			// A net is named after its best wire bit
			if (net->constant == Netlist::Net::Const::None && detail::netNameRank(bit) < detail::netNameRank(nameBit(net)))
				setNameBit(net, bit);
		}
	}
}

SigMap &detail::ViewBuilder::sigmapFor(RTLIL::Module *module)
{
	auto [it, added] = sigmaps_.try_emplace(module, module);
	if (added) {
		detail::addConnectAliases(module, it->second);
		addBarrierAliases(module, it->second);
	}
	return it->second;
}

void detail::ViewBuilder::addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const
{
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type != ID($barrier) || view_.epoch_.barriers.hasMark(cell, BarrierMark::Image))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A), y = cell->getPort(ID::Y);
		for (int b = 0; b < GetSize(a) && b < GetSize(y); b++) {
			// Barriers join no constant, so the cell order does not change this
			if (sigmap(a[b]).wire == nullptr || sigmap(y[b]).wire == nullptr)
				continue;
			// The second bit stays the root, so a cut wire never names a net
			if (detail::isCutWire(a[b].wire))
				sigmap.add(a[b], y[b]);
			else
				sigmap.add(y[b], a[b]);
		}
	}
}

RTLIL::SigBit detail::ViewBuilder::nameBit(const Netlist::Net *net) const
{
	const NetRtlil &rtlil = view_.index_.net_rtlil.get(net->id);
	if (rtlil.name_bit.wire != nullptr)
		return rtlil.name_bit;
	return rtlil.bit;
}

// Reads must work on a stale view
void detail::ViewBuilder::setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit)
{
	NetRtlil &rtlil = view_.index_.net_rtlil[net->id];
	rtlil.name_bit = bit;
	rtlil.name = detail::netName(bit, wireOrigin(bit.wire));
}

// splitnets copies the hdlname of a vector to each of its bits
detail::WireOrigin detail::ViewBuilder::wireOrigin(const RTLIL::Wire *wire)
{
	if (!wire->has_attribute(ID::hdlname))
		return WireOrigin::Declared;
	auto [it, added] = hdlname_counts_.try_emplace(wire->module);
	if (added) {
		for (const RTLIL::Wire *other : wire->module->wires()) {
			if (other->has_attribute(ID::hdlname))
				it->second[other->get_string_attribute(ID::hdlname)]++;
		}
	}
	if (it->second.at(wire->get_string_attribute(ID::hdlname)) > 1)
		return WireOrigin::SplitFromVector;
	return WireOrigin::Declared;
}

Netlist::Net *detail::ViewBuilder::findOrMakeNet(Netlist::Instance *scope, const RTLIL::SigBit &bit)
{
	NetsByScopeBit &nets = view_.index_.nets_by_scope_bit;
	if (bit.wire != nullptr) {
		if (Netlist::Net *net = nets.get(scope, bit))
			return net;
	}
	RTLIL::SigBit canon = bit;
	if (bit.wire != nullptr)
		canon = sigmapFor(bit.wire->module)(bit);
	Netlist::Net *net;
	if (canon.wire == nullptr) {
		if (canon.data != RTLIL::State::S0 && canon.data != RTLIL::State::S1)
			return nullptr; // x/z: unconnected
		net = findOrMakeTieNet(scope, canon);
	} else {
		net = nets.get(scope, canon);
		if (net == nullptr) {
			net = newNet(scope, canon);
			nets.set(scope, canon, net);
		}
	}
	if (bit.wire != nullptr && bit != canon)
		nets.set(scope, bit, net);
	return net;
}

Netlist::Net *detail::ViewBuilder::findOrMakeTieNet(Netlist::Instance *scope, const RTLIL::SigBit &canon)
{
	Netlist::Net::Const value = Netlist::Net::Const::Zero;
	if (canon.data == RTLIL::State::S1)
		value = Netlist::Net::Const::One;
	if (Netlist::Net *net = view_.scope_contents_[scope].tieNet(value))
		return net;
	Netlist::Net *net = newNet(scope, canon);
	view_.scope_contents_[scope].setTieNet(value, net);
	return net;
}

YOSYS_NAMESPACE_END
