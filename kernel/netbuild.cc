#include "kernel/netview_internal.h"

YOSYS_NAMESPACE_BEGIN

detail::ViewBuilder::ViewBuilder(const NetView &view, ViewData &data) : view_(view), data_(data) {}

void detail::ViewBuilder::build(RTLIL::Module *top)
{
	data_.top = newInstance(nullptr, top, nullptr);
	makePins(data_.top);
	buildScope(top, data_.top);
}

bool detail::ViewBuilder::yosysPorts(const Netlist::Instance *inst, std::vector<Netlist::Port> &out) const
{
	RTLIL::Module *mod;
	if (inst->isTop())
		mod = view_.module(inst);
	else
		mod = data_.design->module(view_.cell(inst)->type);
	if (mod != nullptr) {
		detail::modulePorts(mod, out);
		return true;
	}
	return detail::cellTypePorts(view_.cell(inst), out);
}

const std::vector<Netlist::Port> *detail::ViewBuilder::portsFor(Netlist::Instance *inst, RTLIL::Module *sub)
{
	PortStore &store = data_.ports;
	bool shared = inst->kind == Netlist::Instance::Kind::LibraryCell;
	if (shared) {
		if (const std::vector<Netlist::Port> *cached = store.lists_by_library_type.at(inst->type, nullptr))
			return cached;
	}

	std::vector<Netlist::Port> &ports = store.lists.emplace_back();
	bool known = true;
	if (sub != nullptr)
		detail::modulePorts(sub, ports);
	else
		known = leafPorts(inst, ports);

	// Each cell of an unknown type checks its own connections
	if (shared && known)
		store.lists_by_library_type[inst->type] = &ports;
	return &ports;
}

bool detail::ViewBuilder::leafPorts(const Netlist::Instance *inst, std::vector<Netlist::Port> &out)
{
	Netlist::CellLibrary *library = data_.library;
	if (library != nullptr && library->ports(*inst, out))
		return true;
	bool known = yosysPorts(inst, out);
	bool connected = !view_.cell(inst)->connections().empty();
	if (!known && (library == nullptr || connected))
		log_cmd_error("NetView: no port model for cell type %s (cell %s).\n", inst->type, inst->name);
	if (library != nullptr)
		data_.ports.types_not_in_library.insert(inst->type);
	return known;
}

Netlist::Instance *detail::ViewBuilder::newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent)
{
	Netlist::Instance *inst = data_.records.newInstance();

	// The top has no cell, it is named after its module
	RTLIL::IdString name, type;
	if (cell != nullptr) {
		name = cell->name;
		type = cell->type;
	} else {
		name = module->name;
		type = module->name;
	}
	inst->name = detail::unescapedName({data_.design, name});
	inst->type = detail::unescapedName({data_.design, type});

	// A uniquified module keeps its original name in hdlname
	inst->hdl_type = inst->type;
	if (module != nullptr && module->has_attribute(ID::hdlname))
		inst->hdl_type = module->get_string_attribute(ID::hdlname);

	inst->parent = parent;
	inst->view = &view_;

	inst->kind = Netlist::Instance::Kind::Module;
	if (module == nullptr && detail::isInternalType(type))
		inst->kind = Netlist::Instance::Kind::InternalCell;
	else if (module == nullptr)
		inst->kind = Netlist::Instance::Kind::LibraryCell;
	inst->ports = nullptr;

	RtlilIndex &index = data_.index;
	index.instance_rtlil[inst->id] = {cell, module};
	if (cell != nullptr) {
		inst->hdlpath = detail::sourcePath(cell, cell->name.str());
		index.instances_by_cell[cell->hashidx_] = inst;
	}
	if (module != nullptr)
		index.scopes_by_module[module] = inst;
	if (parent != nullptr)
		parent->children.push_back(inst);
	return inst;
}

void detail::ViewBuilder::buildScope(RTLIL::Module *module, Netlist::Instance *scope)
{
	for (RTLIL::Cell *cell : detail::statementOrder(module)) {
		if (detail::isTransparentType(cell->type))
			continue;
		Netlist::Instance *inst = newInstance(cell, detail::childModule(data_.design, cell), scope);
		makePins(inst);
		if (!inst->isLeaf())
			buildScope(view_.module(inst), inst);
	}
	registerWires(module, scope);
}

void detail::ViewBuilder::makePins(Netlist::Instance *inst)
{
	RTLIL::Cell *c = view_.cell(inst);
	RTLIL::Module *sub = view_.module(inst);
	inst->ports = portsFor(inst, sub);
	for (uint32_t p = 0; p < inst->ports->size(); p++) {
		const Netlist::Port &port = (*inst->ports)[p];
		RTLIL::IdString port_id = detail::escapedPortId(data_.design, c, sub, port.name);
		RTLIL::SigSpec sig;
		if (c != nullptr && c->hasPort(port_id))
			sig = c->getPort(port_id);
		RTLIL::Wire *inner_wire = nullptr;
		if (sub != nullptr)
			inner_wire = sub->wire(port_id);
		for (int b = 0; b < port.width; b++) {
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

Netlist::Pin *detail::ViewBuilder::makePin(Netlist::Instance *inst, uint32_t port_index, int bit, Netlist::Net *net)
{
	Netlist::Pin *pin = data_.records.newPin();
	pin->inst = inst;
	pin->net = net;
	pin->term = nullptr;
	pin->port_index = port_index;
	pin->bit = bit;
	inst->pins.push_back(pin);
	if (net != nullptr)
		net->pins.push_back(pin);
	return pin;
}

void detail::ViewBuilder::makeTerm(Netlist::Pin *pin, Netlist::Net *inner_net)
{
	Netlist::Term *term = data_.records.newTerm();
	term->pin = pin;
	term->net = inner_net;
	pin->term = term;
	inner_net->terms.push_back(term);
}

Netlist::Net *detail::ViewBuilder::newNet(Netlist::Instance *scope, const RTLIL::SigBit &bit)
{
	Netlist::Net *net = data_.records.newNet();
	net->scope = scope;
	net->constant = Netlist::Net::Const::None;
	if (bit.wire == nullptr && bit.data == RTLIL::State::S1)
		net->constant = Netlist::Net::Const::One;
	else if (bit.wire == nullptr)
		net->constant = Netlist::Net::Const::Zero;
	data_.index.net_rtlil[net->id].bit = bit;
	if (bit.wire != nullptr)
		setNameBit(net, bit);
	data_.scope_contents[scope].nets.push_back(net);
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
				net = data_.index.nets_by_bit.at(detail::bitKey(canon), nullptr);
			else if (pub)
				net = findOrMakeNet(scope, canon);
			if (net == nullptr)
				continue;
			if (canon.wire != nullptr)
				data_.index.net_rtlil[net->id].wire_bits.push_back(bit);
			if (!pub)
				continue;

			// Public wires collapsed into another wire's net (assign aliases) stay reachable under their own names
			data_.scope_contents[scope].aliases.push_back({detail::netName(bit, wireOrigin(bit.wire)), net});
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
		if (cell->type != ID($barrier))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A), y = cell->getPort(ID::Y);
		for (int b = 0; b < GetSize(a) && b < GetSize(y); b++) {
			// Barriers join no constant, so the cell order does not change this
			if (sigmap(a[b]).wire == nullptr || sigmap(y[b]).wire == nullptr)
				continue;
			sigmap.add(y[b], a[b]);
		}
	}
}

RTLIL::SigBit detail::ViewBuilder::nameBit(const Netlist::Net *net) const
{
	const NetRtlil &rtlil = data_.index.net_rtlil.get(net->id);
	if (rtlil.name_bit.wire != nullptr)
		return rtlil.name_bit;
	return rtlil.bit;
}

void detail::ViewBuilder::setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit)
{
	NetRtlil &rtlil = data_.index.net_rtlil[net->id];
	rtlil.name_bit = bit;
	rtlil.name = detail::netName(bit, wireOrigin(bit.wire));
}

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
	dict<uint64_t, Netlist::Net *> &nets = data_.index.nets_by_bit;
	if (bit.wire != nullptr) {
		if (Netlist::Net *net = nets.at(detail::bitKey(bit), nullptr))
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
		net = nets.at(detail::bitKey(canon), nullptr);
		if (net == nullptr) {
			net = newNet(scope, canon);
			nets[detail::bitKey(canon)] = net;
		}
	}
	if (bit.wire != nullptr && bit != canon)
		nets[detail::bitKey(bit)] = net;
	return net;
}

Netlist::Net *detail::ViewBuilder::findOrMakeTieNet(Netlist::Instance *scope, const RTLIL::SigBit &canon)
{
	Netlist::Net::Const value = Netlist::Net::Const::Zero;
	if (canon.data == RTLIL::State::S1)
		value = Netlist::Net::Const::One;
	if (Netlist::Net *net = data_.scope_contents[scope].tieNet(value))
		return net;
	Netlist::Net *net = newNet(scope, canon);
	data_.scope_contents[scope].setTieNet(value, net);
	return net;
}

YOSYS_NAMESPACE_END
