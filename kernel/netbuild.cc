#include "kernel/netview_internal.h"
#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

detail::ViewBuilder::ViewBuilder(NetView &view, Netlist::CellLibrary *library) : view_(view), library_(library) {}

void detail::ViewBuilder::build(RTLIL::Module *top)
{
	view_.top_ = newInstance(nullptr, top, nullptr);
	buildScope(view_.top_);
	for (const std::string &type : types_not_in_library_)
		log_warning("NetView: no port model for leaf type %s, its instances take the host ports.\n", type);
}

const Netlist::CellType *detail::ViewBuilder::typeOf(const RTLIL::Cell *cell, RTLIL::Module *module)
{
	RTLIL::IdString id = cell != nullptr ? RTLIL::IdString(cell->type) : module->name;
	if (const Netlist::CellType *shared = shared_types_.at(id, nullptr))
		return shared;
	Netlist::CellType &type = view_.types_.emplace_back();
	type.name = RTLIL::PooledName(view_.design_, id).unescape();
	type.hdl_name = type.name;
	bool shared = true;
	if (module != nullptr) {
		view_.watched_module_names_.push_back(module->name); // upToDate hashes its body
		type.hdl_name = detail::hdlName(module);
		type.body_key = detail::bodyKey(module, body_keys_);
		detail::modulePorts(module, type.ports);
	} else {
		using Kind = Netlist::CellType::Kind;
		type.kind = StaticCellTypes::categories.is_known(cell->type) ? Kind::InternalCell : Kind::LibraryCell;
		shared = leafPorts(cell, type);
		// the yosys cell types add to what the library knows
		type.is_buffer = type.is_buffer || cell->type == ID($_BUF_);
	}
	uint32_t pins = 0;
	for (Netlist::Port &port : type.ports) {
		port.first_pin = pins;
		pins += port.width;
	}
	if (shared)
		shared_types_[id] = &type;
	return &type;
}

// a leaf asks library -> blackbox -> yosys cell types, false when the ports are the connections of this cell only
bool detail::ViewBuilder::leafPorts(const RTLIL::Cell *cell, Netlist::CellType &type)
{
	if (library_ != nullptr && library_->describe(type))
		return true;
	if (library_ != nullptr)
		types_not_in_library_.insert(type.name);
	if (RTLIL::Module *blackbox = view_.design_->module(cell->type)) {
		detail::modulePorts(blackbox, type.ports);
		return true;
	}
	bool known = detail::cellTypePorts(cell, type.ports);
	bool connected = !cell->connections().empty();
	if (!known && (library_ == nullptr || connected))
		log_cmd_error("NetView: no port model for cell type %s (cell %s).\n", type.name, cell->name.unescape());
	return false;
}

Netlist::Instance *detail::ViewBuilder::newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Netlist::Instance *parent)
{
	Netlist::Instance *inst = &view_.instances_.emplace_back();
	// the top has no cell, it is named after its module
	inst->name = cell != nullptr ? cell->name.unescape() : module->name.unescape();
	inst->type = typeOf(cell, module);
	inst->id = view_.instances_.size() - 1;
	inst->parent = parent;
	inst->cell = cell;
	inst->module = module;
	if (cell != nullptr)
		view_.instance_by_cell_scope_[{cell->hashidx_, parent->id}] = inst;
	if (parent != nullptr)
		parent->children.push_back(inst);
	makePins(inst);
	return inst;
}

void detail::ViewBuilder::buildScope(Netlist::Instance *scope)
{
	for (RTLIL::Cell *cell : detail::statementOrder(scope->module)) {
		// transparent cells have no instance
		if (cell->type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo)))
			continue;
		Netlist::Instance *inst = newInstance(cell, detail::childModule(view_.design_, cell), scope);
		if (!inst->isLeaf())
			buildScope(inst);
	}
	nameNets(scope);
}

void detail::ViewBuilder::makePins(Netlist::Instance *inst)
{
	RTLIL::Cell *cell = inst->cell;
	RTLIL::Module *module = inst->module;
	for (uint32_t port_index = 0; port_index < inst->type->ports.size(); port_index++) {
		const Netlist::Port &port = inst->type->ports[port_index];
		RTLIL::IdString port_id = detail::escapedPortId(view_.design_, inst, port.name);
		RTLIL::SigSpec sig;
		if (cell != nullptr && cell->hasPort(port_id))
			sig = cell->getPort(port_id);
		RTLIL::Wire *inner_wire = module != nullptr ? module->wire(port_id) : nullptr;
		for (int bit = 0; bit < port.width; bit++) {
			Netlist::Net *net = bit < sig.size() ? findOrMakeNet(inst->parent, sig[bit]) : nullptr;
			uint32_t id = view_.pins_.size() + 1;
			view_.pins_.push_back({.inst = inst, .net = net, .id = id, .port_index = port_index, .bit = bit});
			Netlist::Pin *pin = &view_.pins_.back();
			inst->pins.push_back(pin);
			if (net != nullptr)
				net->pins.push_back(pin);
			if (inner_wire == nullptr || bit >= inner_wire->width)
				continue;
			pin->inner = findOrMakeNet(inst, RTLIL::SigBit(inner_wire, bit));
			if (pin->inner != nullptr)
				pin->inner->boundary.push_back(pin);
		}
	}
}

void detail::ViewBuilder::nameNets(Netlist::Instance *scope)
{
	SigMap &sigmap = sigmapFor(scope->module);
	for (RTLIL::Wire *wire : scope->module->wires()) {
		if (!wire->name.isPublic())
			continue;
		for (int b = 0; b < wire->width; b++) {
			RTLIL::SigBit bit(wire, b);
			RTLIL::SigBit canon = sigmap(bit);
			if (canon.wire == nullptr) {
				findOrMakeNet(scope, canon); // a public wire on a constant makes the tie net
				continue;
			}
			Netlist::Net *net = nets_by_scope_bit_.at({scope->id, canon}, nullptr);
			if (net != nullptr && detail::netNameRank(bit) < detail::netNameRank(net->name_bit))
				setNameBit(net, bit);
		}
	}
}

// made on first use, joins module connections, $connect and $barriers
SigMap &detail::ViewBuilder::sigmapFor(RTLIL::Module *module)
{
	auto [it, added] = sigmaps_.try_emplace(module, module);
	if (added) {
		detail::addConnectAliases(module, it->second);
		addBarrierAliases(module, it->second);
	}
	return it->second;
}

// SigMap add(from, to) keeps the root of to, a constant is always the root
void detail::ViewBuilder::addBarrierAliases(RTLIL::Module *module, SigMap &sigmap) const
{
	RTLIL::IdString cut = module->design->twines().find(detail::cut_attr);
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type != ID($barrier))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A), y = cell->getPort(ID::Y);
		for (int b = 0; b < GetSize(a) && b < GetSize(y); b++) {
			RTLIL::SigBit a_root = sigmap(a[b]);
			bool a_is_const_01 = a_root == RTLIL::State::S0 || a_root == RTLIL::State::S1;
			bool a_has_net = a_root.wire != nullptr || a_is_const_01;
			if (sigmap(y[b]).wire == nullptr || !a_has_net)
				continue;
			// the root is A, or Y when only A is a cut wire, a cut wire never names a net
			bool a_is_cut = a[b].wire != nullptr && a[b].wire->get_bool_attribute(cut);
			if (a_is_cut && !y[b].wire->get_bool_attribute(cut))
				sigmap.add(a[b], y[b]);
			else
				sigmap.add(y[b], a[b]);
		}
	}
}

// a bit that splitnets made is a scalar with the index in its name
void detail::ViewBuilder::setNameBit(Netlist::Net *net, const RTLIL::SigBit &bit)
{
	net->name_bit = bit;
	RTLIL::Wire *wire = bit.wire;
	net->name = {wire->name.unescape(), wire->to_hdl_index(bit.offset), !detail::isVector(wire)};
}

// each SigMap class bit finds the net of its canonical bit
// bit must be a constant or a wire bit of the scope's module
Netlist::Net *detail::ViewBuilder::findOrMakeNet(Netlist::Instance *scope, const RTLIL::SigBit &bit)
{
	RTLIL::SigBit canon = bit;
	if (bit.wire != nullptr)
		canon = sigmapFor(bit.wire->module)(bit);
	bool one = canon == RTLIL::State::S1;
	if (canon.wire == nullptr && canon != RTLIL::State::S0 && !one)
		return nullptr; // x and z stay unconnected
	Netlist::Net *&net = nets_by_scope_bit_[{scope->id, canon}];
	if (net != nullptr)
		return net;
	net = &view_.nets_.emplace_back();
	net->id = view_.nets_.size();
	net->scope = scope;
	scope->nets.push_back(net);
	if (canon.wire != nullptr)
		setNameBit(net, canon);
	else
		net->constant = one ? Netlist::Net::Const::One : Netlist::Net::Const::Zero;
	return net;
}

YOSYS_NAMESPACE_END
