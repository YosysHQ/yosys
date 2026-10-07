#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

bool NetView::built() const
{
	return top_ != nullptr;
}

NetView::Instance *NetView::top() const
{
	return top_;
}

// A host-internal cell type (no library model)
bool detail::internalType(RTLIL::IdString type)
{
	return StaticCellTypes::categories.is_known(type);
}

Netlist::Dir detail::portDir(bool input, bool output)
{
	if (input && output)
		return Netlist::Dir::Inout;
	if (input)
		return Netlist::Dir::Input;
	if (output)
		return Netlist::Dir::Output;
	return Netlist::Dir::Unknown;
}

Netlist::PortShape detail::wireShape(RTLIL::Wire *wire)
{
	Netlist::PortShape shape;
	shape.name = RTLIL::unescape_id(wire->name);
	shape.width = wire->width;
	shape.from = wire->to_hdl_index(wire->width - 1);
	shape.to = wire->to_hdl_index(0);
	shape.dir = detail::portDir(wire->port_input, wire->port_output);
	return shape;
}

void detail::moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out)
{
	for (RTLIL::IdString port_name : module->ports)
		out.push_back(detail::wireShape(module->wire(port_name)));
}

bool detail::libraryPorts(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out)
{
	bool internal = StaticCellTypes::categories.is_known(cell->type);
	if (!internal && !yosys_celltypes.cell_known(cell->type))
		return false;

	// Connected ports carry their width
	std::vector<std::pair<RTLIL::IdString, int>> ports;
	for (const auto &[port, sig] : cell->connections())
		ports.emplace_back(port, sig.size());

	// A fresh internal cell gets width 1
	if (ports.empty() && internal) {
		for (RTLIL::IdString port : StaticCellTypes::port_info.inputs(cell->type))
			ports.emplace_back(port, 1);
		for (RTLIL::IdString port : StaticCellTypes::port_info.outputs(cell->type))
			ports.emplace_back(port, 1);
	}

	for (const auto &[port, width] : ports) {
		Netlist::PortShape shape;
		shape.name = RTLIL::unescape_id(port);
		shape.width = width;
		shape.from = width - 1;
		shape.to = 0;
		shape.dir = detail::libraryPortDir(cell, port, internal);
		out.push_back(shape);
	}
	return !ports.empty();
}

Netlist::Dir detail::libraryPortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool internal)
{
	if (internal) {
		bool input = StaticCellTypes::port_info.inputs(cell->type).contains(port);
		bool output = StaticCellTypes::port_info.outputs(cell->type).contains(port);
		return detail::portDir(input, output);
	}
	bool input = yosys_celltypes.cell_input(cell->type, port);
	bool output = yosys_celltypes.cell_output(cell->type, port);
	return detail::portDir(input, output);
}

bool NetView::hostPorts(const Instance *inst, std::vector<PortShape> &out) const
{
	RTLIL::Module *mod;
	if (isTop(inst))
		mod = module(inst);
	else
		mod = design_->module(cell(inst)->type);
	if (mod != nullptr) {
		detail::moduleShapes(mod, out);
		return true;
	}
	return detail::libraryPorts(cell(inst), out);
}

const NetView::PortShapes *NetView::portsFor(Instance *inst, RTLIL::Module *sub)
{
	// Library leaf shapes are shared per type, internal cells differ in width
	bool shared = inst->leaf && !inst->internal;
	if (shared) {
		auto it = shape_cache_.find(inst->type);
		if (it != shape_cache_.end())
			return it->second;
	}

	PortShapes &shapes = shape_store_.emplace_back();
	bool ok = true;
	if (sub != nullptr)
		detail::moduleShapes(sub, shapes);
	else if (ports_ != nullptr)
		ok = ports_->ports(*inst, shapes);
	else
		ok = hostPorts(inst, shapes);
	if (!ok)
		log_cmd_error("NetView: no port model for cell type %s (cell %s).\n", inst->type, inst->name);

	if (shared)
		shape_cache_[inst->type] = &shapes;
	return &shapes;
}

RTLIL::Module *NetView::topModule(RTLIL::Design *design)
{
	RTLIL::Module *top = nullptr;
	for (RTLIL::Module *module : design->modules()) {
		if (module->get_bool_attribute(ID::top))
			return module;
		top = module;
	}
	if (design->modules().size() == 1)
		return top;
	return nullptr;
}

RTLIL::Module *detail::childModule(RTLIL::Design *design, const RTLIL::Cell *cell)
{
	RTLIL::Module *sub = design->module(cell->type);
	if (sub == nullptr || sub->get_blackbox_attribute())
		return nullptr;
	return sub;
}

// Every non-top module may be instantiated once, more needs uniquify
bool detail::checkUniquified(RTLIL::Design *design, RTLIL::Module *top, RTLIL::Module *module, pool<RTLIL::Module *> &seen, std::string &reason)
{
	for (RTLIL::Cell *cell : module->cells()) {
		RTLIL::Module *sub = detail::childModule(design, cell);
		if (sub == nullptr)
			continue;
		if (sub == top || !seen.insert(sub).second) {
			reason = stringf("module %s instantiated more than once (run uniquify)", log_id(sub));
			return false;
		}
		if (!detail::checkUniquified(design, top, sub, seen, reason))
			return false;
	}
	return true;
}

bool NetView::buildable(RTLIL::Design *design, std::string &reason)
{
	RTLIL::Module *top = topModule(design);
	if (top == nullptr) {
		reason = "no top module (run hierarchy -top)";
		return false;
	}
	pool<RTLIL::Module *> seen;
	return detail::checkUniquified(design, top, top, seen, reason);
}

void NetView::build(RTLIL::Design *design, PortModel *ports)
{
	log_assert(!built());
	std::string reason;
	if (!buildable(design, reason))
		log_cmd_error("NetView: %s.\n", reason);
	design_ = design;
	ports_ = ports;
	// A leaf type without a port model errors out halfway, drop the partial view
	try {
		buildTop(topModule(design));
	} catch (...) {
		reset();
		throw;
	}
}

void NetView::buildTop(RTLIL::Module *top)
{
	top_ = newInstance(nullptr, top, nullptr);
	makePins(top_);
	buildScope(top, top_);
}

void NetView::reset()
{
	design_ = nullptr;
	top_ = nullptr;
	ports_ = nullptr;

	instances_.clear();
	pins_.clear();
	nets_.clear();
	terms_.clear();
	shape_store_.clear();
	shape_cache_.clear();
	sigmaps_.clear();
	bit_net_.clear();
	const_nets_.clear();
	scope_nets_.clear();
	cell_inst_.clear();
	module_scope_.clear();
	inst_cell_.clear();
	inst_module_.clear();
	next_inst_id_ = 1;
	next_pin_id_ = 1;
	next_net_id_ = 1;
	next_term_id_ = 1;
}

NetView::Instance *NetView::newInstance(RTLIL::Cell *cell, RTLIL::Module *module, Instance *parent)
{
	Instance *inst = &instances_.emplace_back();

	// The top has no cell, it is named after its module
	RTLIL::IdString name, type;
	if (cell != nullptr) {
		name = cell->name;
		type = cell->type;
	} else {
		name = module->name;
		type = module->name;
	}
	inst->name = RTLIL::unescape_id(name);
	inst->type = RTLIL::unescape_id(type);

	// The top is 0
	inst->parent = parent;
	inst->id = 0;
	if (parent != nullptr)
		inst->id = next_inst_id_++;

	// Leaves open no scope (module is nullptr)
	inst->leaf = module == nullptr;
	inst->internal = inst->leaf && detail::internalType(type);
	inst->ports = nullptr;

	inst_cell_[inst->id] = cell;
	inst_module_[inst->id] = module;
	if (cell != nullptr)
		cell_inst_[cell->hashidx_] = inst;
	if (module != nullptr)
		module_scope_[module] = inst;
	if (parent != nullptr)
		parent->children.push_back(inst);
	return inst;
}

void NetView::buildScope(RTLIL::Module *module, Instance *scope)
{
	for (RTLIL::Cell *cell : module->cells()) {
		Instance *inst = newInstance(cell, detail::childModule(design_, cell), scope);
		makePins(inst);
		if (!inst->leaf)
			buildScope(this->module(inst), inst);
	}
}

void NetView::makePins(Instance *inst)
{
	RTLIL::Cell *c = cell(inst);
	RTLIL::Module *sub = module(inst);
	inst->ports = portsFor(inst, sub);
	for (uint32_t p = 0; p < inst->ports->size(); p++) {
		const PortShape &shape = (*inst->ports)[p];
		RTLIL::IdString port_id = RTLIL::escape_id(shape.name);
		RTLIL::SigSpec sig;
		if (c != nullptr && c->hasPort(port_id))
			sig = c->getPort(port_id);
		RTLIL::Wire *inner_wire = nullptr;
		if (sub != nullptr)
			inner_wire = sub->wire(port_id);
		for (int b = 0; b < shape.width; b++) {
			// Outer net
			Net *net = nullptr;
			if (b < sig.size())
				net = findOrMakeNet(c->module, sig[b]);
			Pin *pin = makePin(inst, p, b, net);

			// Term into the instance's scope
			if (inner_wire == nullptr || b >= inner_wire->width)
				continue;
			Net *inner_net = findOrMakeNet(sub, RTLIL::SigBit(inner_wire, b));
			if (inner_net != nullptr)
				makeTerm(pin, inner_net);
		}
	}
}

NetView::Pin *NetView::makePin(Instance *inst, uint32_t port, int bit, Net *net)
{
	Pin *pin = &pins_.emplace_back();
	pin->inst = inst;
	pin->net = net;
	pin->term = nullptr;
	pin->id = next_pin_id_++;
	pin->port = port;
	pin->bit = bit;
	inst->pins.push_back(pin);
	if (net != nullptr)
		net->pins.push_back(pin);
	return pin;
}

void NetView::makeTerm(Pin *pin, Net *inner_net)
{
	Term *term = &terms_.emplace_back();
	term->pin = pin;
	term->net = inner_net;
	term->id = next_term_id_++;
	pin->term = term;
	inner_net->terms.push_back(term);
}

NetView::Net *NetView::newNet(Instance *scope, const RTLIL::SigBit &bit)
{
	Net *net = &nets_.emplace_back();
	net->scope = scope;
	net->id = next_net_id_++;
	net->constant = Net::Const::None;
	if (bit.wire == nullptr && bit.data == RTLIL::State::S1)
		net->constant = Net::Const::One;
	else if (bit.wire == nullptr)
		net->constant = Net::Const::Zero;
	scope_nets_[scope].push_back(net);
	return net;
}

SigMap &NetView::sigmapFor(RTLIL::Module *module) const
{
	auto it = sigmaps_.find(module);
	if (it != sigmaps_.end())
		return it->second;
	return sigmaps_.try_emplace(module, module).first->second;
}

uint64_t detail::bitKey(const RTLIL::SigBit &bit)
{
	return uint64_t(bit.wire->hashidx_) << 32 | uint32_t(bit.offset);
}

NetView::Net *NetView::knownNet(const RTLIL::SigBit &bit) const
{
	auto it = bit_net_.find(detail::bitKey(bit));
	if (it == bit_net_.end())
		return nullptr;
	return it->second;
}

RTLIL::Cell *NetView::cell(const Instance *inst) const
{
	return inst_cell_.get(inst->id);
}

RTLIL::Module *NetView::module(const Instance *scope) const
{
	return inst_module_.get(scope->id);
}

NetView::Instance *NetView::instance(const RTLIL::Cell *cell) const
{
	auto it = cell_inst_.find(cell->hashidx_);
	if (it == cell_inst_.end())
		return nullptr;
	return it->second;
}

NetView::Instance *NetView::scope(const RTLIL::Module *module) const
{
	auto it = module_scope_.find(module);
	if (it == module_scope_.end())
		return nullptr;
	return it->second;
}

const std::vector<NetView::Net *> &NetView::nets(const Instance *scope) const
{
	static const std::vector<Net *> none;
	auto it = scope_nets_.find(scope);
	if (it == scope_nets_.end())
		return none;
	return it->second;
}

NetView::Net *NetView::constNet(const Instance *scope, bool one) const
{
	auto it = const_nets_.find(scope);
	if (it == const_nets_.end())
		return nullptr;
	return it->second[one];
}

NetView::Net *NetView::findOrMakeNet(RTLIL::Module *module, const RTLIL::SigBit &bit)
{
	if (bit.wire != nullptr) {
		if (Net *net = knownNet(bit))
			return net;
	}
	RTLIL::SigBit canon = bit;
	if (bit.wire != nullptr)
		canon = sigmapFor(bit.wire->module)(bit);
	Net *net;
	if (canon.wire == nullptr) {
		if (canon.data != RTLIL::State::S0 && canon.data != RTLIL::State::S1)
			return nullptr; // x/z: unconnected
		Instance *s = scope(module);
		Net *&slot = const_nets_[s][canon.data == RTLIL::State::S1];
		if (slot == nullptr)
			slot = newNet(s, canon);
		net = slot;
	} else {
		net = knownNet(canon);
		if (net == nullptr) {
			net = newNet(scope(canon.wire->module), canon);
			bit_net_[detail::bitKey(canon)] = net;
		}
	}
	if (bit.wire != nullptr && bit != canon)
		bit_net_[detail::bitKey(bit)] = net;
	return net;
}

bool NetView::valid() const
{
	return built();
}

YOSYS_NAMESPACE_END
