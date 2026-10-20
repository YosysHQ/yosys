#include "kernel/netview.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

NetView::~NetView()
{
	unregisterMonitor();
}

bool NetView::built() const
{
	return top_ != nullptr;
}

NetView::Instance *NetView::top() const
{
	return top_;
}

std::array<size_t, 3> NetView::counts() const
{
	if (!built())
		return {};
	return {instances_.size() - 1, nets_.size(), pins_.size()};
}

bool NetView::designAlive() const
{
	for (const auto &[idx, design] : *RTLIL::Design::get_all_designs()) {
		if (design == design_)
			return true;
	}
	return false;
}

void NetView::unregisterMonitor()
{
	if (design_ != nullptr && designAlive())
		design_->monitors.erase(this);
}

// A host-internal cell type (no library model)
bool detail::internalType(RTLIL::IdString type)
{
	return StaticCellTypes::categories.is_known(type) && type != ID($scopeinfo);
}

std::vector<std::string> detail::sourcePath(const RTLIL::AttrObject *object, std::string_view name)
{
	if (object->has_attribute(ID::hdlname))
		return object->get_hdlname_attribute();
	return detail::flattenPath(name);
}

// $flatten\a.\b.$x or $flatten\a/\b/$x for a, b and $x
std::vector<std::string> detail::flattenPath(std::string_view name)
{
	constexpr std::string_view prefix = "$flatten";
	if (!name.starts_with(prefix))
		return {};
	name.remove_prefix(prefix.size());
	std::vector<std::string> parts;
	while (name.starts_with('\\')) {
		size_t sep = detail::flattenSeparator(name);
		if (sep == std::string_view::npos)
			break;
		parts.emplace_back(name.substr(1, sep - 1));
		name.remove_prefix(sep + 1);
	}
	if (parts.empty() || name.empty())
		return {};
	parts.emplace_back(name);
	return parts;
}

// '.' or '/', then the next scope ('\') or the private name ('$')
size_t detail::flattenSeparator(std::string_view name)
{
	for (size_t i = 1; i + 1 < name.size(); i++) {
		bool sep = name[i] == '.' || name[i] == '/';
		if (sep && (name[i + 1] == '\\' || name[i + 1] == '$'))
			return i;
	}
	return std::string_view::npos;
}

bool detail::transparentType(RTLIL::IdString type)
{
	return type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo));
}

// Unescaped
std::string detail::plainName(RTLIL::PooledName id)
{
	return id.unescape();
}

RTLIL::IdString detail::escapedPortId(const RTLIL::Design *design, const RTLIL::Cell *cell, const RTLIL::Module *sub, const std::string &name)
{
	RTLIL::IdString pub = design->twines().find("\\" + name);
	if (name.empty() || name[0] != '$')
		return pub;
	bool known = (cell != nullptr && cell->hasPort(pub)) || (sub != nullptr && sub->wire(pub) != nullptr);
	if (known)
		return pub;
	return design->twines().find(name);
}

// Declared with a range - wider than one bit, or [n:n]
bool detail::isVector(const RTLIL::Wire *wire)
{
	return wire->width > 1 || wire->has_attribute(ID::single_bit_vector);
}

Netlist::NetName detail::netName(const RTLIL::SigBit &bit)
{
	RTLIL::Wire *wire = bit.wire;
	return {detail::plainName(wire->name), wire->to_hdl_index(bit.offset), !detail::isVector(wire), detail::sourcePath(wire, wire->name.str())};
}

Netlist::PortShape detail::wireShape(RTLIL::Wire *wire)
{
	Netlist::PortShape shape;
	shape.name = detail::plainName(wire->name);
	shape.width = wire->width;
	shape.vector = detail::isVector(wire);
	shape.from = wire->to_hdl_index(wire->width - 1);
	shape.to = wire->to_hdl_index(0);
	shape.dir = Netlist::portDir(wire->port_input, wire->port_output);
	return shape;
}

void detail::moduleShapes(RTLIL::Module *module, std::vector<Netlist::PortShape> &out)
{
	for (RTLIL::IdString port_name : module->ports) {
		RTLIL::Wire *wire = module->wire(port_name);
		if (wire->width > 0)
			out.push_back(detail::wireShape(wire));
	}
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
		// Width-0 ports have no pins
		if (width == 0)
			continue;
		Netlist::PortShape shape;
		shape.name = detail::plainName({cell->module, port});
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
		return Netlist::portDir(input, output);
	}
	bool input = yosys_celltypes.cell_input(cell->type, port);
	bool output = yosys_celltypes.cell_output(cell->type, port);
	return Netlist::portDir(input, output);
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
	if (sub != nullptr)
		detail::moduleShapes(sub, shapes);
	else if (ports_ == nullptr && !hostPorts(inst, shapes))
		log_cmd_error("NetView: no port model for cell type %s (cell %s).\n", inst->type, inst->name);
	else if (ports_ != nullptr && !ports_->ports(*inst, shapes)) {
		hostPorts(inst, shapes);
		unmodeled_.insert(inst->type);
	}

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

uint64_t detail::countInstances(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, uint64_t> &counts)
{
	auto it = counts.find(module);
	if (it != counts.end())
		return it->second;
	uint64_t count = 0;
	for (RTLIL::Cell *cell : module->cells()) {
		count++;
		if (RTLIL::Module *sub = detail::childModule(design, cell))
			count += detail::countInstances(design, sub, counts);
		count = std::min<uint64_t>(count, UINT32_MAX);
	}
	counts[module] = count;
	return count;
}

bool detail::checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &used, pool<RTLIL::Module *> &open, std::string &reason)
{
	open.insert(module);
	for (RTLIL::Cell *cell : module->cells()) {
		RTLIL::Module *sub = detail::childModule(design, cell);
		if (sub == nullptr)
			continue;
		if (open.count(sub)) {
			reason = stringf("module %s contains itself", sub);
			return false;
		}
		if (used.insert(sub).second && !detail::checkHierarchy(design, sub, used, open, reason))
			return false;
	}
	open.erase(module);
	return true;
}

bool NetView::buildable(RTLIL::Design *design, std::string &reason)
{
	RTLIL::Module *top = topModule(design);
	if (top == nullptr) {
		reason = "no top module (run hierarchy -top)";
		return false;
	}
	pool<RTLIL::Module *> seen = {top};
	pool<RTLIL::Module *> open;
	if (!detail::checkHierarchy(design, top, seen, open, reason))
		return false;
	dict<RTLIL::Module *, uint64_t> counts;
	if (detail::countInstances(design, top, counts) >= UINT32_MAX) {
		reason = "the unfolded design needs more than the 32-bit object ids hold";
		return false;
	}
	pool<RTLIL::Module *> blackboxes;
	for (RTLIL::Module *module : seen) {
		if (!detail::checkModule(module, reason))
			return false;
		detail::addUsedBlackboxes(design, module, blackboxes);
	}
	for (RTLIL::Module *blackbox : blackboxes) {
		if (!detail::checkIndices(blackbox, reason))
			return false;
	}
	return true;
}

bool detail::checkModule(RTLIL::Module *module, std::string &reason)
{
	if (!module->processes.empty()) {
		reason = stringf("module %s has processes (run proc)", module);
		return false;
	}
	return detail::checkIndices(module, reason);
}

bool detail::indicesFitInt(const RTLIL::Wire *wire)
{
	return wire->width <= 0 || int64_t(wire->start_offset) + wire->width - 1 <= INT_MAX;
}

bool detail::checkIndices(RTLIL::Module *module, std::string &reason)
{
	for (RTLIL::Wire *wire : module->wires()) {
		if (!detail::indicesFitInt(wire)) {
			reason = stringf("range of wire %s in module %s overflows", wire, module);
			return false;
		}
	}
	return true;
}

void detail::addUsedBlackboxes(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &blackboxes)
{
	for (RTLIL::Cell *cell : module->cells()) {
		RTLIL::Module *type = design->module(cell->type);
		if (type != nullptr && type->get_blackbox_attribute())
			blackboxes.insert(type);
	}
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
	for (const std::string &type : unmodeled_)
		log_warning("NetView: no port model for leaf type %s, its instances take the host ports.\n", type);
	for (const auto &[module, occurrences] : module_scopes_.data)
		tracked_.push_back(module->name);
	fingerprint_ = fingerprint();
	design_->monitors.insert(this);
}

void NetView::buildTop(RTLIL::Module *top)
{
	top_ = newInstance(nullptr, top, nullptr);
	makePins(top_);
	buildScope(top, top_);
}

void NetView::reset()
{
	unregisterMonitor();
	design_ = nullptr;
	top_ = nullptr;
	ports_ = nullptr;
	fingerprint_ = 0;
	tracked_.clear();
	dirty_ = false;
	changed_ = false;

	instances_.clear();
	pins_.clear();
	nets_.clear();
	terms_.clear();
	clearTables();
	next_inst_id_ = 1;
	next_pin_id_ = 1;
	next_net_id_ = 1;
	next_term_id_ = 1;
}

void NetView::clearTables()
{
	shape_store_.clear();
	shape_cache_.clear();
	unmodeled_.clear();
	sigmaps_.clear();
	bit_nets_.clear();
	scopes_.clear();
	cell_insts_.clear();
	module_scopes_.clear();
	inst_data_.clear();
	net_data_.clear();
}

std::unique_ptr<NetView> NetView::retire()
{
	unregisterMonitor();
	design_ = nullptr;
	clearTables();
	for (Instance &inst : instances_) {
		inst.pins = {};
		inst.children = {};
		inst.name = {};
		inst.hdlpath = {};
		inst.type = {};
		inst.master = {};
		inst.ports = nullptr;
	}
	for (Net &net : nets_) {
		net.pins = {};
		net.terms = {};
	}
	return std::make_unique<NetView>();
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
	inst->name = detail::plainName({design_, name});
	inst->type = detail::plainName({design_, type});

	// A uniquified module keeps its original name in hdlname
	inst->master = inst->type;
	if (module != nullptr && module->has_attribute(ID::hdlname))
		inst->master = module->get_string_attribute(ID::hdlname);

	// The top is 0
	inst->parent = parent;
	inst->netlist = this;
	inst->id = 0;
	if (parent != nullptr)
		inst->id = next_inst_id_++;

	// Leaves open no scope (module is nullptr)
	inst->leaf = module == nullptr;
	inst->internal = inst->leaf && detail::internalType(type);
	inst->ports = nullptr;

	inst_data_[inst->id] = {cell, module};
	if (cell != nullptr) {
		inst->hdlpath = detail::sourcePath(cell, cell->name.str());
		cell_insts_.add(cell->hashidx_, inst);
	}
	if (module != nullptr)
		module_scopes_.add(module, inst);
	if (parent != nullptr)
		parent->children.push_back(inst);
	return inst;
}

std::vector<RTLIL::Cell *> detail::statementOrder(RTLIL::Module *module)
{
	std::vector<RTLIL::Cell *> cells = module->cells();
	if (!std::is_sorted(cells.begin(), cells.end(), RTLIL::sort_by_name_str<RTLIL::Cell>()))
		std::reverse(cells.begin(), cells.end());
	return cells;
}

void NetView::buildScope(RTLIL::Module *module, Instance *scope)
{
	for (RTLIL::Cell *cell : detail::statementOrder(module)) {
		if (detail::transparentType(cell->type))
			continue;
		Instance *inst = newInstance(cell, detail::childModule(design_, cell), scope);
		makePins(inst);
		if (!inst->leaf)
			buildScope(this->module(inst), inst);
	}
	registerWires(module, scope);
}

void NetView::makePins(Instance *inst)
{
	RTLIL::Cell *c = cell(inst);
	RTLIL::Module *sub = module(inst);
	inst->ports = portsFor(inst, sub);
	for (uint32_t p = 0; p < inst->ports->size(); p++) {
		const PortShape &shape = (*inst->ports)[p];
		RTLIL::IdString port_id = detail::escapedPortId(design_, c, sub, shape.name);
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
				net = findOrMakeNet(inst->parent, sig[b]);
			Pin *pin = makePin(inst, p, b, net);

			// Term into the instance's scope
			if (inner_wire == nullptr || b >= inner_wire->width)
				continue;
			Net *inner_net = findOrMakeNet(inst, RTLIL::SigBit(inner_wire, b));
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
	net_data_[net->id].bit = bit;
	if (bit.wire != nullptr)
		setNameBit(net, bit);
	scopes_[scope].nets.push_back(net);
	return net;
}

detail::NameRank detail::nameRank(const RTLIL::SigBit &bit)
{
	const RTLIL::Wire *wire = bit.wire;
	bool port = wire->port_id != 0;
	bool keep = wire->get_bool_attribute(ID::keep);
	bool pub = wire->name.isPublic();
	size_t depth = detail::sourcePath(wire, wire->name.str()).size();
	return {!port, !keep, !pub, depth, wire->name.str(), bit.offset};
}

void NetView::registerWires(RTLIL::Module *module, Instance *scope)
{
	SigMap &sigmap = sigmapFor(module);
	for (RTLIL::Wire *wire : module->wires()) {
		bool pub = wire->name.isPublic();
		for (int b = 0; b < wire->width; b++) {
			RTLIL::SigBit bit(wire, b);
			RTLIL::SigBit canon = sigmap(bit);
			Net *net = nullptr;
			if (canon.wire != nullptr)
				net = bit_nets_.get(scope, canon);
			else if (pub)
				net = findOrMakeNet(scope, canon);
			if (net == nullptr)
				continue;
			if (canon.wire != nullptr)
				net_data_[net->id].wire_bits.push_back(bit);
			if (!pub)
				continue;

			// Public wires collapsed into another wire's net (assign aliases)
			// stay reachable under their own names
			scopes_[scope].aliases.push_back({detail::netName(bit), net});

			// A net is named after its best wire bit
			if (net->constant == Net::Const::None && detail::nameRank(bit) < detail::nameRank(nameBit(net)))
				setNameBit(net, bit);
		}
	}
}

SigMap &NetView::sigmapFor(RTLIL::Module *module)
{
	auto it = sigmaps_.find(module);
	if (it != sigmaps_.end())
		return it->second;
	SigMap &sigmap = sigmaps_.try_emplace(module, module).first->second;
	detail::addConnectAliases(module, sigmap);
	detail::addBarrierAliases(module, sigmap);
	return sigmap;
}

// $connect joins its two sides, as a module connection does
void detail::addConnectAliases(RTLIL::Module *module, SigMap &sigmap)
{
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type != ID($connect))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A), b = cell->getPort(ID::B);
		for (int i = 0; i < GetSize(a) && i < GetSize(b); i++)
			sigmap.add(a[i], b[i]);
	}
}

void detail::addBarrierAliases(RTLIL::Module *module, SigMap &sigmap)
{
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type != ID($barrier))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A), y = cell->getPort(ID::Y);
		for (int b = 0; b < GetSize(a) && b < GetSize(y); b++) {
			// Cell order doesn't matter here
			if (sigmap(a[b]).wire != nullptr && sigmap(y[b]).wire != nullptr)
				sigmap.add(y[b], a[b]);
		}
	}
}

uint64_t detail::bitKey(const RTLIL::SigBit &bit)
{
	return uint64_t(bit.wire->hashidx_) << 32 | uint32_t(bit.offset);
}

NetView::Net *NetView::NetsByScopeBit::get(const Instance *scope, const RTLIL::SigBit &bit) const
{
	return data.at({scope->id, detail::bitKey(bit)}, nullptr);
}

void NetView::NetsByScopeBit::set(const Instance *scope, const RTLIL::SigBit &bit, Net *net)
{
	data[{scope->id, detail::bitKey(bit)}] = net;
}

RTLIL::Cell *NetView::cell(const Instance *inst) const
{
	return inst_data_.get(inst->id).cell;
}

RTLIL::Module *NetView::module(const Instance *scope) const
{
	return inst_data_.get(scope->id).module;
}

NetView::Instance *NetView::instance(const RTLIL::Cell *cell, const Instance *scope) const
{
	const std::vector<Instance *> &all = cell_insts_.get(cell->hashidx_);
	for (Instance *inst : all) {
		if (inst->parent == scope || (scope == nullptr && all.size() == 1))
			return inst;
	}
	return nullptr;
}

const std::vector<NetView::Instance *> &NetView::scopes(const RTLIL::Module *module) const
{
	return module_scopes_.get(module);
}

const std::vector<RTLIL::SigBit> &NetView::wireBits(const Net *net) const
{
	return net_data_.get(net->id).wire_bits;
}

RTLIL::SigBit NetView::nameBit(const Net *net) const
{
	const NetData &data = net_data_.get(net->id);
	if (data.name_bit.wire != nullptr)
		return data.name_bit;
	return data.bit;
}

NetView::NetName NetView::wireName(const Net *net) const
{
	log_assert(net->constant == Net::Const::None);
	return net_data_.get(net->id).name;
}

// The name is copied out of RTLIL: reads must work on a stale view.
void NetView::setNameBit(Net *net, const RTLIL::SigBit &bit)
{
	NetData &data = net_data_[net->id];
	data.name_bit = bit;
	data.name = detail::netName(bit);
}

const NetView::ScopeData &NetView::scopeData(const Instance *scope) const
{
	static const ScopeData none;
	auto it = scopes_.find(scope);
	if (it == scopes_.end())
		return none;
	return it->second;
}

const std::vector<NetView::Net *> &NetView::nets(const Instance *scope) const
{
	return scopeData(scope).nets;
}

const std::vector<NetView::Alias> &NetView::aliases(const Instance *scope) const
{
	return scopeData(scope).aliases;
}

std::vector<NetView::Net *> NetView::constNets(bool one) const
{
	std::vector<Net *> nets;
	for (const auto &[scope, data] : scopes_) {
		if (data.consts[one] != nullptr)
			nets.push_back(data.consts[one]);
	}
	return nets;
}

NetView::Net *NetView::findOrMakeNet(Instance *scope, const RTLIL::SigBit &bit)
{
	if (bit.wire != nullptr) {
		if (Net *net = bit_nets_.get(scope, bit))
			return net;
	}
	RTLIL::SigBit canon = bit;
	if (bit.wire != nullptr)
		canon = sigmapFor(bit.wire->module)(bit);
	Net *net;
	if (canon.wire == nullptr) {
		if (canon.data != RTLIL::State::S0 && canon.data != RTLIL::State::S1)
			return nullptr; // x/z: unconnected
		Net *&slot = scopes_[scope].consts[canon.data == RTLIL::State::S1];
		if (slot == nullptr)
			slot = newNet(scope, canon);
		net = slot;
	} else {
		net = bit_nets_.get(scope, canon);
		if (net == nullptr) {
			net = newNet(scope, canon);
			bit_nets_.set(scope, canon, net);
		}
	}
	if (bit.wire != nullptr && bit != canon)
		bit_nets_.set(scope, bit, net);
	return net;
}

uint64_t detail::mix64(uint64_t state, uint64_t value)
{
	uint64_t z = state + value + 0x9e3779b97f4a7c15;
	z = (z ^ z >> 30) * 0xbf58476d1ce4e5b9;
	z = (z ^ z >> 27) * 0x94d049bb133111eb;
	return z ^ z >> 31;
}

struct detail::Fingerprint {
	uint64_t state = 0;
	void eat(uint64_t value) { state = detail::mix64(state, value); }
	void eat(uint32_t high, uint32_t low) { eat(uint64_t(high) << 32 | low); }
	void eat(RTLIL::IdString id) { eat(uint64_t(id.eq_key())); }
	void eat(const std::string &text)
	{
		eat(text.size());
		for (size_t at = 0; at < text.size(); at += 8) {
			uint64_t chunk = 0;
			memcpy(&chunk, text.data() + at, std::min<size_t>(8, text.size() - at));
			eat(chunk);
		}
	}
	void eat(const RTLIL::SigSpec &sig)
	{
		for (RTLIL::SigBit bit : sig)
			eat(bit.wire ? uint64_t(bit.wire->hashidx_) << 32 | uint32_t(bit.offset) : uint64_t(bit.data) + 8);
	}
	uint64_t yield() const { return state; }
};

uint64_t NetView::fingerprint() const
{
	detail::Fingerprint fp;
	detail::hashDesign(fp, design_);

	for (const std::string &name : tracked_) {
		RTLIL::Module *module = design_->module(name);
		fp.eat(module != nullptr);
		if (module != nullptr)
			detail::hashModule(fp, module);
	}
	return fp.yield();
}

void detail::hashDesign(Fingerprint &fp, RTLIL::Design *design)
{
	for (RTLIL::Module *module : design->modules()) {
		fp.eat(module->name.ref());
		fp.eat(module->hashidx_);
		bool blackbox = module->get_blackbox_attribute();
		fp.eat(blackbox);
		if (!blackbox)
			continue;
		for (RTLIL::IdString port : module->ports)
			detail::hashWire(fp, module->wire(port));
	}
	RTLIL::Module *top = NetView::topModule(design);
	Hasher::hash_t top_idx = 0;
	if (top != nullptr)
		top_idx = top->hashidx_;
	fp.eat(top_idx);
}

void detail::hashModule(Fingerprint &fp, RTLIL::Module *module)
{
	fp.eat(module->hashidx_);
	fp.eat(module->get_string_attribute(ID::hdlname));
	fp.eat(GetSize(module->processes));
	for (const auto &[lhs, rhs] : module->connections()) {
		fp.eat(GetSize(lhs));
		fp.eat(lhs);
		fp.eat(rhs);
	}
	for (RTLIL::Wire *wire : module->wires())
		detail::hashWire(fp, wire);
	for (RTLIL::Cell *cell : module->cells())
		detail::hashCell(fp, cell);
}

void detail::hashWire(Fingerprint &fp, RTLIL::Wire *wire)
{
	int flags = wire->upto | wire->port_input << 1 | wire->port_output << 2;
	flags |= wire->get_bool_attribute(ID::keep) << 3 | wire->has_attribute(ID::single_bit_vector) << 4;
	fp.eat(wire->name.ref());
	fp.eat(wire->hashidx_);
	fp.eat(wire->width, wire->start_offset);
	fp.eat(wire->port_id, flags);
	fp.eat(wire->get_string_attribute(ID::hdlname));
}

void detail::hashCell(Fingerprint &fp, RTLIL::Cell *cell)
{
	fp.eat(cell->name.ref());
	fp.eat(cell->hashidx_);
	fp.eat(cell->type.ref());
	fp.eat(cell->get_string_attribute(ID::hdlname));
	for (const auto &[port, sig] : cell->connections()) {
		fp.eat(port);
		fp.eat(GetSize(sig));
		fp.eat(sig);
	}
}

void NetView::invalidateCheck()
{
	dirty_ = true;
}

bool NetView::valid() const
{
	if (!built() || changed_)
		return false;
	if (!dirty_)
		return true;
	dirty_ = false;
	changed_ = !designAlive() || fingerprint() != fingerprint_;
	return !changed_;
}

void NetView::notify_module_add(RTLIL::Module *)
{
	dirty_ = true;
}

void NetView::notify_module_del(RTLIL::Module *)
{
	dirty_ = true;
}

void NetView::notify_connect(RTLIL::Cell *, RTLIL::IdString, const RTLIL::SigSpec &, const RTLIL::SigSpec &)
{
	dirty_ = true;
}

void NetView::notify_connect(RTLIL::Module *, const RTLIL::SigSig &)
{
	dirty_ = true;
}

void NetView::notify_connect(RTLIL::Module *, const std::vector<RTLIL::SigSig> &)
{
	dirty_ = true;
}

void NetView::notify_blackout(RTLIL::Module *)
{
	dirty_ = true;
}

YOSYS_NAMESPACE_END
