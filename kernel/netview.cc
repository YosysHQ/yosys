#include "kernel/netview_internal.h"
#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

int Netlist::Port::hdlIndex(int bit) const { return from < to ? to - bit : to + bit; }

Netlist::Pin *Netlist::Instance::findPin(const std::string &port_name, int bit) const
{
	for (const Port &port : type->ports) {
		if (port.name == port_name && bit >= 0 && bit < port.width)
			return pins[port.first_pin + bit];
	}
	return nullptr;
}

const Netlist::Port &Netlist::Pin::port() const { return inst->type->ports[port_index]; }

RTLIL::PortDir Netlist::Pin::dir() const { return port().dir; }

int Netlist::Pin::hdlIndex() const { return port().hdlIndex(bit); }

bool Netlist::Pin::isDriver() const
{
	if (inst->isTop())
		return dir() == RTLIL::PD_INPUT || dir() == RTLIL::PD_INOUT; // a top input drives the design
	return inst->isLeaf() && (dir() == RTLIL::PD_OUTPUT || dir() == RTLIL::PD_INOUT);
}

RTLIL::IdString detail::escapedPortId(RTLIL::Design *design, const Netlist::Instance *inst, const std::string &name)
{
	RTLIL::IdString pub = design->twines().find("\\" + name);
	if (name.empty() || name[0] != '$')
		return pub;
	bool on_cell = inst->cell != nullptr && inst->cell->hasPort(pub);
	bool in_module = inst->module != nullptr && inst->module->wire(pub) != nullptr;
	if (on_cell || in_module)
		return pub;
	return design->twines().find(name);
}

// declared with a range, also a one-bit range
bool detail::isVector(const RTLIL::Wire *wire) { return wire->width > 1 || wire->has_attribute(ID::single_bit_vector); }

void detail::modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out)
{
	for (RTLIL::IdString port_name : module->ports) {
		RTLIL::Wire *wire = module->wire(port_name);
		if (wire->width <= 0)
			continue;
		RTLIL::PortDir dir = RTLIL::PortDir(wire->port_input * RTLIL::PD_INPUT | wire->port_output * RTLIL::PD_OUTPUT);
		int from = wire->to_hdl_index(wire->width - 1), to = wire->to_hdl_index(0);
		out.push_back({.name = wire->name.unescape(), .width = wire->width, .from = from, .to = to, .dir = dir,
		               .vector = detail::isVector(wire)});
	}
}

bool detail::cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out)
{
	if (!yosys_celltypes.cell_known(cell->type))
		return false;
	for (const auto &[port_id, sig] : cell->connections()) {
		// width-0 ports have no pins
		if (sig.size() == 0)
			continue;
		std::string name = RTLIL::PooledName(cell->module, port_id).unescape();
		out.push_back({.name = name, .width = sig.size(), .from = sig.size() - 1, .dir = cell->port_dir(port_id)});
	}
	return true;
}

RTLIL::Module *detail::topModule(RTLIL::Design *design)
{
	for (RTLIL::Module *module : design->modules()) {
		if (module->get_bool_attribute(ID::top))
			return module;
	}
	return design->modules().size() == 1 ? *design->modules().begin() : nullptr;
}

RTLIL::Module *detail::childModule(RTLIL::Design *design, const RTLIL::Cell *cell)
{
	RTLIL::Module *sub = design->module(cell->type);
	return (sub != nullptr && !sub->get_blackbox_attribute()) ? sub : nullptr;
}

// counts the records of one instance of a module, at most UINT32_MAX, false with a reason when a check fails
bool detail::countRecords(RTLIL::Module *module, ModuleRole role, RecordCounts &counts, std::string &reason)
{
	constexpr uint64_t open = UINT64_MAX; // the walk is inside the module
	if (counts.count(module)) {
		if (counts.at(module) == open)
			reason = stringf("module %s contains itself", module);
		return counts.at(module) != open;
	}
	for (RTLIL::Wire *wire : module->wires()) {
		if (wire->width > 0 && int64_t(wire->start_offset) + wire->width - 1 > INT_MAX) {
			reason = stringf("range of wire %s in module %s overflows", wire, module);
			return false;
		}
	}
	// the instance and its pins
	uint64_t count = 1;
	for (RTLIL::IdString port : module->ports)
		count += std::max(module->wire(port)->width, 0);
	counts[module] = open;
	if (role == ModuleRole::Scope && !detail::countBody(module, counts, reason, count))
		return false;
	counts[module] = std::min<uint64_t>(count, UINT32_MAX);
	return true;
}

// adds the nets and the cells of a module body
bool detail::countBody(RTLIL::Module *module, RecordCounts &counts, std::string &reason, uint64_t &count)
{
	if (!module->processes.empty()) {
		reason = stringf("module %s has processes (run proc)", module);
		return false;
	}
	// a net per wire bit and the two tie nets
	count += 2;
	for (RTLIL::Wire *wire : module->wires())
		count += std::max(wire->width, 0);
	for (RTLIL::Cell *cell : module->cells()) {
		if (RTLIL::Module *type = module->design->module(cell->type)) {
			ModuleRole role = type->get_blackbox_attribute() ? ModuleRole::Leaf : ModuleRole::Scope;
			if (!detail::countRecords(type, role, counts, reason))
				return false;
			count += counts.at(type);
			continue;
		}
		count += 1;
		for (const auto &[port, sig] : cell->connections())
			count += GetSize(sig);
	}
	return true;
}

bool NetView::buildable(RTLIL::Design *design, std::string &reason)
{
	RTLIL::Module *top = detail::topModule(design);
	if (top == nullptr) {
		reason = "no top module (run hierarchy -top)";
		return false;
	}
	detail::RecordCounts counts;
	if (!detail::countRecords(top, detail::ModuleRole::Scope, counts, reason))
		return false;
	if (counts.at(top) == UINT32_MAX)
		reason = "the unfolded design needs more than the 32-bit object ids hold";
	return counts.at(top) < UINT32_MAX;
}

NetView::NetView(RTLIL::Design *design, Netlist::CellLibrary *library) : design_(design)
{
	std::string reason;
	if (!buildable(design, reason))
		log_cmd_error("NetView: %s.\n", reason);
	design_owner_ = design->weak_from_this();
	design_shared_ = !design_owner_.expired();
	detail::ViewBuilder(*this, library).build(detail::topModule(design));
	twines_serial_ = design->twines().serial();
	markUpToDate();
}

// cells() lists the newest cell first, reversed it is creation order until a cell is removed
// a module sorted by name keeps name order
std::vector<RTLIL::Cell *> detail::statementOrder(RTLIL::Module *module)
{
	std::vector<RTLIL::Cell *> cells = module->cells();
	if (!std::is_sorted(cells.begin(), cells.end(), RTLIL::sort_by_name_str<RTLIL::Cell>()))
		std::reverse(cells.begin(), cells.end());
	return cells;
}

// a smaller rank is a better name
detail::NetNameRank detail::netNameRank(const RTLIL::SigBit &bit)
{
	const RTLIL::Wire *wire = bit.wire;
	return {wire->port_id == 0, !wire->name.isPublic(), wire->name.str(), bit.offset};
}

std::string detail::ownedMarkerName(RTLIL::Design *design, RTLIL::IdString attr)
{
	return std::string(detail::owned_marker_prefix) + RTLIL::PooledName(design, attr).unescape();
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

Netlist::Instance *NetView::instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const
{
	return instance_by_cell_scope_.at({cell->hashidx_, scope->id}, nullptr);
}

std::vector<const Netlist::Net *> detail::connectedNets(const Netlist::Net *net)
{
	std::vector<const Netlist::Net *> nets;
	pool<const Netlist::Net *> seen;
	std::vector<const Netlist::Net *> todo = {net};
	while (!todo.empty()) {
		const Netlist::Net *at = todo.back();
		todo.pop_back();
		if (at == nullptr || !seen.insert(at).second)
			continue;
		nets.push_back(at);
		for (const Netlist::Pin *port : at->boundary)
			todo.push_back(port->net);
		for (const Netlist::Pin *pin : at->pins) {
			if (pin->inner != nullptr)
				todo.push_back(pin->inner);
		}
	}
	return nets;
}

// hashes what a view reads of the design
// with body_keys it hashes a module body, see bodyKey
struct detail::Fingerprint {
	uint64_t state = 0;
	const BodyKeys *body_keys = nullptr;

	void eat(uint64_t value)
	{
		uint64_t z = state + value + 0x9e3779b97f4a7c15;
		z = (z ^ z >> 30) * 0xbf58476d1ce4e5b9;
		z = (z ^ z >> 27) * 0x94d049bb133111eb;
		state = z ^ z >> 31;
	}
	void eat(uint32_t high, uint32_t low) { eat(uint64_t(high) << 32 | low); }
	void eat(const std::string &text) { eat(std::hash<std::string>()(text)); }
	// a body has no object identity, a name stands for the object
	void eatIdentity(uint64_t hashidx)
	{
		if (body_keys == nullptr)
			eat(hashidx);
	}
	void eat(const RTLIL::SigSpec &sig)
	{
		for (RTLIL::SigBit bit : sig) {
			if (bit.wire == nullptr) {
				eat(uint64_t(bit.data) + 8);
			} else if (body_keys == nullptr) {
				eat(bit.wire->hashidx_, bit.offset);
			} else {
				eat(bit.wire->name.str());
				eat(uint64_t(bit.offset));
			}
		}
	}
};

// equal for modules with one source name and equal bodies, as uniquify makes them
// a child module counts as its body key, so keys has the children first
uint64_t detail::bodyKey(RTLIL::Module *module, BodyKeys &keys)
{
	if (keys.count(module->name))
		return keys.at(module->name);
	for (RTLIL::Cell *cell : module->cells()) {
		if (RTLIL::Module *sub = detail::childModule(module->design, cell))
			detail::bodyKey(sub, keys);
	}
	detail::Fingerprint fp = {0, &keys};
	fp.eat(detail::hdlName(module));
	detail::hashModule(fp, module);
	keys[module->name] = fp.state;
	return fp.state;
}

uint64_t detail::designModuleHash(RTLIL::Module *module)
{
	detail::Fingerprint fp;
	fp.eat(module->name.str());
	fp.eat(module->hashidx_);
	bool blackbox = module->get_blackbox_attribute();
	fp.eat(blackbox);
	if (!blackbox)
		return fp.state;
	for (RTLIL::IdString port : module->ports)
		fp.eat(detail::wireHash(module->wire(port)));
	return fp.state;
}

void detail::hashModule(Fingerprint &fp, RTLIL::Module *module)
{
	fp.eatIdentity(module->hashidx_);
	// bodyKey has the source name, a copy has the hdlname that its source lacks
	if (fp.body_keys == nullptr)
		fp.eat(module->get_string_attribute(ID::hdlname));
	fp.eat(GetSize(module->processes));
	uint64_t body = 0; // of the connections, wires and cells in any order
	for (const auto &[lhs, rhs] : module->connections()) {
		detail::Fingerprint conn_fp = {0, fp.body_keys};
		conn_fp.eat(GetSize(lhs));
		conn_fp.eat(lhs);
		conn_fp.eat(rhs);
		body += conn_fp.state;
	}
	for (RTLIL::Wire *wire : module->wires())
		body += detail::wireHash(wire, fp.body_keys);
	for (RTLIL::Cell *cell : module->cells())
		body += detail::cellHash(cell, fp.body_keys);
	fp.eat(body);
}

uint64_t detail::wireHash(RTLIL::Wire *wire, const BodyKeys *body_keys)
{
	detail::Fingerprint fp = {0, body_keys};
	int flags = wire->upto | wire->port_input << 1 | wire->port_output << 2;
	flags |= wire->has_attribute(ID::single_bit_vector) << 3;
	fp.eat(wire->name.str());
	fp.eatIdentity(wire->hashidx_);
	fp.eat(wire->width, wire->start_offset);
	fp.eat(wire->port_id, flags);
	return fp.state;
}

uint64_t detail::cellHash(RTLIL::Cell *cell, const BodyKeys *body_keys)
{
	detail::Fingerprint fp = {0, body_keys};
	fp.eat(cell->name.str());
	fp.eatIdentity(cell->hashidx_);
	if (body_keys != nullptr && body_keys->count(cell->type)) {
		fp.eat(body_keys->at(cell->type));
	} else {
		// bodyKey has the key of each child module first
		log_assert(body_keys == nullptr || detail::childModule(cell->module->design, cell) == nullptr);
		fp.eat(cell->type.str());
	}
	uint64_t ports = 0;
	for (const auto &[port, sig] : cell->connections()) {
		detail::Fingerprint port_fp = {0, body_keys};
		port_fp.eat(RTLIL::PooledName(cell->module, port).str());
		port_fp.eat(GetSize(sig));
		port_fp.eat(sig);
		ports += port_fp.state;
	}
	fp.eat(ports);
	return fp.state;
}

uint64_t detail::designFingerprint(RTLIL::Design *design, const std::vector<std::string> &module_names)
{
	uint64_t modules = 0;
	for (RTLIL::Module *module : design->modules())
		modules += detail::designModuleHash(module);
	RTLIL::Module *top = detail::topModule(design);
	detail::Fingerprint fp;
	fp.eat(modules);
	fp.eat(top != nullptr ? top->hashidx_ : 0);
	for (const std::string &name : module_names) {
		RTLIL::Module *module = design->module(name);
		fp.eat(module != nullptr);
		if (module != nullptr)
			detail::hashModule(fp, module);
	}
	return fp.state;
}

bool NetView::upToDate() const
{
	if ((design_shared_ && design_owner_.expired()) || design_->twines().serial() != twines_serial_)
		return false;
	return detail::designFingerprint(design_, watched_module_names_) == fingerprint_;
}

void NetView::markUpToDate() { fingerprint_ = detail::designFingerprint(design_, watched_module_names_); }

YOSYS_NAMESPACE_END
