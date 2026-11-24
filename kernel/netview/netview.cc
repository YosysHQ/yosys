#include "kernel/netview/netview_internal.h"
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

bool detail::isVector(const RTLIL::Wire *wire) { return wire->width > 1 || wire->has_attribute(ID::single_bit_vector); }

void detail::modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out)
{
	for (RTLIL::IdString port_name : module->ports) {
		RTLIL::Wire *wire = module->wire(port_name);
		if (wire->width <= 0)
			continue;
		int dir = wire->port_input * RTLIL::PD_INPUT | wire->port_output * RTLIL::PD_OUTPUT;
		Netlist::Port port = {
			.name = wire->name.unescape(),
			.width = wire->width,
			.from = wire->to_hdl_index(wire->width - 1),
			.to = wire->to_hdl_index(0),
			.dir = RTLIL::PortDir(dir),
			.vector = detail::isVector(wire),
		};
		out.push_back(std::move(port));
	}
}

bool detail::cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out)
{
	if (!yosys_celltypes.cell_known(cell->type))
		return false;
	for (const auto &[port_id, sig] : cell->connections()) {
		if (sig.size() == 0)
			continue;
		Netlist::Port port = {
			.name = RTLIL::PooledName(cell->module, port_id).unescape(),
			.width = sig.size(),
			.from = sig.size() - 1,
			.dir = cell->port_dir(port_id),
		};
		out.push_back(std::move(port));
	}
	return true;
}

RTLIL::Module *detail::topModule(RTLIL::Design *design)
{
	for (RTLIL::Module *module : design->modules()) {
		if (module->get_bool_attribute(ID::top))
			return module;
	}
	if (design->modules().size() != 1)
		return nullptr;
	return *design->modules().begin();
}

RTLIL::Module *detail::childModule(RTLIL::Design *design, const RTLIL::Cell *cell)
{
	RTLIL::Module *sub = design->module(cell->type);
	if (sub == nullptr || sub->get_blackbox_attribute())
		return nullptr;
	return sub;
}

// $flatten\a.\b.$x -> "a b $x", flatten names a private object that way, another name stays
std::string detail::flattenNames(const std::string &name)
{
	constexpr std::string_view prefix = "$flatten\\";
	std::string_view rest = name;
	if (!rest.starts_with(prefix))
		return name;
	rest.remove_prefix(prefix.size() - 1); // each scope name starts at its backslash
	std::string names;
	while (rest.starts_with('\\')) {
		size_t dot = std::min(rest.find(".\\"), rest.find(".$"));
		if (dot == std::string_view::npos)
			return name;
		names += std::string(rest.substr(1, dot - 1)) + " ";
		rest.remove_prefix(dot + 1);
	}
	return names + std::string(rest);
}

// records of one instance of a module, at most UINT32_MAX, false with a reason when a check fails
bool detail::countRecords(RTLIL::Module *module, ModuleRole role, RecordCounts &counts, std::string &reason)
{
	constexpr uint64_t open = UINT64_MAX; // walk is inside the module
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
	uint64_t count = 1;
	for (RTLIL::IdString port : module->ports)
		count += std::max(module->wire(port)->width, 0);
	counts[module] = open;
	if (role == ModuleRole::Scope && !detail::countBody(module, counts, reason, count))
		return false;
	counts[module] = std::min<uint64_t>(count, UINT32_MAX);
	return true;
}

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

// cells() is newest first, reversed it is creation order until a cell is removed
// a module sorted by name keeps name order, the barriers of a later checkpoint do not count
std::vector<RTLIL::Cell *> detail::statementOrder(RTLIL::Module *module)
{
	std::vector<RTLIL::Cell *> cells;
	for (RTLIL::Cell *cell : module->cells()) {
		// transparent cells have no instance
		if (!cell->type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo)))
			cells.push_back(cell);
	}
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

// $connect joins its two sides like a module connection
void detail::addConnectAliases(RTLIL::Module *module, SigMap &sigmap)
{
	for (RTLIL::Cell *cell : module->cells()) {
		if (cell->type != ID($connect))
			continue;
		RTLIL::SigSpec a = cell->getPort(ID::A);
		RTLIL::SigSpec b = cell->getPort(ID::B);
		for (int i = 0; i < GetSize(a) && i < GetSize(b); i++)
			sigmap.add(a[i], b[i]);
	}
}

Netlist::Instance *NetView::instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const
{
	return instance_by_cell_scope_.at({cell->hashidx_, scope->id}, nullptr);
}

// nets that ports join with this net, over the hierarchy
Netlist::NetList detail::connectedNets(const Netlist::Net *net)
{
	Netlist::NetList nets;
	pool<const Netlist::Net *> seen;
	Netlist::NetList todo = {net};
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
	uint64_t body = 0; // a sum, connections, wires and cells in any order
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

// module names, blackbox ports, top, and the wires, cells and connections of the view modules
uint64_t detail::designFingerprint(RTLIL::Design *design, const std::vector<std::string> &module_names)
{
	uint64_t modules = 0;
	for (RTLIL::Module *module : design->modules())
		modules += detail::designModuleHash(module);
	RTLIL::Module *top = detail::topModule(design);
	detail::Fingerprint fp;
	fp.eat(modules);
	uint64_t top_identity = 0;
	if (top != nullptr)
		top_identity = top->hashidx_;
	fp.eat(top_identity);
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
	// design that a shared_ptr held at the build is gone
	if (design_shared_ && design_owner_.expired())
		return false;
	bool names_changed = design_->twines().serial() != twines_serial_;
	if (names_changed)
		return false;
	return detail::designFingerprint(design_, watched_module_names_) == fingerprint_;
}

// for checkpoint, a barrier and an owned keep do not change the view
void NetView::markUpToDate() { fingerprint_ = detail::designFingerprint(design_, watched_module_names_); }

YOSYS_NAMESPACE_END
