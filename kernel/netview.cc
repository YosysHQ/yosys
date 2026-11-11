#include "kernel/netview_internal.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

#include <charconv>

YOSYS_NAMESPACE_BEGIN

Netlist::CellLibrary::~CellLibrary() = default;

bool Netlist::CellLibrary::isRegister(const Instance &) { return false; }

bool Netlist::CellLibrary::isClockPin(const Pin &) { return false; }

bool Netlist::CellLibrary::isBuffer(const Instance &) { return false; }

NetView::~NetView() = default;

Netlist::Instance *NetView::top() const { return data_->top; }

RTLIL::Design *NetView::design() const { return data_->design; }

NetView::Counts NetView::counts() const
{
	const detail::RecordStore &records = data_->records;
	return {records.instances.size() - 1, records.nets.size(), records.pins.size()};
}

bool detail::designAlive(const ViewData &data)
{
	return !data.design_shared || !data.design_owner.expired();
}

// A yosys internal cell type (no library cell)
bool detail::isInternalType(RTLIL::IdString type)
{
	return StaticCellTypes::categories.is_known(type) && type != ID($scopeinfo);
}

std::vector<std::string> detail::sourcePath(const RTLIL::AttrObject *object, std::string_view name)
{
	if (object->has_attribute(ID::hdlname))
		return object->get_hdlname_attribute();
	return detail::flattenPath(name);
}

// $flatten\a.\b.$x for a, b and $x, any separator for the dot
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

// A separator char, then the next scope ('\') or the private name ('$')
size_t detail::flattenSeparator(std::string_view name)
{
	for (bool any_char : {false, true}) {
		for (size_t i = 1; i + 1 < name.size(); i++) {
			bool sep = name[i] == '.';
			if (any_char)
				sep = !isalnum(static_cast<unsigned char>(name[i]));
			if (sep && (name[i + 1] == '\\' || name[i + 1] == '$'))
				return i;
		}
	}
	return std::string_view::npos;
}

// The N of a name that ends in [N]
bool detail::trailingIndex(std::string_view name, int &index)
{
	size_t open = name.rfind('[');
	if (open == std::string_view::npos || !name.ends_with(']'))
		return false;
	const char *first = name.data() + open + 1;
	const char *last = name.data() + name.size() - 1;
	int value = 0;
	auto [end, error] = std::from_chars(first, last, value);
	if (error != std::errc() || end != last)
		return false;
	index = value;
	return true;
}

bool detail::isTransparentType(RTLIL::IdString type)
{
	return type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo));
}

std::string detail::unescapedName(RTLIL::PooledName id) { return id.unescape(); }

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
bool detail::isVector(const RTLIL::Wire *wire) { return wire->width > 1 || wire->has_attribute(ID::single_bit_vector); }

Netlist::NetName detail::netName(const RTLIL::SigBit &bit, WireOrigin origin)
{
	RTLIL::Wire *wire = bit.wire;
	std::string name = detail::unescapedName(wire->name);
	bool scalar = !detail::isVector(wire) && origin == WireOrigin::Declared;
	int index = wire->to_hdl_index(bit.offset);
	if (origin == WireOrigin::SplitFromVector && wire->width == 1)
		detail::trailingIndex(name, index);
	return {name, index, scalar, detail::sourcePath(wire, wire->name.str())};
}

Netlist::Port detail::wirePort(RTLIL::Wire *wire)
{
	Netlist::Port port;
	port.name = detail::unescapedName(wire->name);
	port.width = wire->width;
	port.vector = detail::isVector(wire);
	port.from = wire->to_hdl_index(wire->width - 1);
	port.to = wire->to_hdl_index(0);
	port.dir = Netlist::portDir(wire->port_input, wire->port_output);
	return port;
}

void detail::modulePorts(RTLIL::Module *module, std::vector<Netlist::Port> &out)
{
	for (RTLIL::IdString port_name : module->ports) {
		RTLIL::Wire *wire = module->wire(port_name);
		if (wire->width > 0)
			out.push_back(detail::wirePort(wire));
	}
}

bool detail::cellTypePorts(const RTLIL::Cell *cell, std::vector<Netlist::Port> &out)
{
	bool static_type = StaticCellTypes::categories.is_known(cell->type);
	if (!static_type && !yosys_celltypes.cell_known(cell->type))
		return false;

	// Connected ports carry their width
	std::vector<std::pair<RTLIL::IdString, int>> ports;
	for (const auto &[port, sig] : cell->connections())
		ports.emplace_back(port, sig.size());

	// A fresh internal cell gets width 1
	if (ports.empty() && static_type) {
		for (RTLIL::IdString port : StaticCellTypes::port_info.inputs(cell->type))
			ports.emplace_back(port, 1);
		for (RTLIL::IdString port : StaticCellTypes::port_info.outputs(cell->type))
			ports.emplace_back(port, 1);
	}

	for (const auto &[port_id, width] : ports) {
		// Width-0 ports have no pins
		if (width == 0)
			continue;
		Netlist::Port port;
		port.name = detail::unescapedName({cell->module, port_id});
		port.width = width;
		port.from = width - 1;
		port.to = 0;
		port.dir = detail::cellTypePortDir(cell, port_id, static_type);
		out.push_back(port);
	}
	return !ports.empty();
}

Netlist::PortDir detail::cellTypePortDir(const RTLIL::Cell *cell, RTLIL::IdString port, bool static_type)
{
	bool input, output;
	if (static_type) {
		input = StaticCellTypes::port_info.inputs(cell->type).contains(port);
		output = StaticCellTypes::port_info.outputs(cell->type).contains(port);
	} else {
		input = yosys_celltypes.cell_input(cell->type, port);
		output = yosys_celltypes.cell_output(cell->type, port);
	}
	return Netlist::portDir(input, output);
}

RTLIL::Module *detail::topModule(RTLIL::Design *design)
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

void NetView::Counts::add(const Counts &other)
{
	instances = std::min<uint64_t>(instances + other.instances, UINT32_MAX);
	pins = std::min<uint64_t>(pins + other.pins, UINT32_MAX);
	nets = std::min<uint64_t>(nets + other.nets, UINT32_MAX);
}

bool NetView::Counts::fitIds() const { return instances < UINT32_MAX && pins < UINT32_MAX && nets < UINT32_MAX; }

NetView::Counts detail::countRecords(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, NetView::Counts> &counts)
{
	auto it = counts.find(module);
	if (it != counts.end())
		return it->second;
	NetView::Counts count;
	count.nets = std::min<uint64_t>(detail::wireBits(module) + 2, UINT32_MAX);
	for (RTLIL::Cell *cell : module->cells()) {
		NetView::Counts cell_count = {1, 0, detail::cellPinBits(design, cell)};
		// A $barrier can be an instance with a net per bit
		if (cell->type == ID($barrier))
			cell_count.nets = cell_count.pins;
		if (RTLIL::Module *sub = detail::childModule(design, cell))
			cell_count.add(detail::countRecords(design, sub, counts));
		count.add(cell_count);
	}
	counts[module] = count;
	return count;
}

uint64_t detail::portBits(RTLIL::Module *module)
{
	uint64_t bits = 0;
	for (RTLIL::IdString port : module->ports)
		bits += std::max(module->wire(port)->width, 0);
	return bits;
}

uint64_t detail::wireBits(RTLIL::Module *module)
{
	uint64_t bits = 0;
	for (RTLIL::Wire *wire : module->wires())
		bits += std::max(wire->width, 0);
	return bits;
}

uint64_t detail::cellPinBits(RTLIL::Design *design, const RTLIL::Cell *cell)
{
	if (RTLIL::Module *type = design->module(cell->type))
		return detail::portBits(type);
	uint64_t bits = 0;
	for (const auto &[port, sig] : cell->connections())
		bits += GetSize(sig);
	return bits;
}

bool detail::checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, ModuleSet &used, ModuleSet &open, std::string &reason)
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
	RTLIL::Module *top = detail::topModule(design);
	if (top == nullptr) {
		reason = "no top module (run hierarchy -top)";
		return false;
	}
	pool<RTLIL::Module *> seen = {top};
	pool<RTLIL::Module *> open;
	if (!detail::checkHierarchy(design, top, seen, open, reason))
		return false;
	dict<RTLIL::Module *, Counts> counts;
	Counts count = detail::countRecords(design, top, counts);
	count.pins += detail::portBits(top);
	if (!count.fitIds()) {
		reason = "the unfolded design needs more than the 32-bit object ids hold";
		return false;
	}
	pool<RTLIL::Module *> blackboxes;
	for (RTLIL::Module *module : seen) {
		if (!detail::checkModule(design, module, blackboxes, reason))
			return false;
	}
	return true;
}

bool detail::checkModule(RTLIL::Design *design, RTLIL::Module *module, ModuleSet &blackboxes, std::string &reason)
{
	if (!module->processes.empty()) {
		reason = stringf("module %s has processes (run proc)", module);
		return false;
	}
	for (RTLIL::Cell *cell : module->cells()) {
		RTLIL::Module *type = design->module(cell->type);
		bool new_blackbox = type != nullptr && type->get_blackbox_attribute() && blackboxes.insert(type).second;
		if (new_blackbox && !detail::checkIndices(type, reason))
			return false;
	}
	return detail::checkIndices(module, reason);
}

bool detail::checkIndices(RTLIL::Module *module, std::string &reason)
{
	for (RTLIL::Wire *wire : module->wires()) {
		if (wire->width > 0 && int64_t(wire->start_offset) + wire->width - 1 > INT_MAX) {
			reason = stringf("range of wire %s in module %s overflows", wire, module);
			return false;
		}
	}
	return true;
}

NetView::NetView(RTLIL::Design *design) : NetView(design, BuildOptions()) {}

NetView::NetView(RTLIL::Design *design, const BuildOptions &options) : data_(std::make_unique<detail::ViewData>())
{
	std::string reason;
	if (!buildable(design, reason))
		log_cmd_error("NetView: %s.\n", reason);
	data_->design = design;
	data_->design_owner = design->weak_from_this();
	data_->design_shared = !data_->design_owner.expired();
	data_->library = options.library;
	detail::ViewBuilder(*this, *data_, options.barrier_instances).build(detail::topModule(design));
	for (const std::string &type : data_->ports.types_not_in_library)
		log_warning("NetView: no port model for leaf type %s, its instances take the host ports.\n", type);
	data_->twines_serial = design->twines().serial();
	for (const auto &[module, occurrences] : data_->index.scopes_by_module.data)
		data_->watched_module_names.push_back(module->name);
	// body keys, children first, a child has a larger id
	// the top (id 0) needs none
	for (uint32_t id = data_->records.instances.size(); id-- > 1;) {
		const Netlist::Instance *inst = &data_->records.instances[id];
		if (!inst->isLeaf())
			data_->body_keys[id] = detail::scopeBodyHash(*this, inst);
	}
	markUpToDate();
}

Netlist::Instance *detail::RecordStore::newInstance()
{
	Netlist::Instance *inst = &instances.emplace_back();
	inst->id = next_inst_id++;
	return inst;
}

Netlist::Pin *detail::RecordStore::newPin()
{
	Netlist::Pin *pin = &pins.emplace_back();
	pin->id = next_pin_id++;
	return pin;
}

Netlist::Net *detail::RecordStore::newNet()
{
	Netlist::Net *net = &nets.emplace_back();
	net->id = next_net_id++;
	return net;
}

std::vector<RTLIL::Cell *> detail::statementOrder(RTLIL::Module *module)
{
	std::vector<RTLIL::Cell *> cells = module->cells();
	if (!std::is_sorted(cells.begin(), cells.end(), RTLIL::sort_by_name_str<RTLIL::Cell>()))
		std::reverse(cells.begin(), cells.end());
	return cells;
}

detail::NetNameRank detail::netNameRank(const RTLIL::SigBit &bit)
{
	const RTLIL::Wire *wire = bit.wire;
	bool port = wire->port_id != 0;
	bool keep = detail::hasUserKeep(wire);
	bool pub = wire->name.isPublic();
	size_t depth = detail::sourcePath(wire, wire->name.str()).size();
	return {!port, !keep, !pub, depth, wire->name.str(), bit.offset};
}

bool detail::hasUserKeep(const RTLIL::Wire *wire)
{
	if (!wire->get_bool_attribute(ID::keep))
		return false;
	RTLIL::Design *design = wire->module->design;
	return !wire->get_bool_attribute(design->twines().find(detail::ownedMarkerName(design, ID::keep)));
}

std::string detail::ownedMarkerName(RTLIL::Design *design, RTLIL::IdString attr)
{
	return std::string(detail::owned_marker_prefix) + detail::unescapedName({design, attr});
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

uint64_t detail::bitKey(const RTLIL::SigBit &bit) { return uint64_t(bit.wire->hashidx_) << 32 | uint32_t(bit.offset); }

Netlist::Net *detail::NetsByScopeBit::get(const Netlist::Instance *scope, const RTLIL::SigBit &bit) const
{
	return data.at({scope->id, detail::bitKey(bit)}, nullptr);
}

void detail::NetsByScopeBit::set(const Netlist::Instance *scope, const RTLIL::SigBit &bit, Netlist::Net *net)
{
	data[{scope->id, detail::bitKey(bit)}] = net;
}

RTLIL::Cell *NetView::cell(const Netlist::Instance *inst) const
{
	return data_->index.instance_rtlil.get(inst->id).cell;
}

RTLIL::Module *NetView::module(const Netlist::Instance *scope) const
{
	return data_->index.instance_rtlil.get(scope->id).module;
}

Netlist::Instance *NetView::instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const
{
	for (Netlist::Instance *inst : data_->index.instances_by_cell.get(cell->hashidx_)) {
		if (inst->parent == scope)
			return inst;
	}
	return nullptr;
}

const std::vector<Netlist::Instance *> &NetView::scopes(const RTLIL::Module *module) const
{
	return data_->index.scopes_by_module.get(module);
}

const std::vector<RTLIL::SigBit> &NetView::wireBits(const Netlist::Net *net) const
{
	return data_->index.net_rtlil.get(net->id).wire_bits;
}

Netlist::Instance *NetView::instanceById(uint32_t id) const { return detail::recordAt(data_->records.instances, id); }

Netlist::Pin *NetView::pinById(uint32_t id) const { return detail::recordAt(data_->records.pins, id - 1); }

Netlist::Net *NetView::netById(uint32_t id) const { return detail::recordAt(data_->records.nets, id - 1); }

Netlist::NetName NetView::name(const Netlist::Net *net) const
{
	log_assert(net->constant == Netlist::Net::Const::None);
	return data_->index.net_rtlil.get(net->id).name;
}

const std::vector<Netlist::Net *> &NetView::nets(const Netlist::Instance *scope) const
{
	return data_->scope_contents.get(scope->id).nets;
}

const std::vector<Netlist::NetName> &NetView::aliases(const Netlist::Net *net) const
{
	return data_->index.net_rtlil.get(net->id).aliases;
}

std::vector<Netlist::Net *> NetView::constNets(Netlist::Net::Const value) const
{
	std::vector<Netlist::Net *> nets;
	for (const detail::ScopeContents &contents : data_->scope_contents.data) {
		if (Netlist::Net *net = contents.tie_nets[value == Netlist::Net::Const::One])
			nets.push_back(net);
	}
	std::sort(nets.begin(), nets.end(), detail::idLess<Netlist::Net>);
	return nets;
}

std::vector<Netlist::Pin *> NetView::leafPins(const Netlist::Net *net, Netlist::WalkTarget target) const
{
	std::vector<Netlist::Pin *> pins;
	detail::addLeafPins(net, target, pins);
	return pins;
}

void detail::addLeafPins(const Netlist::Net *net, Netlist::WalkTarget target, std::vector<Netlist::Pin *> &out)
{
	for (Netlist::Pin *pin : net->pins) {
		if (!detail::pinMatchesTarget(pin, target))
			continue;
		if (pin->inst->isLeaf())
			out.push_back(pin);
		else if (pin->inner != nullptr)
			detail::addLeafPins(pin->inner, target, out);
	}
}

std::vector<const Netlist::Net *> detail::connectedNets(const Netlist::Net *net, bool down)
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
			if (down && pin->inner != nullptr)
				todo.push_back(pin->inner);
		}
	}
	return nets;
}

bool detail::pinMatchesTarget(const Netlist::Pin *pin, Netlist::WalkTarget target)
{
	if (pin->dir() == Netlist::PortDir::Inout)
		return true;
	bool drivers = target == Netlist::WalkTarget::Drivers;
	if (pin->inst->isLeaf())
		return pin->isDriver() == drivers;
	return pin->dir() == (drivers ? Netlist::PortDir::Output : Netlist::PortDir::Input);
}

void detail::nameChildren(Netlist::Instance *scope)
{
	for (Netlist::Instance *child : scope->children)
		child->unique_name = child->localName();
	bool changed = true;
	while (changed) {
		dict<std::string, int> counts;
		for (const Netlist::Instance *child : scope->children)
			counts[child->unique_name]++;
		changed = false;
		for (Netlist::Instance *child : scope->children) {
			if (counts.at(child->unique_name) > 1 && child->unique_name != child->name) {
				child->unique_name = child->name;
				changed = true;
			}
		}
	}
}

bool NetView::isRegister(const Netlist::Instance *inst) const
{
	if (data_->library != nullptr && data_->library->isRegister(*inst))
		return true;
	return !inst->isTop() && StaticCellTypes::categories.is_ff(cell(inst)->type);
}

bool NetView::isClockPin(const Netlist::Pin *pin) const
{
	if (data_->library != nullptr && data_->library->isClockPin(*pin))
		return true;
	const std::string &name = pin->port().name;
	bool clock_port_name = name == "C" || name == "CLK";
	return !pin->inst->isTop() && StaticCellTypes::categories.is_ff(cell(pin->inst)->type) && clock_port_name;
}

bool NetView::isBuffer(const Netlist::Instance *inst) const
{
	bool internal_buffer = !inst->isTop() && cell(inst)->type == ID($_BUF_);
	return internal_buffer || (data_->library != nullptr && data_->library->isBuffer(*inst));
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
		for (RTLIL::SigBit bit : sig) {
			if (bit.wire != nullptr)
				eat(detail::bitKey(bit));
			else
				eat(uint64_t(bit.data) + 8);
		}
	}
	uint64_t yield() const { return state; }
};

uint64_t NetView::bodyKey(const Netlist::Instance *scope) const
{
	log_assert(!scope->isLeaf() && !scope->isTop());
	return data_->body_keys.get(scope->id);
}

uint64_t detail::scopeBodyHash(const NetView &view, const Netlist::Instance *scope)
{
	uint64_t sum = 0;
	for (const Netlist::Port &port : *scope->ports) {
		detail::Fingerprint fp;
		fp.eat(uint64_t('P'));
		fp.eat(port.name);
		fp.eat(port.width, port.from);
		fp.eat(port.to, int(port.dir));
		sum += fp.yield();
	}
	for (const Netlist::Pin *pin : scope->pins)
		sum += detail::pinHash('T', "", view, pin, pin->inner);
	for (const Netlist::Net *net : view.nets(scope)) {
		detail::Fingerprint fp;
		fp.eat(uint64_t('N'));
		detail::eatNet(fp, view, net);
		sum += fp.yield();
	}
	for (const Netlist::Instance *child : scope->children) {
		detail::Fingerprint fp;
		if (child->isLeaf()) {
			fp.eat(uint64_t('L'));
			fp.eat(child->unique_name);
			fp.eat(child->type);
		} else {
			fp.eat(uint64_t('C'));
			fp.eat(child->unique_name);
			fp.eat(child->hdl_type);
			fp.eat(view.bodyKey(child));
		}
		sum += fp.yield();
		for (const Netlist::Pin *pin : child->pins)
			sum += detail::pinHash('c', child->unique_name, view, pin, pin->net);
	}
	return sum;
}

uint64_t detail::pinHash(char tag, const std::string &child, const NetView &view, const Netlist::Pin *pin, const Netlist::Net *net)
{
	detail::Fingerprint fp;
	fp.eat(uint64_t(tag));
	fp.eat(child);
	fp.eat(pin->port().name);
	fp.eat(uint64_t(pin->hdlIndex()));
	detail::eatNet(fp, view, net);
	return fp.yield();
}

void detail::eatNet(Fingerprint &fp, const NetView &view, const Netlist::Net *net)
{
	if (net == nullptr) {
		fp.eat(uint64_t(3)); // past Const::One
		return;
	}
	if (net->constant != Netlist::Net::Const::None) {
		fp.eat(uint64_t(net->constant));
		return;
	}
	Netlist::NetName name = view.name(net);
	fp.eat(name.path());
	if (!name.scalar)
		fp.eat(uint64_t(name.index));
}

uint64_t detail::designModuleHash(RTLIL::Module *module)
{
	detail::Fingerprint fp;
	fp.eat(module->name.str());
	fp.eat(module->hashidx_);
	bool blackbox = module->get_blackbox_attribute();
	fp.eat(blackbox);
	if (!blackbox)
		return fp.yield();
	for (RTLIL::IdString port : module->ports)
		fp.eat(detail::wireHash(module->wire(port)));
	return fp.yield();
}

void detail::hashModule(Fingerprint &fp, RTLIL::Module *module)
{
	fp.eat(module->hashidx_);
	fp.eat(module->get_string_attribute(ID::hdlname));
	fp.eat(GetSize(module->processes));
	uint64_t connections = 0;
	for (const auto &[lhs, rhs] : module->connections()) {
		detail::Fingerprint conn_fp;
		conn_fp.eat(GetSize(lhs));
		conn_fp.eat(lhs);
		conn_fp.eat(rhs);
		connections += conn_fp.yield();
	}
	fp.eat(connections);
	uint64_t wires = 0;
	for (RTLIL::Wire *wire : module->wires())
		wires += detail::wireHash(wire);
	fp.eat(wires);
	uint64_t cells = 0;
	for (RTLIL::Cell *cell : module->cells())
		cells += detail::cellHash(cell);
	fp.eat(cells);
}

uint64_t detail::wireHash(RTLIL::Wire *wire)
{
	detail::Fingerprint fp;
	int flags = wire->upto | wire->port_input << 1 | wire->port_output << 2;
	flags |= detail::hasUserKeep(wire) << 3 | wire->has_attribute(ID::single_bit_vector) << 4;
	fp.eat(wire->name.str());
	fp.eat(wire->hashidx_);
	fp.eat(wire->width, wire->start_offset);
	fp.eat(wire->port_id, flags);
	fp.eat(wire->get_string_attribute(ID::hdlname));
	return fp.yield();
}

uint64_t detail::cellHash(RTLIL::Cell *cell)
{
	detail::Fingerprint fp;
	fp.eat(cell->name.str());
	fp.eat(cell->hashidx_);
	fp.eat(cell->type.str());
	fp.eat(cell->get_string_attribute(ID::hdlname));
	uint64_t ports = 0;
	for (const auto &[port, sig] : cell->connections()) {
		detail::Fingerprint port_fp;
		port_fp.eat(RTLIL::PooledName(cell->module, port).str());
		port_fp.eat(GetSize(sig));
		port_fp.eat(sig);
		ports += port_fp.yield();
	}
	fp.eat(ports);
	return fp.yield();
}

uint64_t detail::designFingerprint(RTLIL::Design *design, const std::vector<std::string> &module_names)
{
	uint64_t modules = 0;
	for (RTLIL::Module *module : design->modules())
		modules += detail::designModuleHash(module);
	RTLIL::Module *top = detail::topModule(design);
	detail::Fingerprint fp;
	fp.eat(modules);
	Hasher::hash_t top_idx = 0;
	if (top != nullptr)
		top_idx = top->hashidx_;
	fp.eat(top_idx);
	for (const std::string &name : module_names) {
		RTLIL::Module *module = design->module(name);
		fp.eat(module != nullptr);
		if (module != nullptr)
			detail::hashModule(fp, module);
	}
	return fp.yield();
}

bool NetView::upToDate() const
{
	const detail::ViewData &data = *data_;
	if (!detail::designAlive(data) || data.design->twines().serial() != data.twines_serial)
		return false;
	return detail::designFingerprint(data.design, data.watched_module_names) == data.fingerprint;
}

void NetView::markUpToDate()
{
	data_->fingerprint = detail::designFingerprint(data_->design, data_->watched_module_names);
}

YOSYS_NAMESPACE_END
