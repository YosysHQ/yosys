#include "kernel/netview_internal.h"
#include "kernel/newcelltypes.h"
#include "kernel/register.h"

#include <charconv>

YOSYS_NAMESPACE_BEGIN

Netlist::CellLibrary::~CellLibrary() = default;

NetView::NetView() : data_(std::make_unique<detail::ViewData>()) {}

NetView::~NetView() = default;

bool NetView::built() const { return data_->top != nullptr; }

Netlist::Instance *NetView::top() const { return data_->top; }

RTLIL::Design *NetView::design() const { return data_->design; }

NetView::Counts NetView::counts() const
{
	if (!built())
		return {};
	const detail::RecordStore &records = data_->records;
	return {records.instances.size() - 1, records.nets.size(), records.pins.size()};
}

bool detail::designAlive(const RTLIL::Design *design)
{
	for (const RTLIL::Design *other : *RTLIL::Design::get_all_designs()) {
		if (other == design)
			return true;
	}
	return false;
}

// A yosys internal cell type (no library cell)
bool detail::isInternalType(RTLIL::IdString type) { return StaticCellTypes::categories.is_known(type) && type != ID($scopeinfo); }

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

// The default '.' first, so a name part can hold other chars (u_$x)
size_t detail::flattenSeparator(std::string_view name)
{
	size_t dot = detail::findSeparator(name, SeparatorRule::DefaultDot);
	if (dot != std::string_view::npos)
		return dot;
	return detail::findSeparator(name, SeparatorRule::AnyChar);
}

// A separator char, then the next scope ('\') or the private name ('$')
size_t detail::findSeparator(std::string_view name, SeparatorRule rule)
{
	for (size_t i = 1; i + 1 < name.size(); i++) {
		bool sep = name[i] == '.';
		if (rule == SeparatorRule::AnyChar)
			sep = !isalnum(static_cast<unsigned char>(name[i]));
		if (sep && (name[i + 1] == '\\' || name[i + 1] == '$'))
			return i;
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

bool detail::isTransparentType(RTLIL::IdString type) { return type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo)); }

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
	CellTypeTable table = CellTypeTable::Yosys;
	if (StaticCellTypes::categories.is_known(cell->type))
		table = CellTypeTable::Static;
	if (table == CellTypeTable::Yosys && !yosys_celltypes.cell_known(cell->type))
		return false;

	// Connected ports carry their width
	std::vector<std::pair<RTLIL::IdString, int>> ports;
	for (const auto &[port, sig] : cell->connections())
		ports.emplace_back(port, sig.size());

	// A fresh internal cell gets width 1
	if (ports.empty() && table == CellTypeTable::Static) {
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
		port.dir = detail::cellTypePortDir(cell, port_id, table);
		out.push_back(port);
	}
	return !ports.empty();
}

Netlist::PortDir detail::cellTypePortDir(const RTLIL::Cell *cell, RTLIL::IdString port, CellTypeTable table)
{
	if (table == CellTypeTable::Static) {
		bool input = StaticCellTypes::port_info.inputs(cell->type).contains(port);
		bool output = StaticCellTypes::port_info.outputs(cell->type).contains(port);
		return Netlist::portDir(input, output);
	}
	bool input = yosys_celltypes.cell_input(cell->type, port);
	bool output = yosys_celltypes.cell_output(cell->type, port);
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

void detail::RecordCounts::add(const RecordCounts &other)
{
	instances = std::min<uint64_t>(instances + other.instances, UINT32_MAX);
	pins = std::min<uint64_t>(pins + other.pins, UINT32_MAX);
	nets = std::min<uint64_t>(nets + other.nets, UINT32_MAX);
}

bool detail::RecordCounts::fitIds() const { return instances < UINT32_MAX && pins < UINT32_MAX && nets < UINT32_MAX; }

detail::RecordCounts detail::countRecords(RTLIL::Design *design, RTLIL::Module *module, dict<RTLIL::Module *, RecordCounts> &counts)
{
	auto it = counts.find(module);
	if (it != counts.end())
		return it->second;
	RecordCounts count;
	count.nets = std::min<uint64_t>(detail::wireBits(module) + 2, UINT32_MAX);
	for (RTLIL::Cell *cell : module->cells()) {
		RecordCounts cell_count = {1, detail::cellPinBits(design, cell), 0};
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

bool detail::checkHierarchy(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module *> &used, pool<RTLIL::Module *> &open,
			    std::string &reason)
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
	dict<RTLIL::Module *, detail::RecordCounts> counts;
	detail::RecordCounts count = detail::countRecords(design, top, counts);
	count.pins += detail::portBits(top);
	if (!count.fitIds()) {
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

bool detail::indicesFitInt(const RTLIL::Wire *wire) { return wire->width <= 0 || int64_t(wire->start_offset) + wire->width - 1 <= INT_MAX; }

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

void NetView::build(RTLIL::Design *design) { build(design, BuildOptions()); }

void NetView::build(RTLIL::Design *design, const BuildOptions &options)
{
	log_assert(!built());
	std::string reason;
	if (!buildable(design, reason))
		log_cmd_error("NetView: %s.\n", reason);
	data_->design = design;
	data_->library = options.library;
	// A leaf type without ports errors out halfway, drop the partial view
	try {
		detail::ViewBuilder(*this, *data_).build(detail::topModule(design));
	} catch (...) {
		clear();
		throw;
	}
	for (const std::string &type : data_->ports.types_not_in_library)
		log_warning("NetView: no port model for leaf type %s, its instances take the host ports.\n", type);
	data_->watch.arm(design, data_->index.scopeModuleNames());
}

void NetView::clear()
{
	data_->watch.disarm();
	data_->design = nullptr;
	data_->top = nullptr;
	data_->library = nullptr;
	data_->records.clear();
	data_->clearTables();
}

void detail::ViewData::clearTables()
{
	ports.clear();
	scope_contents.clear();
	index.clear();
	body_keys.clear();
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

Netlist::Term *detail::RecordStore::newTerm()
{
	Netlist::Term *term = &terms.emplace_back();
	term->id = next_term_id++;
	return term;
}

void detail::RecordStore::clear()
{
	instances.clear();
	pins.clear();
	nets.clear();
	terms.clear();
	next_inst_id = 0;
	next_pin_id = 1;
	next_net_id = 1;
	next_term_id = 1;
}

void detail::PortStore::clear()
{
	lists.clear();
	lists_by_library_type.clear();
	types_not_in_library.clear();
}

std::vector<std::string> detail::RtlilIndex::scopeModuleNames() const
{
	std::vector<std::string> names;
	for (const auto &[module, occurrences] : scopes_by_module.data)
		names.push_back(module->name);
	return names;
}

void detail::RtlilIndex::clear()
{
	instances_by_cell.clear();
	scopes_by_module.clear();
	instance_rtlil.clear();
	net_rtlil.clear();
	nets_by_scope_bit.clear();
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
	bool keep = wire->get_bool_attribute(ID::keep);
	bool pub = wire->name.isPublic();
	size_t depth = detail::sourcePath(wire, wire->name.str()).size();
	return {!port, !keep, !pub, depth, wire->name.str(), bit.offset};
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

void detail::NetsByScopeBit::clear() { data.clear(); }

RTLIL::Cell *NetView::cell(const Netlist::Instance *inst) const { return data_->index.instance_rtlil.get(inst->id).cell; }

RTLIL::Module *NetView::module(const Netlist::Instance *scope) const { return data_->index.instance_rtlil.get(scope->id).module; }

Netlist::Instance *NetView::instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const
{
	for (Netlist::Instance *inst : data_->index.instances_by_cell.get(cell->hashidx_)) {
		if (inst->parent == scope)
			return inst;
	}
	return nullptr;
}

const std::vector<Netlist::Instance *> &NetView::scopes(const RTLIL::Module *module) const { return data_->index.scopes_by_module.get(module); }

const std::vector<RTLIL::SigBit> &NetView::wireBits(const Netlist::Net *net) const { return data_->index.net_rtlil.get(net->id).wire_bits; }

Netlist::NetName NetView::name(const Netlist::Net *net) const
{
	log_assert(net->constant == Netlist::Net::Const::None);
	return data_->index.net_rtlil.get(net->id).name;
}

Netlist::Net *detail::ScopeContents::tieNet(Netlist::Net::Const value) const
{
	if (value == Netlist::Net::Const::One)
		return one_net;
	return zero_net;
}

void detail::ScopeContents::setTieNet(Netlist::Net::Const value, Netlist::Net *net)
{
	if (value == Netlist::Net::Const::One)
		one_net = net;
	else
		zero_net = net;
}

const detail::ScopeContents &detail::ViewData::scopeContents(const Netlist::Instance *scope) const
{
	static const ScopeContents none;
	auto it = scope_contents.find(scope);
	if (it == scope_contents.end())
		return none;
	return it->second;
}

const std::vector<Netlist::Net *> &NetView::nets(const Netlist::Instance *scope) const { return data_->scopeContents(scope).nets; }

const std::vector<Netlist::NetAlias> &NetView::aliases(const Netlist::Instance *scope) const { return data_->scopeContents(scope).aliases; }

std::vector<Netlist::Net *> NetView::constNets(Netlist::Net::Const value) const
{
	std::vector<Netlist::Net *> nets;
	for (const auto &[scope, contents] : data_->scope_contents) {
		if (Netlist::Net *net = contents.tieNet(value))
			nets.push_back(net);
	}
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
		else if (pin->term != nullptr)
			detail::addLeafPins(pin->term->net, target, out);
	}
}

Netlist::PortDir detail::pinDirOfTarget(Netlist::WalkTarget target)
{
	if (target == Netlist::WalkTarget::Drivers)
		return Netlist::PortDir::Output;
	return Netlist::PortDir::Input;
}

bool detail::pinMatchesTarget(const Netlist::Pin *pin, Netlist::WalkTarget target)
{
	if (pin->inst->isLeaf())
		return pin->isDriver() == (target == Netlist::WalkTarget::Drivers);
	return pin->dir() == detail::pinDirOfTarget(target);
}

std::vector<std::string> NetView::childNames(const Netlist::Instance *scope) const
{
	std::vector<std::string> names;
	for (const Netlist::Instance *child : scope->children)
		names.push_back(child->localName());
	bool changed = true;
	while (changed)
		changed = detail::useOwnNames(scope, names);
	return names;
}

bool detail::useOwnNames(const Netlist::Instance *scope, std::vector<std::string> &names)
{
	dict<std::string, int> counts;
	for (const std::string &name : names)
		counts[name]++;
	bool changed = false;
	for (size_t i = 0; i < names.size(); i++) {
		const std::string &own = scope->children[i]->name;
		if (counts.at(names[i]) > 1 && names[i] != own) {
			names[i] = own;
			changed = true;
		}
	}
	return changed;
}

NetView::ScopeNames NetView::netNames(const Netlist::Instance *scope) const
{
	ScopeNames result;
	std::map<detail::NameKey, Netlist::OwnedName> owners;
	for (Netlist::Net *net : nets(scope)) {
		if (net->constant != Netlist::Net::Const::None)
			continue;
		Netlist::OwnedName claim = {name(net), net, true};
		result.shared += owners.count(detail::nameKey(claim.name));
		detail::claimName(owners, claim);
	}
	for (const Netlist::NetAlias &alias : aliases(scope)) {
		Netlist::NetName by_wire = alias.name;
		by_wire.hdlpath.clear();
		detail::claimName(owners, {alias.name, alias.net, false});
		detail::claimName(owners, {by_wire, alias.net, false});
	}
	for (const auto &[key, owner] : owners)
		result.names.push_back(owner);
	return result;
}

detail::NameKey detail::nameKey(const Netlist::NetName &name)
{
	if (name.scalar)
		return {name.path(), std::nullopt};
	return {name.path(), name.index};
}

bool detail::beats(const Netlist::OwnedName &claim, const Netlist::OwnedName &owner)
{
	if (claim.canonical != owner.canonical)
		return claim.canonical;
	return std::tie(claim.name.wire, claim.name.index) < std::tie(owner.name.wire, owner.name.index);
}

// The first claim of a name owns it until a claim beats it
void detail::claimName(std::map<NameKey, Netlist::OwnedName> &owners, const Netlist::OwnedName &claim)
{
	auto [it, added] = owners.try_emplace(detail::nameKey(claim.name), claim);
	if (!added && detail::beats(claim, it->second))
		it->second = claim;
}

std::string NetView::bodyKey(const Netlist::Instance *scope) const
{
	log_assert(built());
	return data_->body_keys.key(*this, scope);
}

std::string detail::BodyKeys::key(const NetView &view, const Netlist::Instance *scope)
{
	std::vector<std::string> lines;
	for (const Netlist::Port &port : *scope->ports)
		lines.push_back(detail::portLine(port));
	for (const Netlist::Pin *pin : scope->pins) {
		const Netlist::Net *inner = nullptr;
		if (pin->term != nullptr)
			inner = pin->term->net;
		lines.push_back(detail::pinLine("T", view, pin, inner));
	}
	for (const Netlist::Net *net : view.nets(scope)) {
		std::string line = "N";
		detail::addNetFields(line, view, net);
		lines.push_back(line);
	}
	std::vector<std::string> names = view.childNames(scope);
	for (size_t i = 0; i < names.size(); i++)
		addChildLines(lines, view, scope->children[i], names[i]);
	std::sort(lines.begin(), lines.end());
	std::string key;
	for (const std::string &line : lines)
		key += line + "\n";
	scope_numbers[scope->id] = numbers.emplace(key, uint32_t(numbers.size() + 1)).first->second;
	return key;
}

uint32_t detail::BodyKeys::number(const NetView &view, const Netlist::Instance *scope)
{
	if (scope_numbers.get(scope->id) == 0)
		key(view, scope);
	return scope_numbers.get(scope->id);
}

void detail::BodyKeys::addChildLines(std::vector<std::string> &lines, const NetView &view, const Netlist::Instance *child, const std::string &name)
{
	std::string line = "C";
	detail::addKeyField(line, name);
	if (child->isLeaf()) {
		detail::addKeyField(line, child->type);
	} else {
		detail::addKeyField(line, child->hdl_type);
		detail::addKeyField(line, std::to_string(number(view, child)));
	}
	lines.push_back(line);
	std::string head = "c";
	detail::addKeyField(head, name);
	for (const Netlist::Pin *pin : child->pins)
		lines.push_back(detail::pinLine(head, view, pin, pin->net));
}

void detail::BodyKeys::clear()
{
	numbers.clear();
	scope_numbers.clear();
}

void detail::addKeyField(std::string &line, std::string_view text)
{
	line += ' ';
	for (char c : text) {
		if (c == '\\' || c == ' ' || c == '\n')
			line += '\\';
		line += c;
	}
}

void detail::addNetFields(std::string &line, const NetView &view, const Netlist::Net *net)
{
	if (net == nullptr) {
		detail::addKeyField(line, "-");
		return;
	}
	if (net->constant != Netlist::Net::Const::None) {
		detail::addKeyField(line, std::to_string(int(net->constant)));
		return;
	}
	Netlist::NetName name = view.name(net);
	detail::addKeyField(line, "n" + name.path());
	if (!name.scalar)
		detail::addKeyField(line, std::to_string(name.index));
}

std::string detail::portLine(const Netlist::Port &port)
{
	std::string line = "P";
	detail::addKeyField(line, port.name);
	detail::addKeyField(line, std::to_string(port.width));
	detail::addKeyField(line, std::to_string(port.from));
	detail::addKeyField(line, std::to_string(port.to));
	detail::addKeyField(line, std::to_string(int(port.dir)));
	return line;
}

std::string detail::pinLine(std::string head, const NetView &view, const Netlist::Pin *pin, const Netlist::Net *net)
{
	detail::addKeyField(head, pin->port().name);
	detail::addKeyField(head, std::to_string(pin->hdlIndex()));
	detail::addNetFields(head, view, net);
	return head;
}

struct detail::Fingerprint {
	Hasher lo, hi;
	Fingerprint() { hi.force(0x9e3779b9); }
	template <typename T> void eat(const T &value)
	{
		lo.eat(value);
		hi.eat(value);
	}
	uint64_t yield() const { return uint64_t(hi.yield()) << 32 | lo.yield(); }
};

void detail::hashDesign(Fingerprint &fp, RTLIL::Design *design)
{
	for (RTLIL::Module *module : design->modules()) {
		fp.eat(module->name.str());
		fp.eat(module->hashidx_);
		bool blackbox = module->get_blackbox_attribute();
		fp.eat(blackbox);
		if (!blackbox)
			continue;
		for (RTLIL::IdString port : module->ports)
			detail::hashWire(fp, module->wire(port));
	}
	RTLIL::Module *top = detail::topModule(design);
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
	for (const RTLIL::SigSig &conn : module->connections())
		fp.eat(conn);
	for (RTLIL::Wire *wire : module->wires())
		detail::hashWire(fp, wire);
	for (RTLIL::Cell *cell : module->cells())
		detail::hashCell(fp, cell);
}

void detail::hashWire(Fingerprint &fp, RTLIL::Wire *wire)
{
	fp.eat(wire->name.str());
	fp.eat(wire->hashidx_);
	fp.eat(wire->width);
	fp.eat(wire->start_offset);
	fp.eat(wire->upto);
	fp.eat(wire->port_id);
	fp.eat(wire->port_input);
	fp.eat(wire->port_output);
	fp.eat(wire->get_bool_attribute(ID::keep));
	fp.eat(wire->get_string_attribute(ID::hdlname));
	fp.eat(wire->has_attribute(ID::single_bit_vector));
}

void detail::hashCell(Fingerprint &fp, RTLIL::Cell *cell)
{
	fp.eat(cell->name.str());
	fp.eat(cell->hashidx_);
	fp.eat(cell->type.str());
	fp.eat(cell->get_string_attribute(ID::hdlname));
	for (const auto &[port, sig] : cell->connections()) {
		fp.eat(RTLIL::PooledName(cell->module, port).str());
		fp.eat(sig);
	}
}

detail::ChangeDetector::~ChangeDetector() { disarm(); }

void detail::ChangeDetector::arm(RTLIL::Design *design, std::vector<std::string> module_names)
{
	design_ = design;
	watched_module_names_ = std::move(module_names);
	fingerprint_ = computeFingerprint();
	design_->monitors.insert(this);
}

// A deleted design has no monitors to leave
void detail::ChangeDetector::disarm()
{
	if (design_ != nullptr && detail::designAlive(design_))
		design_->monitors.erase(this);
	design_ = nullptr;
	fingerprint_ = 0;
	watched_module_names_.clear();
	maybe_changed_ = false;
	stale_ = false;
}

void detail::ChangeDetector::noteEvent() { maybe_changed_ = true; }

bool detail::ChangeDetector::isStale() const
{
	if (stale_)
		return true;
	if (!maybe_changed_)
		return false;
	maybe_changed_ = false;
	stale_ = !detail::designAlive(design_) || computeFingerprint() != fingerprint_;
	return stale_;
}

uint64_t detail::ChangeDetector::computeFingerprint() const
{
	detail::Fingerprint fp;
	detail::hashDesign(fp, design_);
	for (const std::string &name : watched_module_names_) {
		RTLIL::Module *module = design_->module(name);
		fp.eat(module != nullptr);
		if (module != nullptr)
			detail::hashModule(fp, module);
	}
	return fp.yield();
}

void detail::ChangeDetector::notify_module_add(RTLIL::Module *) { noteEvent(); }

void detail::ChangeDetector::notify_module_del(RTLIL::Module *) { noteEvent(); }

void detail::ChangeDetector::notify_connect(RTLIL::Cell *, RTLIL::IdString, const RTLIL::SigSpec &, const RTLIL::SigSpec &) { noteEvent(); }

void detail::ChangeDetector::notify_connect(RTLIL::Module *, const RTLIL::SigSig &) { noteEvent(); }

void detail::ChangeDetector::notify_connect(RTLIL::Module *, const std::vector<RTLIL::SigSig> &) { noteEvent(); }

void detail::ChangeDetector::notify_blackout(RTLIL::Module *) { noteEvent(); }

void NetView::recheck() { data_->watch.noteEvent(); }

bool NetView::upToDate() const
{
	if (!built())
		return false;
	return !data_->watch.isStale();
}

YOSYS_NAMESPACE_END
