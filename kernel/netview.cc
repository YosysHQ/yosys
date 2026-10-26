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
	return {records_.instances.size() - 1, records_.nets.size(), records_.pins.size()};
}

bool detail::designAlive(const RTLIL::Design *design)
{
	for (const auto &[idx, other] : *RTLIL::Design::get_all_designs()) {
		if (other == design)
			return true;
	}
	return false;
}

void NetView::unregisterMonitor()
{
	if (design_ != nullptr && detail::designAlive(design_))
		design_->monitors.erase(this);
}

// A host-internal cell type (no library model)
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

// A char not a letter or digit, then the next scope ('\') or the private name ('$')
size_t detail::flattenSeparator(std::string_view name)
{
	for (size_t i = 1; i + 1 < name.size(); i++) {
		bool sep = !isalnum(static_cast<unsigned char>(name[i]));
		if (sep && (name[i + 1] == '\\' || name[i + 1] == '$'))
			return i;
	}
	return std::string_view::npos;
}

bool detail::isTransparentType(RTLIL::IdString type)
{
	return type.in(ID($barrier), ID($connect), ID($input_port), ID($scopeinfo));
}

std::string detail::unescapedName(RTLIL::PooledName id)
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
	return {detail::unescapedName(wire->name), wire->to_hdl_index(bit.offset), !detail::isVector(wire), detail::sourcePath(wire, wire->name.str())};
}

Netlist::PortShape detail::wireShape(RTLIL::Wire *wire)
{
	Netlist::PortShape shape;
	shape.name = detail::unescapedName(wire->name);
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

bool detail::cellTypePortShapes(const RTLIL::Cell *cell, std::vector<Netlist::PortShape> &out)
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

	for (const auto &[port, width] : ports) {
		// Width-0 ports have no pins
		if (width == 0)
			continue;
		Netlist::PortShape shape;
		shape.name = detail::unescapedName({cell->module, port});
		shape.width = width;
		shape.from = width - 1;
		shape.to = 0;
		shape.dir = detail::cellTypePortDir(cell, port, table);
		out.push_back(shape);
	}
	return !ports.empty();
}

Netlist::Dir detail::cellTypePortDir(const RTLIL::Cell *cell, RTLIL::IdString port, CellTypeTable table)
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
		detail::ViewBuilder(*this).build(topModule(design));
	} catch (...) {
		reset();
		throw;
	}
	for (const std::string &type : shapes_.unmodeled_leaf_types)
		log_warning("NetView: no port model for leaf type %s, its instances take the host ports.\n", type);
	std::vector<std::string> module_names;
	for (const auto &[module, occurrences] : index_.scopes_by_module.data)
		module_names.push_back(module->name);
	watch_.arm(design_, std::move(module_names));
	design_->monitors.insert(this);
}

void NetView::reset()
{
	unregisterMonitor();
	design_ = nullptr;
	top_ = nullptr;
	ports_ = nullptr;
	watch_.clear();
	records_.clear();
	clearTables();
}

void NetView::clearTables()
{
	shapes_.clear();
	scope_contents_.clear();
	index_.clear();
}

std::unique_ptr<NetView> NetView::retire()
{
	unregisterMonitor();
	design_ = nullptr;
	clearTables();
	for (Instance &inst : records_.instances) {
		inst.pins = {};
		inst.children = {};
		inst.name = {};
		inst.hdlpath = {};
		inst.type = {};
		inst.master = {};
		inst.ports = nullptr;
	}
	for (Net &net : records_.nets) {
		net.pins = {};
		net.terms = {};
	}
	return std::make_unique<NetView>();
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

void detail::PortShapeCache::clear()
{
	shape_store.clear();
	shapes_by_leaf_type.clear();
	unmodeled_leaf_types.clear();
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

Netlist::Net *detail::NetsByScopeBit::get(const Netlist::Instance *scope, const RTLIL::SigBit &bit) const
{
	return data.at({scope->id, detail::bitKey(bit)}, nullptr);
}

void detail::NetsByScopeBit::set(const Netlist::Instance *scope, const RTLIL::SigBit &bit, Netlist::Net *net)
{
	data[{scope->id, detail::bitKey(bit)}] = net;
}

void detail::NetsByScopeBit::clear()
{
	data.clear();
}

RTLIL::Cell *NetView::cell(const Instance *inst) const
{
	return index_.instance_rtlil.get(inst->id).cell;
}

RTLIL::Module *NetView::module(const Instance *scope) const
{
	return index_.instance_rtlil.get(scope->id).module;
}

NetView::Instance *NetView::instance(const RTLIL::Cell *cell, const Instance *scope) const
{
	const std::vector<Instance *> &all = index_.instances_by_cell.get(cell->hashidx_);
	for (Instance *inst : all) {
		if (inst->parent == scope || (scope == nullptr && all.size() == 1))
			return inst;
	}
	return nullptr;
}

const std::vector<NetView::Instance *> &NetView::scopes(const RTLIL::Module *module) const
{
	return index_.scopes_by_module.get(module);
}

NetView::NetName NetView::wireName(const Net *net) const
{
	log_assert(net->constant == Net::Const::None);
	return index_.net_rtlil.get(net->id).name;
}

NetView::Net *NetView::ScopeContents::tieNet(Net::Const value) const
{
	if (value == Net::Const::One)
		return one_net;
	return zero_net;
}

void NetView::ScopeContents::setTieNet(Net::Const value, Net *net)
{
	if (value == Net::Const::One)
		one_net = net;
	else
		zero_net = net;
}

const NetView::ScopeContents &NetView::scopeContents(const Instance *scope) const
{
	static const ScopeContents none;
	auto it = scope_contents_.find(scope);
	if (it == scope_contents_.end())
		return none;
	return it->second;
}

const std::vector<NetView::Net *> &NetView::nets(const Instance *scope) const
{
	return scopeContents(scope).nets;
}

const std::vector<NetView::NetAlias> &NetView::aliases(const Instance *scope) const
{
	return scopeContents(scope).aliases;
}

std::vector<NetView::Net *> NetView::constNets(Net::Const value) const
{
	std::vector<Net *> nets;
	for (const auto &[scope, contents] : scope_contents_) {
		if (Net *net = contents.tieNet(value))
			nets.push_back(net);
	}
	return nets;
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
		for (RTLIL::SigBit bit : sig) {
			if (bit.wire != nullptr)
				eat(detail::bitKey(bit));
			else
				eat(uint64_t(bit.data) + 8);
		}
	}
	uint64_t yield() const { return state; }
};

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

void detail::ChangeDetector::arm(RTLIL::Design *design, std::vector<std::string> module_names)
{
	tracked_module_names_ = std::move(module_names);
	fingerprint_ = computeFingerprint(design);
}

void detail::ChangeDetector::noteEvent()
{
	maybe_changed_ = true;
}

bool detail::ChangeDetector::isStale(RTLIL::Design *design) const
{
	if (stale_)
		return true;
	if (!maybe_changed_)
		return false;
	maybe_changed_ = false;
	stale_ = !detail::designAlive(design) || computeFingerprint(design) != fingerprint_;
	return stale_;
}

void detail::ChangeDetector::clear()
{
	fingerprint_ = 0;
	tracked_module_names_.clear();
	maybe_changed_ = false;
	stale_ = false;
}

uint64_t detail::ChangeDetector::computeFingerprint(RTLIL::Design *design) const
{
	detail::Fingerprint fp;
	detail::hashDesign(fp, design);
	for (const std::string &name : tracked_module_names_) {
		RTLIL::Module *module = design->module(name);
		fp.eat(module != nullptr);
		if (module != nullptr)
			detail::hashModule(fp, module);
	}
	return fp.yield();
}

void NetView::invalidateCheck()
{
	watch_.noteEvent();
}

bool NetView::valid() const
{
	if (!built())
		return false;
	return !watch_.isStale(design_);
}

void NetView::notify_module_add(RTLIL::Module *)
{
	watch_.noteEvent();
}

void NetView::notify_module_del(RTLIL::Module *)
{
	watch_.noteEvent();
}

void NetView::notify_connect(RTLIL::Cell *, RTLIL::IdString, const RTLIL::SigSpec &, const RTLIL::SigSpec &)
{
	watch_.noteEvent();
}

void NetView::notify_connect(RTLIL::Module *, const RTLIL::SigSig &)
{
	watch_.noteEvent();
}

void NetView::notify_connect(RTLIL::Module *, const std::vector<RTLIL::SigSig> &)
{
	watch_.noteEvent();
}

void NetView::notify_blackout(RTLIL::Module *)
{
	watch_.noteEvent();
}

YOSYS_NAMESPACE_END
