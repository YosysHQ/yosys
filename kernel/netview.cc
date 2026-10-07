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

void NetView::build(RTLIL::Design *design)
{
	log_assert(!built());
	std::string reason;
	if (!buildable(design, reason))
		log_cmd_error("NetView: %s.\n", reason);
	design_ = design;
	buildTop(topModule(design));
}

void NetView::buildTop(RTLIL::Module *top)
{
	top_ = newInstance(nullptr, top, nullptr);
	buildScope(top, top_);
}

void NetView::reset()
{
	design_ = nullptr;
	top_ = nullptr;

	instances_.clear();
	cell_inst_.clear();
	module_scope_.clear();
	inst_cell_.clear();
	inst_module_.clear();
	next_inst_id_ = 1;
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
		if (!inst->leaf)
			buildScope(this->module(inst), inst);
	}
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

bool NetView::valid() const
{
	return built();
}

YOSYS_NAMESPACE_END
