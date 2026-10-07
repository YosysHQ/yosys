#include "kernel/netview.h"
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

void NetView::build(RTLIL::Design *design)
{
	log_assert(!built());
	RTLIL::Module *top = topModule(design);
	if (top == nullptr)
		log_cmd_error("NetView: no top module (run hierarchy -top).\n");
	design_ = design;
	buildTop(top);
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
