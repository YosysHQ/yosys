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

void NetView::build(RTLIL::Design *design)
{
	log_assert(!built());
	RTLIL::Module *top = topModule(design);
	if (top == nullptr)
		log_cmd_error("NetView: no top module (run hierarchy -top).\n");
	buildTop(top);
}

// The top is 0, it is named after its module
void NetView::buildTop(RTLIL::Module *top)
{
	top_ = &instances_.emplace_back();
	top_->name = RTLIL::unescape_id(top->name);
	top_->type = top_->name;
	top_->parent = nullptr;
	top_->id = 0;
	top_->leaf = false;
	top_->ports = nullptr;
}

void NetView::reset()
{
	top_ = nullptr;

	instances_.clear();
}

bool NetView::valid() const
{
	return built();
}

YOSYS_NAMESPACE_END
