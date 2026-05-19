#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include "kernel/unstable/patch.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TestPatchPass : public Pass {
	TestPatchPass() : Pass("test_patch", "test patcher") { }
	void help() override
	{
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		(void) args;
		design->sigNormalize();
		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($add)) {
					RTLIL::Patch patcher;
					patcher.mod = module;
					patcher.map = SigMap(module);
					RTLIL::Cell* sub = patcher.addCell(NEW_ID, ID($sub));
					// sub->connections_ = cell->connections();
					sub->parameters = cell->parameters;
					sub->connections_[ID::A] = cell->getPort(ID::A);
					sub->connections_[ID::B] = cell->getPort(ID::B);
					sub->connections_[ID::Y] = cell->getPort(ID::Y);
					log_cell(sub);
					patcher.patch(cell, sub);
				}
			}
		}
	}
} TestPatchPass;

PRIVATE_NAMESPACE_END
