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
		RTLIL::Patch patcher;
		design->bufNormalize();
		for (auto module : design->selected_modules()) {
			patcher.mod = module;
			patcher.map = SigMap(module);
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($add)) {
					RTLIL::Cell* sub = patcher.addCell(NEW_ID, ID($sub));
					sub->connections_ = cell->connections();
					sub->parameters = cell->parameters;
					sub->setPort(ID::A, cell->getPort(ID::A));
					sub->setPort(ID::B, cell->getPort(ID::B));
					sub->setPort(ID::Y, cell->getPort(ID::Y));
					patcher.patch();
				}
			}
		}
	}
} TestPatchPass;

PRIVATE_NAMESPACE_END
