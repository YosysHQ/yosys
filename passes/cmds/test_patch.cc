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
					Cell* add = cell;
					log_assert(add->getPort(ID::B).is_wire());
					log_assert(add->getPort(ID::B).known_driver());
					auto neg = add->getPort(ID::B)[0].wire->driverCell();
					log_assert(neg->type == ID($not));
					RTLIL::Patch patcher;
					patcher.mod = module;
					patcher.map = SigMap(module);
					auto sub = patcher.addSub(NEW_ID,
						neg->getPort(ID::A),
						cell->getPort(ID::A),
						patcher.addWire(NEW_ID, cell->getPort(ID::A).size()));
					auto new_cell = patcher.addNeg(NEW_ID, sub->getPort(ID::Y), SigSpec());
					log_cell(new_cell);
					patcher.patch(add, new_cell);
				}
			}
		}
	}
} TestPatchPass;

PRIVATE_NAMESPACE_END
