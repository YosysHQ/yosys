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
			SigMap sigmap(module);
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($add)) {
					Cell* add = cell;
					log_assert(add->getPort(ID::B).is_wire());
					log_assert(add->getPort(ID::B).known_driver());
					auto neg = add->getPort(ID::B)[0].wire->driverCell();
					log_assert(neg->type == ID($not));
					RTLIL::Patch patcher(module, nullptr);
					int width = cell->getPort(ID::A).size();
					auto sub = patcher.addSub(NEW_ID,
						neg->getPort(ID::A),
						add->getPort(ID::A),
						patcher.addWire(NEW_ID, width));
					auto new_out_wire = patcher.addWire(NEW_ID, width);
					auto new_cell = patcher.addNeg(NEW_ID, sub->getPort(ID::Y), new_out_wire);
					log_cell(new_cell);
					patcher.patch(add, ID::Y, new_out_wire);
				}
			}
		}
	}
} TestPatchPass;

PRIVATE_NAMESPACE_END
