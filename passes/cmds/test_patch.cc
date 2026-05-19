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
					auto neg = add->getPort(ID::B).as_wire()->driverCell();
					log_assert(neg->type == ID($not));


					RTLIL::Patch patcher;
					patcher.mod = module;
					patcher.map = SigMap(module);
					auto new_cell = patcher.addNeg(NEW_ID, patcher.Sub(NEW_ID, neg->getPort(ID::A), cell->getPort(ID::A)), SigSpec());
					// // sub->connections_ = cell->connections();
					// sub->parameters = add->parameters;
					// sub->connections_[ID::A] = add->getPort(ID::A);
					// sub->connections_[ID::B] = add->getPort(ID::B);
					// sub->connections_[ID::Y] = add->getPort(ID::Y);
					log_cell(new_cell);
					patcher.patch(add, new_cell);
				}
			}
		}
	}
} TestPatchPass;

PRIVATE_NAMESPACE_END
