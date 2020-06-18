#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

struct TestPass : public Pass {
	TestPass() : Pass("test", "test") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx = 1;
		extra_args(args, argidx, design);
		log("Plugin test passed!\n");
	}
} TestPass;

YOSYS_NAMESPACE_END
