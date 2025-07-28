#include "kernel/yosys.h"
#include <csignal>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SegfaultPass : public Pass {
	SegfaultPass() : Pass("segfault", "segfault") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    segfault\n");
		log("\n");
		log("Segfault.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
        raise(SIGSEGV);
	}
} SegfaultPass;

PRIVATE_NAMESPACE_END
