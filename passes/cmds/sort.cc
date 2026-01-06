#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SortPass : Pass {
	SortPass() : Pass("sort", "sort the design objects") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sort\n");
		log("\n");
		log("Sorts the design objects.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing SORT pass.\n");
        if (args.size() != 1)
            log_cmd_error("This pass takes no arguments.\n");
        d->sort();
	}
} SortPass;

PRIVATE_NAMESPACE_END
