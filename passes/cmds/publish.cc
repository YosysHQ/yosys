#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PublishPass : public Pass {
private:
	static void publish(RTLIL::IdString& id) {
		if (id.begins_with("$")) {
			log_debug("publishing %s\n", id.c_str());
			id = "\\" + id.str();
			log_debug("published %s\n", id.c_str());
		}
	}
public:
	PublishPass() : Pass("publish", "publish private cell types") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    publish\n");
		log("Makes all module names and cell types public by prefixing\n");
		log("%% with \\.\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PUBLISH pass. (make cell types public)\n");
		extra_args(args, 1, design);
		auto saved_modules = design->modules_;
		design->modules_.clear();
		for (auto& [name, mod] : saved_modules) {
			publish(mod->name);
			design->modules_[mod->name] = mod;
			for (auto* cell : mod->cells()) {
				publish(cell->type);
			}
		}
	}
} PublishPass;

PRIVATE_NAMESPACE_END
