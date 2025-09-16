#include "kernel/functional.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FunctionalDummyBackend : public Backend {
	FunctionalDummyBackend() : Backend("functional_dummy", "dump generated Functional IR") {}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		// backend pass boiler plate
		log_header(design, "Executing dummy functional backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules())
		{
			log("Processing module `%s`.\n", module->name);

			// convert module to FunctionalIR
			auto ir = Functional::IR::from_module(module);
			*f << "module " << module->name.c_str() << "\n";

			// write node functions
			for (auto node : ir)
				*f << "  assign " << log_id(node.name())
				   << " = " << node.to_string() << "\n";
			*f << "\n";

			// write outputs and next state
			for (auto output : ir.outputs())
				*f << " " << log_id(output->kind)
				   << " " << log_id(output->name)
				   << " = " << log_id(output->value().name()) << "\n";
			for (auto state : ir.states())
				*f << " " << log_id(state->kind)
				   << " " << log_id(state->name)
				   << " = " << log_id(state->next_value().name()) << "\n";
		}
	}
} FunctionalDummyBackend;

PRIVATE_NAMESPACE_END
