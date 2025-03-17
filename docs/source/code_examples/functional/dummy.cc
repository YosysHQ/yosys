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
			log("Processing module `%s`.\n", module->name.c_str());

			// convert module to FunctionalIR
			auto ir = Functional::IR::from_module(module);
			*f << "module " << module->name.c_str() << "\n";

			// write node functions
			for (auto node : ir)
				*f << "  assign " << id2cstr(node.name())
				   << " = " << node.to_string() << "\n";
			*f << "\n";

			// write outputs and next state
			for (auto output : ir.outputs())
				*f << " " << id2cstr(output->kind)
				   << " " << id2cstr(output->name)
				   << " = " << id2cstr(output->value().name()) << "\n";
			for (auto state : ir.states())
				*f << " " << id2cstr(state->kind)
				   << " " << id2cstr(state->name)
				   << " = " << id2cstr(state->next_value().name()) << "\n";
		}
	}
} FunctionalDummyBackend;

PRIVATE_NAMESPACE_END
