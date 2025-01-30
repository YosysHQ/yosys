#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool abstract_state(Module* mod, Cell* cell, Wire* enable, bool enable_pol) {
	CellTypes ct;
	ct.setup_internals_ff();
	if (!ct.cell_types.count(cell->type))
		return false;
	FfData ff(nullptr, cell);
	// Doesn't matter if there was an enable signal already
	// we discard it and mux with symbolic value
	ff.has_ce = false;
	Wire* inp = cell->getPort(ID::D).as_wire();
	cell = ff.emit();

	Wire* abstracted = mod->addWire(NEW_ID, inp->width);
	SigSpec mux_a, mux_b;
	if (enable_pol) {
		mux_a = inp;
		mux_b = mod->Anyseq(NEW_ID, inp->width);
	} else {
		mux_a = mod->Anyseq(NEW_ID, inp->width);
		mux_b = inp;
	}
	(void)mod->addMux(NEW_ID,
	mux_a,
	mux_b,
	enable,
	abstracted);
	cell->setPort(ID::D, SigSpec(abstracted));
	return true;
}

struct AbstractPass : public Pass {
	AbstractPass() : Pass("abstract", "extract clock gating out of flip flops") { }
	void help() override {
		// TODO
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing ABSTRACT pass.\n");

		size_t argidx;
		enum Mode {
			None,
			State,
			Initial,
			Value,
		};
		Mode mode;
		std::string enable_name;
		bool enable_pol; // true is high
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-state") {
				mode = State;
				continue;
			}
			if (arg == "-init") {
				mode = Initial;
				continue;
			}
			if (arg == "-value") {
				mode = Value;
				continue;
			}
			if (arg == "-enable") {
				enable_name = args[++argidx];
				enable_pol = true;
				continue;
			}
			if (arg == "-enablen") {
				enable_name = args[++argidx];
				enable_pol = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		unsigned int changed_cells = 0;
		if ((mode == State) || (mode == Value)) {
			if (!enable_name.length())
				log_cmd_error("Unspecified enable wire\n");
			for (auto mod : design->selected_modules()) {
				log("module %s\n", mod->name.c_str());
				Wire *enable_wire = mod->wire("\\" + enable_name);
				if (!enable_wire)
					log_cmd_error("Enable wire %s not found in module %s\n", enable_name.c_str(), mod->name.c_str());
				if (mode == State) {
					for (auto cell : mod->selected_cells()) {
						log("cell %s\n", cell->name.c_str());
						changed_cells += abstract_state(mod, cell, enable_wire, enable_pol);
					}
				} else {
					// Value
					log_cmd_error("Unsupported (TODO)\n");
				}
			}
		} else if (mode == Initial) {
			log_cmd_error("Unsupported\n");
		} else {
			log_cmd_error("No mode selected, see help message\n");
		}
		log("Abstracted %d cell(s).\n", changed_cells);
	}
} AbstractPass;

PRIVATE_NAMESPACE_END
