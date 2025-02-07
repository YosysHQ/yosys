#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool abstract_state(Module* mod, Cell* cell, Wire* enable, bool enable_pol) {
	FfData ff(nullptr, cell);
	if (ff.has_sr)
		log_cmd_error("SR not supported\n");

	// Normalize to simpler FF
	ff.unmap_ce();
	ff.unmap_srst();
	if (ff.has_arst)
		ff.arst_to_aload();

	// Construct abstract value
	auto anyseq = mod->Anyseq(NEW_ID, ff.width);

	if (ff.has_aload) {
		// ad := enable ? anyseq : ad
		Wire* abstracted_ad = mod->addWire(NEW_ID, ff.sig_ad.size());
		SigSpec mux_a, mux_b;
		if (enable_pol) {
			mux_a = ff.sig_ad;
			mux_b = anyseq;
		} else {
			mux_a = anyseq;
			mux_b = ff.sig_ad;
		}
		(void)mod->addMux(NEW_ID,
			mux_a,
			mux_b,
			enable,
			abstracted_ad);
		ff.sig_ad = abstracted_ad;
	}
	// d := enable ? anyseq : d
	Wire* abstracted_d = mod->addWire(NEW_ID, ff.sig_d.size());
	SigSpec mux_a, mux_b;
	if (enable_pol) {
		mux_a = ff.sig_d;
		mux_b = anyseq;
	} else {
		mux_a = anyseq;
		mux_b = ff.sig_d;
	}
	(void)mod->addMux(NEW_ID,
		mux_a,
		mux_b,
		enable,
		abstracted_d);
	ff.sig_d = abstracted_d;
	(void)ff.emit();
	return true;
}

struct AbstractPortCtx {
	Module* mod;
	SigMap sigmap;
	pool<std::pair<Cell*, IdString>> outs;
};

void collect_selected_ports(AbstractPortCtx& ctx) {
	for (Cell* cell : ctx.mod->cells()) {
		for (auto& conn : cell->connections()) {
			// we bufnorm
			log_assert(conn.second.is_wire() || conn.second.is_fully_const());
			if (conn.second.is_wire() && cell->output(conn.first))
				if (ctx.mod->selected(cell) || ctx.mod->selected(conn.second.as_wire()))
					ctx.outs.insert(std::make_pair(cell, conn.first));
		}
	}
}

unsigned int abstract_value(Module* mod, Wire* enable, bool enable_pol) {
	AbstractPortCtx ctx {mod, SigMap(mod), {}};
	collect_selected_ports(ctx);
	unsigned int changed = 0;
	for (auto [cell, port] : ctx.outs) {
		SigSpec sig = cell->getPort(port);
		log_assert(sig.is_wire());
		Wire* original = mod->addWire(NEW_ID, sig.size());
		cell->setPort(port, original);
		auto anyseq = mod->Anyseq(NEW_ID, sig.size());
		// This code differs from abstract_state
		// in that we reuse the original signal as the mux output,
		// not input
		SigSpec mux_a, mux_b;
		if (enable_pol) {
			mux_a = original;
			mux_b = anyseq;
		} else {
			mux_a = anyseq;
			mux_b = original;
		}
		(void)mod->addMux(NEW_ID,
			mux_a,
			mux_b,
			enable,
			sig);
		changed++;
	}
	return changed;
}

unsigned int abstract_init(Module* mod) {
	AbstractPortCtx ctx {mod, SigMap(mod), {}};
	collect_selected_ports(ctx);

	unsigned int changed = 0;

	for (auto [cell, port] : ctx.outs) {
		SigSpec sig = cell->getPort(port);
		log_assert(sig.is_wire());
		if (!sig.as_wire()->has_attribute(ID::init))
			continue;

		Const init = sig.as_wire()->attributes.at(ID::init);
		sig.as_wire()->attributes.erase(ID::init);
		changed += sig.size();
	}
	return changed;
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

		design->bufNormalize(true);
		unsigned int changed = 0;
		if ((mode == State) || (mode == Value)) {
			if (!enable_name.length())
				log_cmd_error("Unspecified enable wire\n");
			CellTypes ct;
			if (mode == State)
				ct.setup_internals_ff();
			for (auto mod : design->selected_modules()) {
				log_debug("module %s\n", mod->name.c_str());
				Wire *enable_wire = mod->wire("\\" + enable_name);
				if (!enable_wire)
					log_cmd_error("Enable wire %s not found in module %s\n", enable_name.c_str(), mod->name.c_str());
				if (mode == State) {
					for (auto cell : mod->selected_cells())
						if (ct.cell_types.count(cell->type))
							changed += abstract_state(mod, cell, enable_wire, enable_pol);
				} else {
					changed += abstract_value(mod, enable_wire, enable_pol);
				}
			}
			if (mode == State)
				log("Abstracted %d cells.\n", changed);
			else
				log("Abstracted %d values.\n", changed);
		} else if (mode == Initial) {
			for (auto mod : design->selected_modules()) {
				changed += abstract_init(mod);
			}
			log("Abstracted %d bits.\n", changed);
		} else {
			log_cmd_error("No mode selected, see help message\n");
		}
		design->bufNormalize(false);
	}
} AbstractPass;

PRIVATE_NAMESPACE_END
