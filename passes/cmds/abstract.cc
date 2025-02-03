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

bool abstract_value(Module* mod, Wire* wire, Wire* enable, bool enable_pol) {
	// (void)mod->addMux(NEW_ID,
	// 	mux_a,
	// 	mux_b,
	// 	enable,
	// 	abstracted);
	// 	cell->setPort(ID::D, SigSpec(abstracted));
	return false;
}

struct AbstractInitCtx {
	Module* mod;
	SigMap sigmap;
	pool<SigBit> init_bits;
};

void collect_init_bits_cells(AbstractInitCtx& ctx) {
	// TODO Should this discriminate between FFs and other cells?
	for (auto cell : ctx.mod->selected_cells()) {
		// Add all sigbits on all cell outputs to init_bits
		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first)) {
				for (auto bit : conn.second) {
					log_debug("init: cell %s output %s\n", cell->name.c_str(), log_signal(bit));
					ctx.init_bits.insert(ctx.sigmap(bit));
				}
			}
		}
	}
}

void collect_init_bits_wires(AbstractInitCtx& ctx) {
	for (auto wire : ctx.mod->selected_wires()) {
		auto canonical = ctx.sigmap(wire);
		// Find canonical drivers of all the wire bits and add them to init_bits
		for (auto bit : canonical.bits()) {
			log_debug("init: wire %s bit %s\n", wire->name.c_str(), log_signal(bit));
			ctx.init_bits.insert(ctx.sigmap(bit));
		}
	}
}

unsigned int abstract_init(Module* mod) {
	AbstractInitCtx ctx {mod, SigMap(mod), pool<SigBit>()};
	pool<SigBit> init_bits;
	collect_init_bits_cells(ctx);
	collect_init_bits_wires(ctx);
	unsigned int changed = 0;

	for (SigBit bit : ctx.init_bits) {
next_sigbit:
		if (!bit.is_wire() || !bit.wire->has_attribute(ID::init))
			continue;

		Const init = bit.wire->attributes.at(ID::init);
		std::vector<RTLIL::State>& bits = init.bits();
		bits[bit.offset] = RTLIL::State::Sx;
		changed++;

		for (auto bit : bits)
			if (bit != RTLIL::State::Sx)
				goto next_sigbit;
		// All bits are Sx, erase init attribute entirely
		bit.wire->attributes.erase(ID::init);
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
					// Value
					for (auto wire : mod->selected_wires()) {
						changed += abstract_value(mod, wire, enable_wire, enable_pol);
					}
					log_cmd_error("Unsupported (TODO)\n");
				}
			}
			log("Abstracted %d cells.\n", changed);
		} else if (mode == Initial) {
			for (auto mod : design->selected_modules()) {
				changed += abstract_init(mod);
			}
			log("Abstracted %d bits.\n", changed);
		} else {
			log_cmd_error("No mode selected, see help message\n");
		}
	}
} AbstractPass;

PRIVATE_NAMESPACE_END
