#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EnableLogic {
	Wire* wire;
	bool pol;
};

bool abstract_state_port(FfData& ff, SigSpec& port_sig, std::set<int> offsets, EnableLogic enable) {
	// Construct abstract value
	auto anyseq = ff.module->Anyseq(NEW_ID, offsets.size());
	Wire* abstracted = ff.module->addWire(NEW_ID, offsets.size());
	SigSpec mux_input;
	int abstracted_idx = 0;
	for (int d_idx = 0; d_idx < ff.width; d_idx++) {
		if (offsets.count(d_idx)) {
			log_debug("bit %d: abstracted\n", d_idx);
			mux_input.append(port_sig[d_idx]);
			port_sig[d_idx].wire = abstracted;
			port_sig[d_idx].offset = abstracted_idx;
			log_assert(abstracted_idx < abstracted->width);
			abstracted_idx++;
		}
	}
	SigSpec mux_a, mux_b;
	if (enable.pol) {
		mux_a = mux_input;
		mux_b = anyseq;
	} else {
		mux_a = anyseq;
		mux_b = mux_input;
	}
	(void)ff.module->addMux(NEW_ID,
		mux_a,
		mux_b,
		enable.wire,
		abstracted);
	(void)ff.emit();
	return true;
}

pool<SigBit> gather_selected_reps(Module* mod, SigMap& sigmap) {
	pool<SigBit> selected_representatives;

	// Collect reps for all wire bits of selected wires
	for (auto wire : mod->selected_wires())
		for (auto bit : sigmap(wire))
			selected_representatives.insert(bit);

	// Collect reps for all output wire bits of selected cells
	for (auto cell : mod->selected_cells())
		for (auto conn : cell->connections())
			if (cell->output(conn.first))
				for (auto bit : conn.second.bits())
					selected_representatives.insert(sigmap(bit));
	return selected_representatives;
}

unsigned int abstract_state(Module* mod, EnableLogic enable) {
	CellTypes ct;
	ct.setup_internals_ff();
	SigMap sigmap(mod);
	pool<SigBit> selected_representatives = gather_selected_reps(mod, sigmap);

	unsigned int changed = 0;
	std::vector<FfData> ffs;
	// Abstract flop inputs if they're driving a selected output rep
	for (auto cell : mod->cells()) {
		if (!ct.cell_types.count(cell->type))
			continue;
		FfData ff(nullptr, cell);
		if (ff.has_sr)
			log_cmd_error("SR not supported\n");
		ffs.push_back(ff);
	}
	for (auto ff : ffs) {
		// A bit inefficient
		std::set<int> offsets_to_abstract;
		for (auto bit : ff.sig_q)
			if (selected_representatives.count(sigmap(bit)))
				offsets_to_abstract.insert(bit.offset);

		if (offsets_to_abstract.empty())
			continue;

		// Normalize to simpler FF
		ff.unmap_ce();
		ff.unmap_srst();
		if (ff.has_arst)
			ff.arst_to_aload();

		if (ff.has_aload)
			changed += abstract_state_port(ff, ff.sig_ad, offsets_to_abstract, enable);
		changed += abstract_state_port(ff, ff.sig_d, offsets_to_abstract, enable);
	}
	return changed;
}

bool abstract_value_port(Module* mod, Cell* cell, std::set<int> offsets, IdString port_name, EnableLogic enable) {
	auto anyseq = mod->Anyseq(NEW_ID, offsets.size());
	Wire* to_abstract = mod->addWire(NEW_ID, offsets.size());
	SigSpec mux_input;
	SigSpec mux_output;
	const SigSpec& old_port = cell->getPort(port_name);
	SigSpec new_port = old_port;
	int to_abstract_idx = 0;
	for (int port_idx = 0; port_idx < old_port.size(); port_idx++) {
		if (offsets.count(port_idx)) {
			log_debug("bit %d: abstracted\n", port_idx);
			mux_output.append(old_port[port_idx]);
			SigBit in_bit {to_abstract, to_abstract_idx};
			new_port.replace(port_idx, in_bit);
			mux_input.append(in_bit);
			log_assert(to_abstract_idx < to_abstract->width);
			to_abstract_idx++;
		}
	}
	cell->setPort(port_name, new_port);
	SigSpec mux_a, mux_b;
	if (enable.pol) {
		mux_a = mux_input;
		mux_b = anyseq;
	} else {
		mux_a = anyseq;
		mux_b = mux_input;
	}
	(void)mod->addMux(NEW_ID,
		mux_a,
		mux_b,
		enable.wire,
		mux_output);
	return true;
}

unsigned int abstract_value(Module* mod, EnableLogic enable) {
	SigMap sigmap(mod);
	pool<SigBit> selected_representatives = gather_selected_reps(mod, sigmap);
	unsigned int changed = 0;
	std::vector<Cell*> cells_snapshot = mod->cells();
	for (auto cell : cells_snapshot) {
		for (auto conn : cell->connections())
			if (cell->output(conn.first)) {
				std::set<int> offsets_to_abstract;
				for (int i = 0; i < conn.second.size(); i++) {
					if (selected_representatives.count(sigmap(conn.second[i]))) {
						offsets_to_abstract.insert(i);
					}
				}
				if (offsets_to_abstract.empty())
					continue;

				changed += abstract_value_port(mod, cell, offsets_to_abstract, conn.first, enable);
			}
	}
	return changed;
}

unsigned int abstract_init(Module* mod) {
	// AbstractPortCtx ctx {mod, SigMap(mod), {}};
	// collect_selected_ports(ctx);

	unsigned int changed = 0;

	// for (auto [cell, port] : ctx.outs) {
	// 	SigSpec sig = cell->getPort(port);
	// 	log_assert(sig.is_wire());
	// 	if (!sig.as_wire()->has_attribute(ID::init))
	// 		continue;

	// 	Const init = sig.as_wire()->attributes.at(ID::init);
	// 	sig.as_wire()->attributes.erase(ID::init);
	// 	changed += sig.size();
	// }
	log_cmd_error("Not implemented\n"); (void)mod;
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
			for (auto mod : design->selected_modules()) {
				log_debug("module %s\n", mod->name.c_str());
				Wire *enable_wire = mod->wire("\\" + enable_name);
				if (!enable_wire)
					log_cmd_error("Enable wire %s not found in module %s\n", enable_name.c_str(), mod->name.c_str());
				if (mode == State) {
					// for (auto cell : mod->selected_cells())
					// 	if (ct.cell_types.count(cell->type))
					changed += abstract_state(mod, {enable_wire, enable_pol});
				} else {
					changed += abstract_value(mod, {enable_wire, enable_pol});
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
	}
} AbstractPass;

PRIVATE_NAMESPACE_END
