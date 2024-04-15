/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


// Finds signal values with known constant or known unused values in the initial state
struct InitValWorker
{
	Module *module;

	ModWalker modwalker;
	SigMap &sigmap;
	FfInitVals initvals;

	dict<RTLIL::SigBit, RTLIL::State> initconst_bits;
	dict<RTLIL::SigBit, bool> used_bits;

	InitValWorker(Module *module) : module(module), modwalker(module->design), sigmap(modwalker.sigmap)
	{
		modwalker.setup(module);
		initvals.set(&modwalker.sigmap, module);

		for (auto wire : module->wires())
			if (wire->name.isPublic() || wire->get_bool_attribute(ID::keep))
				for (auto bit : SigSpec(wire))
					used_bits[sigmap(bit)] = true;
	}

	// Sign/Zero-extended indexing of individual port bits
	static SigBit bit_in_port(RTLIL::Cell *cell, RTLIL::IdString port, RTLIL::IdString sign, int index)
	{
		auto sig_port = cell->getPort(port);
		if (index < GetSize(sig_port))
			return sig_port[index];
		else if (cell->getParam(sign).as_bool())
			return GetSize(sig_port) > 0 ? sig_port[GetSize(sig_port) - 1] : State::Sx;
		else
			return State::S0;
	}

	// Has the signal a known constant value in the initial state?
	//
	// For sync-only FFs outputs, this is their initval. For logic loops,
	// multiple drivers or unknown cells this is Sx. For a small number of
	// handled cells we recurse through their inputs. All results are cached.
	RTLIL::State initconst(SigBit bit)
	{
		sigmap.apply(bit);

		if (!bit.is_wire())
			return bit.data;

		auto it = initconst_bits.find(bit);
		if (it != initconst_bits.end())
			return it->second;

		// Setting this temporarily to x takes care of any logic loops
		initconst_bits[bit] = State::Sx;

		pool<ModWalker::PortBit> portbits;
		modwalker.get_drivers(portbits, {bit});

		if (portbits.size() != 1)
			return State::Sx;

		ModWalker::PortBit portbit = *portbits.begin();
		RTLIL::Cell *cell = portbit.cell;

		if (RTLIL::builtin_ff_cell_types().count(cell->type))
		{
			FfData ff(&initvals, cell);

			if (ff.has_aload || ff.has_sr || ff.has_arst || (!ff.has_clk && !ff.has_gclk)) {
				for (auto bit_q : ff.sig_q) {
					initconst_bits[sigmap(bit_q)] = State::Sx;
				}
				return State::Sx;
			}

			for (int i = 0; i < ff.width; i++) {
				initconst_bits[sigmap(ff.sig_q[i])] = ff.val_init[i];
			}

			return ff.val_init[portbit.offset];
		}

		if (cell->type.in(ID($mux), ID($and), ID($or), ID($eq), ID($eqx), ID($initstate)))
		{
			if (cell->type == ID($mux))
			{
				SigBit sig_s = sigmap(cell->getPort(ID::S));
				State init_s = initconst(sig_s);
				State init_y;

				if (init_s == State::S0) {
					init_y = initconst(cell->getPort(ID::A)[portbit.offset]);
				} else if (init_s == State::S1) {
					init_y = initconst(cell->getPort(ID::B)[portbit.offset]);
				} else {
					State init_a = initconst(cell->getPort(ID::A)[portbit.offset]);
					State init_b = initconst(cell->getPort(ID::B)[portbit.offset]);
					init_y = init_a == init_b ? init_a : State::Sx;
				}
				initconst_bits[bit] = init_y;
				return init_y;
			}

			if (cell->type.in(ID($and), ID($or)))
			{
				State init_a = initconst(bit_in_port(cell, ID::A, ID::A_SIGNED, portbit.offset));
				State init_b = initconst(bit_in_port(cell, ID::B, ID::B_SIGNED, portbit.offset));
				State init_y;
				if (init_a == init_b)
					init_y = init_a;
				else if (cell->type == ID($and) && (init_a == State::S0 || init_b == State::S0))
					init_y = State::S0;
				else if (cell->type == ID($or) && (init_a == State::S1 || init_b == State::S1))
					init_y = State::S1;
				else
					init_y = State::Sx;

				initconst_bits[bit] = init_y;
				return init_y;
			}

			if (cell->type.in(ID($eq), ID($eqx))) // Treats $eqx as $eq
			{
				if (portbit.offset > 0) {
					initconst_bits[bit] = State::S0;
					return State::S0;
				}

				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_b = cell->getPort(ID::B);

				State init_y = State::S1;

				for (int i = 0; init_y != State::S0 && i < GetSize(sig_a); i++) {
					State init_ai = initconst(bit_in_port(cell, ID::A, ID::A_SIGNED, i));
					if (init_ai == State::Sx) {
						init_y = State::Sx;
						continue;
					}
					State init_bi = initconst(bit_in_port(cell, ID::B, ID::B_SIGNED, i));
					if (init_bi == State::Sx)
						init_y = State::Sx;
					else if (init_ai != init_bi)
						init_y = State::S0;
				}

				initconst_bits[bit] = init_y;
				return init_y;
			}

			if (cell->type == ID($initstate))
			{
				initconst_bits[bit] = State::S1;
				return State::S1;
			}

			log_assert(false);
		}

		return State::Sx;
	}

	RTLIL::Const initconst(SigSpec sig)
	{
		std::vector<RTLIL::State> bits;
		for (auto bit : sig)
			bits.push_back(initconst(bit));
		return bits;
	}

	// Is the initial value of this signal used?
	//
	// An initial value of a signal is considered as used if it a) aliases a
	// wire with a public name, an output wire or with a keep attribute b)
	// combinationally drives such a wire or c) drive an input to an unknown
	// cell.
	//
	// This recurses into driven cells for a small number of known handled
	// celltypes. Results are cached and initconst is used to detect unused
	// inputs for the handled celltypes.
	bool is_initval_used(SigBit bit)
	{
		if (!bit.is_wire())
			return false;

		auto it = used_bits.find(bit);
		if (it != used_bits.end())
			return it->second;

		used_bits[bit] = true; // Temporarily set to guard against logic loops

		pool<ModWalker::PortBit> portbits;
		modwalker.get_consumers(portbits, {bit});

		for (auto portbit : portbits) {
			RTLIL::Cell *cell = portbit.cell;
			if (!cell->type.in(ID($mux), ID($and), ID($or), ID($mem_v2)) && !RTLIL::builtin_ff_cell_types().count(cell->type)) {
				return true;
			}
		}

		for (auto portbit : portbits)
		{
			RTLIL::Cell *cell = portbit.cell;
			if (RTLIL::builtin_ff_cell_types().count(cell->type))
			{
				FfData ff(&initvals, cell);
				if (ff.has_aload || ff.has_sr || ff.has_arst || ff.has_gclk || !ff.has_clk)
					return true;
				if (ff.has_ce && initconst(ff.sig_ce.as_bit()) == (ff.pol_ce ? State::S0 : State::S1))
					continue;
				if (ff.has_srst && initconst(ff.sig_srst.as_bit()) == (ff.pol_srst ? State::S1 : State::S0))
					continue;

				return true;
			}
			else if (cell->type == ID($mux))
			{
				State init_s = initconst(cell->getPort(ID::S).as_bit());
				if (init_s == State::S0 && portbit.port == ID::B)
					continue;
				if (init_s == State::S1 && portbit.port == ID::A)
					continue;
				auto sig_y = cell->getPort(ID::Y);

				if (is_initval_used(sig_y[portbit.offset]))
					return true;
			}
			else if (cell->type.in(ID($and), ID($or)))
			{
				auto sig_a = cell->getPort(ID::A);
				auto sig_b = cell->getPort(ID::B);
				auto sig_y = cell->getPort(ID::Y);
				if (GetSize(sig_y) != GetSize(sig_a) || GetSize(sig_y) != GetSize(sig_b))
					return true; // TODO handle more of this
				State absorbing = cell->type == ID($and) ? State::S0 : State::S1;
				if (portbit.port == ID::A && initconst(sig_b[portbit.offset]) == absorbing)
					continue;
				if (portbit.port == ID::B && initconst(sig_a[portbit.offset]) == absorbing)
					continue;

				if (is_initval_used(sig_y[portbit.offset]))
					return true;
			}
			else if (cell->type == ID($mem_v2))
			{
				// TODO Use mem.h instead to uniformily cover all cases, most
				// likely requires processing all memories when initializing
				// the worker
				if (!portbit.port.in(ID::WR_DATA, ID::WR_ADDR, ID::RD_ADDR))
					return true;

				if (portbit.port == ID::WR_DATA)
				{
					if (initconst(cell->getPort(ID::WR_EN)[portbit.offset]) == State::S0)
						continue;
				}
				else if (portbit.port == ID::WR_ADDR)
				{
					int port = portbit.offset / cell->getParam(ID::ABITS).as_int();
					auto sig_en = cell->getPort(ID::WR_EN);
					int width = cell->getParam(ID::WIDTH).as_int();

					for (int i = port * width; i < (port + 1) * width; i++)
						if (initconst(sig_en[i]) != State::S0)
							return true;

					continue;
				}
				else if (portbit.port == ID::RD_ADDR)
				{
					int port = portbit.offset / cell->getParam(ID::ABITS).as_int();
					auto sig_en = cell->getPort(ID::RD_EN);

					if (initconst(sig_en[port]) != State::S0)
						return true;

					continue;
				}
				else
					return true;
			}
			else
				log_assert(false);
		}

		used_bits[bit] = false;
		return false;
	}
};

struct ReplacedPort {
	IdString name;
	int offset;
	bool clk_pol;
};

struct HierarchyWorker
{
	Design *design;
	pool<Module *> pending;

	dict<Module *, std::vector<ReplacedPort>> replaced_clk_inputs;

	HierarchyWorker(Design *design) :
		design(design)
	{
		for (auto module : design->modules())
			pending.insert(module);
	}

	void propagate();

	const std::vector<ReplacedPort> &find_replaced_clk_inputs(IdString cell_type);
};

// Propagates replaced clock signals
struct PropagateWorker
{
	HierarchyWorker &hierarchy;

	Module *module;
	SigMap sigmap;

	dict<SigBit, bool> replaced_clk_bits;
	dict<SigBit, SigBit> not_drivers;

	std::vector<ReplacedPort> replaced_clk_inputs;
	std::vector<std::pair<SigBit, bool>> pending;

	PropagateWorker(Module *module, HierarchyWorker &hierarchy) :
		hierarchy(hierarchy), module(module), sigmap(module)
	{
		hierarchy.pending.erase(module);

		for (auto wire : module->wires())
			if (wire->has_attribute(ID::replaced_by_gclk))
				replace_clk_bit(SigBit(wire), wire->attributes[ID::replaced_by_gclk].bits.at(0) == State::S1, false);

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($not), ID($_NOT_))) {
				auto sig_a = cell->getPort(ID::A);
				auto &sig_y = cell->getPort(ID::Y);
				sig_a.extend_u0(GetSize(sig_y), cell->hasParam(ID::A_SIGNED) && cell->parameters.at(ID::A_SIGNED).as_bool());

				for (int i = 0; i < GetSize(sig_a); i++)
					if (sig_a[i].is_wire())
						not_drivers.emplace(sigmap(sig_y[i]), sigmap(sig_a[i]));
			} else {
				for (auto &port_bit : hierarchy.find_replaced_clk_inputs(cell->type))
					replace_clk_bit(cell->getPort(port_bit.name)[port_bit.offset], port_bit.clk_pol, true);
			}
		}

		while (!pending.empty()) {
			auto current = pending.back();
			pending.pop_back();
			auto it = not_drivers.find(current.first);
			if (it == not_drivers.end())
				continue;

			replace_clk_bit(it->second, !current.second, true);
		}

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($not), ID($_NOT_)))
				continue;
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (SigBit bit : conn.second) {
					sigmap.apply(bit);
					if (replaced_clk_bits.count(bit))
						log_error("derived signal %s driven by %s (%s) from module %s is used as clock, derived clocks are only supported with clk2fflogic.\n",
								log_signal(bit), log_id(cell->name), log_id(cell->type), log_id(module));
				}
			}
		}

		for (auto port : module->ports) {
			auto wire = module->wire(port);
			if (!wire->port_input)
				continue;
			for (int i = 0; i < GetSize(wire); i++) {
				SigBit bit(wire, i);
				sigmap.apply(bit);
				auto it = replaced_clk_bits.find(bit);
				if (it == replaced_clk_bits.end())
					continue;
				replaced_clk_inputs.emplace_back(ReplacedPort {port, i, it->second});

				if (it->second) {
					bit = module->Not(NEW_ID, bit);
				}
			}
		}
	}

	void replace_clk_bit(SigBit bit, bool polarity, bool add_attribute)
	{
		sigmap.apply(bit);
		if (!bit.is_wire())
			log_error("XXX todo\n");

		auto it = replaced_clk_bits.find(bit);
		if (it != replaced_clk_bits.end()) {
			if (it->second != polarity)
				log_error("signal %s from module %s is used as clock with different polarities, run clk2fflogic instead.\n",
						log_signal(bit), log_id(module));
			return;
		}

		replaced_clk_bits.emplace(bit, polarity);

		if (add_attribute) {
			Wire *clk_wire = bit.wire;
			if (bit.offset != 0 || GetSize(bit.wire) != 1) {
				clk_wire = module->addWire(NEW_ID);
				module->connect(RTLIL::SigBit(clk_wire), bit);
			}
			clk_wire->attributes[ID::replaced_by_gclk] = polarity ? State::S1 : State::S0;
			clk_wire->set_bool_attribute(ID::keep);
		}

		pending.emplace_back(bit, polarity);
	}
};

const std::vector<ReplacedPort> &HierarchyWorker::find_replaced_clk_inputs(IdString cell_type)
{
	static const std::vector<ReplacedPort> empty;
	if (!cell_type.isPublic())
		return empty;

	Module *module = design->module(cell_type);
	if (module == nullptr)
		return empty;

	auto it = replaced_clk_inputs.find(module);
	if (it != replaced_clk_inputs.end())
		return it->second;

	if (pending.count(module)) {
		PropagateWorker worker(module, *this);
		return replaced_clk_inputs.emplace(module, std::move(worker.replaced_clk_inputs)).first->second;
	}

	return empty;
}


void HierarchyWorker::propagate()
{
	while (!pending.empty())
		PropagateWorker worker(pending.pop(), *this);
}

struct FormalFfPass : public Pass {
	FormalFfPass() : Pass("formalff", "prepare FFs for formal") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    formalff [options] [selection]\n");
		log("\n");
		log("This pass transforms clocked flip-flops to prepare a design for formal\n");
		log("verification. If a design contains latches and/or multiple different clocks run\n");
		log("the async2sync or clk2fflogic passes before using this pass.\n");
		log("\n");
		log("    -clk2ff\n");
		log("        Replace all clocked flip-flops with $ff cells that use the implicit\n");
		log("        global clock. This assumes, without checking, that the design uses a\n");
		log("        single global clock. If that is not the case, the clk2fflogic pass\n");
		log("        should be used instead.\n");
		log("\n");
		log("    -ff2anyinit\n");
		log("        Replace uninitialized bits of $ff cells with $anyinit cells. An\n");
		log("        $anyinit cell behaves exactly like an $ff cell with an undefined\n");
		log("        initialization value. The difference is that $anyinit inhibits\n");
		log("        don't-care optimizations and is used to track solver-provided values\n");
		log("        in witness traces.\n");
		log("\n");
		log("        If combined with -clk2ff this also affects newly created $ff cells.\n");
		log("\n");
		log("    -anyinit2ff\n");
		log("        Replaces $anyinit cells with uninitialized $ff cells. This performs the\n");
		log("        reverse of -ff2anyinit and can be used, before running a backend pass\n");
		log("        (or similar) that is not yet aware of $anyinit cells.\n");
		log("\n");
		log("        Note that after running -anyinit2ff, in general, performing don't-care\n");
		log("        optimizations is not sound in a formal verification setting.\n");
		log("\n");
		log("    -fine\n");
		log("        Emit fine-grained $_FF_ cells instead of coarse-grained $ff cells for\n");
		log("        -anyinit2ff. Cannot be combined with -clk2ff or -ff2anyinit.\n");
		log("\n");
		log("    -setundef\n");
		log("        Find FFs with undefined initialization values for which changing the\n");
		log("        initialization does not change the observable behavior and initialize\n");
		log("        them. For -ff2anyinit, this reduces the number of generated $anyinit\n");
		log("        cells that drive wires with private names.\n");
		log("\n");
		log("    -hierarchy\n");
		log("        Propagates the 'replaced_by_gclk' attribute set by clk2ff upwards\n");
		log("        through the design hierarchy towards the toplevel inputs. This option\n");
		log("        works on the whole design and ignores the selection.\n");
		log("\n");
		log("    -assume\n");
		log("        Add assumptions that constrain wires with the 'replaced_by_gclk'\n");
		log("        attribute to the value they would have before an active clock edge.\n");
		log("\n");

		// TODO: An option to check whether all FFs use the same clock before changing it to the global clock
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_clk2ff = false;
		bool flag_ff2anyinit = false;
		bool flag_anyinit2ff = false;
		bool flag_fine = false;
		bool flag_setundef = false;
		bool flag_hierarchy = false;
		bool flag_assume = false;

		log_header(design, "Executing FORMALFF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-clk2ff") {
				flag_clk2ff = true;
				continue;
			}
			if (args[argidx] == "-ff2anyinit") {
				flag_ff2anyinit = true;
				continue;
			}
			if (args[argidx] == "-anyinit2ff") {
				flag_anyinit2ff = true;
				continue;
			}
			if (args[argidx] == "-fine") {
				flag_fine = true;
				continue;
			}
			if (args[argidx] == "-setundef") {
				flag_setundef = true;
				continue;
			}
			if (args[argidx] == "-hierarchy") {
				flag_hierarchy = true;
				continue;
			}
			if (args[argidx] == "-assume") {
				flag_assume = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!(flag_clk2ff || flag_ff2anyinit || flag_anyinit2ff || flag_hierarchy || flag_assume))
			log_cmd_error("One of the options -clk2ff, -ff2anyinit, -anyinit2ff, -hierarchy or -assume must be specified.\n");

		if (flag_ff2anyinit && flag_anyinit2ff)
			log_cmd_error("The options -ff2anyinit and -anyinit2ff are exclusive.\n");

		if (flag_fine && !flag_anyinit2ff)
			log_cmd_error("The option -fine requries the -anyinit2ff option.\n");

		if (flag_fine && flag_clk2ff)
			log_cmd_error("The options -fine and -clk2ff are exclusive.\n");

		for (auto module : design->selected_modules())
		{
			if (flag_setundef)
			{
				InitValWorker worker(module);

				for (auto cell : module->selected_cells())
				{
					if (RTLIL::builtin_ff_cell_types().count(cell->type))
					{
						FfData ff(&worker.initvals, cell);
						if (ff.has_aload || ff.has_sr || ff.has_arst || ff.val_init.is_fully_def())
							continue;

						if (ff.has_ce && // CE can make the initval stick around
								worker.initconst(ff.sig_ce.as_bit()) != (ff.pol_ce ? State::S1 : State::S0) && // unless it's known active
								(!ff.has_srst || ff.ce_over_srst ||
									worker.initconst(ff.sig_srst.as_bit()) != (ff.pol_srst ? State::S1 : State::S0))) // or a srst with priority is known active
							continue;

						auto before = ff.val_init;
						for (int i = 0; i < ff.width; i++)
							if (ff.val_init[i] == State::Sx && !worker.is_initval_used(ff.sig_q[i]))
								ff.val_init[i] = State::S0;

						if (ff.val_init != before) {
							log("Setting unused undefined initial value of %s.%s (%s) from %s to %s\n",
									log_id(module), log_id(cell), log_id(cell->type),
									log_const(before), log_const(ff.val_init));
							worker.initvals.set_init(ff.sig_q, ff.val_init);
						}
					}
				}
			}
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);


			for (auto cell : module->selected_cells())
			{
				if (flag_anyinit2ff && cell->type == ID($anyinit))
				{
					FfData ff(&initvals, cell);
					ff.remove();
					ff.is_anyinit = false;
					ff.is_fine = flag_fine;
					if (flag_fine)
						for (int i = 0; i < ff.width; i++)
							ff.slice({i}).emit();
					else
						ff.emit();

					continue;
				}

				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);
				bool emit = false;

				if (flag_clk2ff && ff.has_clk) {
					if (ff.sig_clk.is_fully_const())
						log_error("Const CLK on %s (%s) from module %s, run async2sync first.\n",
								log_id(cell), log_id(cell->type), log_id(module));
					if (ff.has_aload || ff.has_arst || ff.has_sr)
						log_error("Async inputs on %s (%s) from module %s, run async2sync first.\n",
								log_id(cell), log_id(cell->type), log_id(module));

					auto clk_wire = ff.sig_clk.is_wire() ? ff.sig_clk.as_wire() : nullptr;

					if (clk_wire == nullptr) {
						clk_wire = module->addWire(NEW_ID);
						module->connect(RTLIL::SigBit(clk_wire), ff.sig_clk);
					}

					auto clk_polarity = ff.pol_clk ? State::S1 : State::S0;

					std::string attribute = clk_wire->get_string_attribute(ID::replaced_by_gclk);

					auto &attr = clk_wire->attributes[ID::replaced_by_gclk];

					if (!attr.empty() && attr != clk_polarity)
						log_error("CLK %s on %s (%s) from module %s also used with opposite polarity, run clk2fflogic instead.\n",
								log_id(clk_wire), log_id(cell), log_id(cell->type), log_id(module));

					attr = clk_polarity;
					clk_wire->set_bool_attribute(ID::keep);

					// TODO propagate the replaced_by_gclk attribute upwards throughout the hierarchy

					ff.unmap_ce_srst();
					ff.has_clk = false;
					ff.has_gclk = true;
					emit = true;
				}

				if (!ff.has_gclk) {
					continue;
				}

				if (flag_ff2anyinit && !ff.val_init.is_fully_def())
				{
					ff.remove();
					emit = false;

					int cursor = 0;
					while (cursor < ff.val_init.size())
					{
						bool is_anyinit = ff.val_init[cursor] == State::Sx;
						std::vector<int> bits;
						bits.push_back(cursor++);
						while (cursor < ff.val_init.size() && (ff.val_init[cursor] == State::Sx) == is_anyinit)
							bits.push_back(cursor++);

						if ((int)bits.size() == ff.val_init.size()) {
							// This check is only to make the private names more helpful for debugging
							ff.is_anyinit = true;
							ff.is_fine = false;
							emit = true;
							break;
						}

						auto slice = ff.slice(bits);
						slice.is_anyinit = is_anyinit;
						slice.is_fine = false;
						slice.emit();
					}
				}

				if (emit)
					ff.emit();
			}
		}

		if (flag_hierarchy) {
			HierarchyWorker worker(design);
			worker.propagate();
		}

		if (flag_assume) {
			for (auto module : design->selected_modules()) {
				std::vector<pair<SigBit, bool>> found;
				for (auto wire : module->wires()) {
					if (!wire->has_attribute(ID::replaced_by_gclk))
						continue;
					bool clk_pol = wire->attributes[ID::replaced_by_gclk].bits.at(0) == State::S1;

					found.emplace_back(SigSpec(wire), clk_pol);
				}
				for (auto pair : found) {
					SigBit clk = pair.first;

					if (pair.second)
						clk = module->Not(NEW_ID, clk);

					module->addAssume(NEW_ID, clk, State::S1);

				}
			}
		}
	}
} FormalFfPass;

PRIVATE_NAMESPACE_END
