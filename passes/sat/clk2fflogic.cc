/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SampledSig {
	SigSpec sampled, current;
	SigSpec &operator[](bool get_current) { return get_current ? current : sampled; }
};

struct Clk2fflogicPass : public Pass {
	Clk2fflogicPass() : Pass("clk2fflogic", "convert clocked FFs to generic $ff cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clk2fflogic [options] [selection]\n");
		log("\n");
		log("This command replaces clocked flip-flops with generic $ff cells that use the\n");
		log("implicit global clock. This is useful for formal verification of designs with\n");
		log("multiple clocks.\n");
		log("\n");
		log("This pass assumes negative hold time for the async FF inputs. For example when\n");
		log("a reset deasserts with the clock edge, then the FF output will still drive the\n");
		log("reset value in the next cycle regardless of the data-in value at the time of\n");
		log("the clock edge.\n");
		log("\n");
		log("    -nolower\n");
		log("        Do not automatically run 'chformal -lower' to lower $check cells.\n");
		log("\n");
	}
	// Active-high sampled and current value of a level-triggered control signal. Initial sampled values is low/non-asserted.
	SampledSig sample_control(Module *module, SigSpec sig, bool polarity, bool is_fine) {
		if (!polarity) {
			if (is_fine)
				sig = module->NotGate(NEW_ID, sig);
			else
				sig = module->Not(NEW_ID, sig);
		}
		std::string sig_str = log_signal(sig);
		sig_str.erase(std::remove(sig_str.begin(), sig_str.end(), ' '), sig_str.end());
		Wire *sampled_sig = module->addWire(NEW_ID_SUFFIX(stringf("%s#sampled", sig_str.c_str())), GetSize(sig));
		sampled_sig->attributes[ID::init] = RTLIL::Const(State::S0, GetSize(sig));
		if (is_fine)
			module->addFfGate(NEW_ID, sig, sampled_sig);
		else
			module->addFf(NEW_ID, sig, sampled_sig);
		return {sampled_sig, sig};
	}
	// Active-high trigger signal for an edge-triggered control signal. Initial values is low/non-edge.
	SigSpec sample_control_edge(Module *module, SigSpec sig, bool polarity, bool is_fine) {
		std::string sig_str = log_signal(sig);
		sig_str.erase(std::remove(sig_str.begin(), sig_str.end(), ' '), sig_str.end());
		Wire *sampled_sig = module->addWire(NEW_ID_SUFFIX(stringf("%s#sampled", sig_str.c_str())), GetSize(sig));
		sampled_sig->attributes[ID::init] = RTLIL::Const(polarity ? State::S1 : State::S0, GetSize(sig));
		if (is_fine)
			module->addFfGate(NEW_ID, sig, sampled_sig);
		else
			module->addFf(NEW_ID, sig, sampled_sig);
		return module->Eqx(NEW_ID, {sampled_sig, sig}, polarity ? SigSpec {State::S0, State::S1} : SigSpec {State::S1, State::S0});
	}
	// Sampled and current value of a data signal.
	SampledSig sample_data(Module *module, SigSpec sig, RTLIL::Const init, bool is_fine, bool set_attribute = false) {
		std::string sig_str = log_signal(sig);
		sig_str.erase(std::remove(sig_str.begin(), sig_str.end(), ' '), sig_str.end());


		Wire *sampled_sig = module->addWire(NEW_ID_SUFFIX(stringf("%s#sampled", sig_str.c_str())), GetSize(sig));
		sampled_sig->attributes[ID::init] = init;

		Cell *cell;
		if (is_fine)
			cell = module->addFfGate(NEW_ID, sig, sampled_sig);
		else
			cell = module->addFf(NEW_ID, sig, sampled_sig);

		if (set_attribute) {
			for (auto &chunk : sig.chunks())
				if (chunk.wire != nullptr)
					chunk.wire->set_bool_attribute(ID::keep);
			cell->set_bool_attribute(ID(clk2fflogic));
		}

		return {sampled_sig, sig};
	}
	SigSpec mux(Module *module, SigSpec a, SigSpec b, SigSpec s, bool is_fine) {
		if (is_fine)
			return module->MuxGate(NEW_ID, a, b, s);
		else
			return module->Mux(NEW_ID, a, b, s);
	}
	SigSpec bitwise_sr(Module *module, SigSpec a, SigSpec s, SigSpec r, bool is_fine) {
		if (is_fine)
			return module->AndGate(NEW_ID, module->OrGate(NEW_ID, a, s), module->NotGate(NEW_ID, r));
		else
			return module->And(NEW_ID, module->Or(NEW_ID, a, s), module->Not(NEW_ID, r));
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_nolower = false;

		log_header(design, "Executing CLK2FFLOGIC pass (convert clocked FFs to generic $ff cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-nolower") {
				flag_nolower = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		bool have_check_cells = false;

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);

			for (auto &mem : Mem::get_selected_memories(module))
			{
				for (int i = 0; i < GetSize(mem.rd_ports); i++) {
					auto &port = mem.rd_ports[i];
					if (port.clk_enable)
						log_error("Read port %d of memory %s.%s is clocked. This is not supported by \"clk2fflogic\"! "
								"Call \"memory\" with -nordff to avoid this error.\n", i, log_id(mem.memid), log_id(module));
				}

				for (int i = 0; i < GetSize(mem.wr_ports); i++)
				{
					auto &port = mem.wr_ports[i];

					if (!port.clk_enable)
						continue;

					log("Modifying write port %d on memory %s.%s: CLK=%s, A=%s, D=%s\n",
							i, log_id(module), log_id(mem.memid), log_signal(port.clk),
							log_signal(port.addr), log_signal(port.data));

					Wire *past_clk = module->addWire(NEW_ID_SUFFIX(stringf("%s#%d#past_clk#%s", log_id(mem.memid), i, log_signal(port.clk))));
					past_clk->attributes[ID::init] = port.clk_polarity ? State::S1 : State::S0;
					module->addFf(NEW_ID, port.clk, past_clk);

					SigSpec clock_edge_pattern;

					if (port.clk_polarity) {
						clock_edge_pattern.append(State::S0);
						clock_edge_pattern.append(State::S1);
					} else {
						clock_edge_pattern.append(State::S1);
						clock_edge_pattern.append(State::S0);
					}

					SigSpec clock_edge = module->Eqx(NEW_ID, {port.clk, SigSpec(past_clk)}, clock_edge_pattern);

					SigSpec en_q = module->addWire(NEW_ID_SUFFIX(stringf("%s#%d#en_q", log_id(mem.memid), i)), GetSize(port.en));
					module->addFf(NEW_ID, port.en, en_q);

					SigSpec addr_q = module->addWire(NEW_ID_SUFFIX(stringf("%s#%d#addr_q", log_id(mem.memid), i)), GetSize(port.addr));
					module->addFf(NEW_ID, port.addr, addr_q);

					SigSpec data_q = module->addWire(NEW_ID_SUFFIX(stringf("%s#%d#data_q", log_id(mem.memid), i)), GetSize(port.data));
					module->addFf(NEW_ID, port.data, data_q);

					port.clk = State::S0;
					port.en = module->Mux(NEW_ID, Const(0, GetSize(en_q)), en_q, clock_edge);
					port.addr = addr_q;
					port.data = data_q;

					port.clk_enable = false;
					port.clk_polarity = false;
				}

				mem.emit();
			}

			SigBit initstate;

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (cell->type.in(ID($print), ID($check)))
				{
					if (cell->type == ID($check))
						have_check_cells = true;

					bool trg_enable = cell->getParam(ID(TRG_ENABLE)).as_bool();
					if (!trg_enable)
						continue;

					int trg_width = cell->getParam(ID(TRG_WIDTH)).as_int();

					if (trg_width == 0) {
						if (initstate == State::S0)
							initstate = module->Initstate(NEW_ID);

						SigBit sig_en = cell->getPort(ID::EN);
						cell->setPort(ID::EN, module->And(NEW_ID, sig_en, initstate));
					} else {
						SigBit sig_en = cell->getPort(ID::EN);
						SigSpec sig_args = cell->getPort(ID::ARGS);
						Const trg_polarity = cell->getParam(ID(TRG_POLARITY));
						SigSpec sig_trg = cell->getPort(ID::TRG);

						SigSpec sig_trg_sampled;

						for (auto const &bit : sig_trg)
							sig_trg_sampled.append(sample_control_edge(module, bit, trg_polarity[GetSize(sig_trg_sampled)] == State::S1, false));
						SigSpec sig_args_sampled = sample_data(module, sig_args, Const(State::S0, GetSize(sig_args)), false, false).sampled;
						SigBit sig_en_sampled = sample_data(module, sig_en, State::S0, false, false).sampled;

						SigBit sig_trg_combined = module->ReduceOr(NEW_ID, sig_trg_sampled);

						cell->setPort(ID::EN, module->And(NEW_ID, sig_en_sampled, sig_trg_combined));
						cell->setPort(ID::ARGS, sig_args_sampled);
						if (cell->type == ID($check)) {
							SigBit sig_a = cell->getPort(ID::A);
							SigBit sig_a_sampled = sample_data(module, sig_a, State::S1, false, false).sampled;
							cell->setPort(ID::A, sig_a_sampled);
						}
					}

					cell->setPort(ID::TRG, SigSpec());

					cell->setParam(ID::TRG_ENABLE, false);
					cell->setParam(ID::TRG_WIDTH, 0);
					cell->setParam(ID::TRG_POLARITY, false);
					cell->set_bool_attribute(ID(trg_on_gclk));

					continue;
				}

				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);

				if (ff.has_gclk) {
					// Already a $ff or $_FF_ cell.
					continue;
				}

				if (ff.has_clk) {
					log("Replacing %s.%s (%s): CLK=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(ff.sig_clk), log_signal(ff.sig_d), log_signal(ff.sig_q));
				} else if (ff.has_aload) {
					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(ff.sig_aload), log_signal(ff.sig_ad), log_signal(ff.sig_q));
				} else {
					// $sr.
					log("Replacing %s.%s (%s): SET=%s, CLR=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(ff.sig_set), log_signal(ff.sig_clr), log_signal(ff.sig_q));
				}

				ff.remove();

				if (ff.has_clk)
					ff.unmap_ce_srst();

				auto next_q = sample_data(module, ff.sig_q, ff.val_init, ff.is_fine, true).sampled;

				if (ff.has_clk) {
					// The init value for the sampled d is never used, so we can set it to fixed zero, reducing uninit'd FFs
					auto sampled_d = sample_data(module, ff.sig_d, RTLIL::Const(State::S0, ff.width), ff.is_fine);
					auto clk_edge = sample_control_edge(module, ff.sig_clk, ff.pol_clk, ff.is_fine);
					next_q = mux(module, next_q, sampled_d.sampled, clk_edge, ff.is_fine);
				}

				SampledSig sampled_aload, sampled_ad, sampled_set, sampled_clr, sampled_arst;
				// The check for a constant sig_aload is also done by opt_dff, but when using verific and running
				// clk2fflogic before opt_dff (which does more and possibly unwanted optimizations) this check avoids
				// generating a lot of extra logic.
				bool has_nonconst_aload = ff.has_aload && ff.sig_aload != (ff.pol_aload ? State::S0 : State::S1);
				if (has_nonconst_aload) {
					sampled_aload = sample_control(module, ff.sig_aload, ff.pol_aload, ff.is_fine);
					// The init value for the sampled ad is never used, so we can set it to fixed zero, reducing uninit'd FFs
					sampled_ad = sample_data(module, ff.sig_ad, RTLIL::Const(State::S0, ff.width), ff.is_fine);
				}
				if (ff.has_sr) {
					sampled_set = sample_control(module, ff.sig_set, ff.pol_set, ff.is_fine);
					sampled_clr = sample_control(module, ff.sig_clr, ff.pol_clr, ff.is_fine);
				}
				if (ff.has_arst)
					sampled_arst = sample_control(module, ff.sig_arst, ff.pol_arst, ff.is_fine);

				// First perform updates using _only_ sampled values, then again using _only_ current values. Unlike the previous
				// implementation, this approach correctly handles all the cases of multiple signals changing simultaneously.
				for (int current = 0; current < 2; current++) {
					if (has_nonconst_aload)
						next_q = mux(module, next_q, sampled_ad[current], sampled_aload[current], ff.is_fine);
					if (ff.has_sr)
						next_q = bitwise_sr(module, next_q, sampled_set[current], sampled_clr[current], ff.is_fine);
					if (ff.has_arst)
						next_q = mux(module, next_q, ff.val_arst, sampled_arst[current], ff.is_fine);
				}

				module->connect(ff.sig_q, next_q);

			}
		}

		if (have_check_cells && !flag_nolower) {
			log_push();
			Pass::call(design, "chformal -lower");
			log_pop();
		}
	}
} Clk2fflogicPass;

PRIVATE_NAMESPACE_END
