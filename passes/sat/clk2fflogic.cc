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
	}
	SigSpec wrap_async_control(Module *module, SigSpec sig, bool polarity, bool is_fine, IdString past_sig_id) {
		if (!is_fine)
			return wrap_async_control(module, sig, polarity, past_sig_id);
		return wrap_async_control_gate(module, sig, polarity, past_sig_id);
	}
	SigSpec wrap_async_control(Module *module, SigSpec sig, bool polarity, IdString past_sig_id) {
		Wire *past_sig = module->addWire(past_sig_id, GetSize(sig));
		past_sig->attributes[ID::init] = RTLIL::Const(polarity ? State::S0 : State::S1, GetSize(sig));
		module->addFf(NEW_ID, sig, past_sig);
		if (polarity)
			sig = module->Or(NEW_ID, sig, past_sig);
		else
			sig = module->And(NEW_ID, sig, past_sig);
		if (polarity)
			return sig;
		else
			return module->Not(NEW_ID, sig);
	}
	SigSpec wrap_async_control_gate(Module *module, SigSpec sig, bool polarity, IdString past_sig_id) {
		Wire *past_sig = module->addWire(past_sig_id);
		past_sig->attributes[ID::init] = polarity ? State::S0 : State::S1;
		module->addFfGate(NEW_ID, sig, past_sig);
		if (polarity)
			sig = module->OrGate(NEW_ID, sig, past_sig);
		else
			sig = module->AndGate(NEW_ID, sig, past_sig);
		if (polarity)
			return sig;
		else
			return module->NotGate(NEW_ID, sig);
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		// bool flag_noinit = false;

		log_header(design, "Executing CLK2FFLOGIC pass (convert clocked FFs to generic $ff cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-noinit") {
			// 	flag_noinit = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

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

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				SigSpec qval;
				if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
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

					// Strip spaces from signal name, since Yosys IDs can't contain spaces
					// Spaces only occur when we have a signal that's a slice of a larger bus,
					// e.g. "\myreg [5:0]", so removing spaces shouldn't result in loss of uniqueness
					std::string sig_q_str = log_signal(ff.sig_q);
					sig_q_str.erase(std::remove(sig_q_str.begin(), sig_q_str.end(), ' '), sig_q_str.end());

					Wire *past_q = module->addWire(NEW_ID_SUFFIX(stringf("%s#past_q_wire", sig_q_str.c_str())), ff.width);
          
					if (!ff.is_fine) {
						module->addFf(NEW_ID, ff.sig_q, past_q);
					} else {
						module->addFfGate(NEW_ID, ff.sig_q, past_q);
					}
					if (!ff.val_init.is_fully_undef())
						initvals.set_init(past_q, ff.val_init);

					if (ff.has_clk) {
						ff.unmap_ce_srst();

						Wire *past_clk = module->addWire(NEW_ID_SUFFIX(stringf("%s#past_clk#%s", sig_q_str.c_str(), log_signal(ff.sig_clk))));
						initvals.set_init(past_clk, ff.pol_clk ? State::S1 : State::S0);

						if (!ff.is_fine)
							module->addFf(NEW_ID, ff.sig_clk, past_clk);
						else
							module->addFfGate(NEW_ID, ff.sig_clk, past_clk);

						SigSpec clock_edge_pattern;

						if (ff.pol_clk) {
							clock_edge_pattern.append(State::S0);
							clock_edge_pattern.append(State::S1);
						} else {
							clock_edge_pattern.append(State::S1);
							clock_edge_pattern.append(State::S0);
						}

						SigSpec clock_edge = module->Eqx(NEW_ID, {ff.sig_clk, SigSpec(past_clk)}, clock_edge_pattern);

						Wire *past_d = module->addWire(NEW_ID_SUFFIX(stringf("%s#past_d_wire", sig_q_str.c_str())), ff.width);
						if (!ff.is_fine)
							module->addFf(NEW_ID, ff.sig_d, past_d);
						else
							module->addFfGate(NEW_ID, ff.sig_d, past_d);

						if (!ff.val_init.is_fully_undef())
							initvals.set_init(past_d, ff.val_init);

						if (!ff.is_fine)
							qval = module->Mux(NEW_ID, past_q, past_d, clock_edge);
						else
							qval = module->MuxGate(NEW_ID, past_q, past_d, clock_edge);
					} else {
						qval = past_q;
					}

					// The check for a constant sig_aload is also done by opt_dff, but when using verific and running
					// clk2fflogic before opt_dff (which does more and possibly unwanted optimizations) this check avoids
					// generating a lot of extra logic.
					if (ff.has_aload && ff.sig_aload != (ff.pol_aload ? State::S0 : State::S1)) {
						SigSpec sig_aload = wrap_async_control(module, ff.sig_aload, ff.pol_aload, ff.is_fine, NEW_ID);

						if (!ff.is_fine)
							qval = module->Mux(NEW_ID, qval, ff.sig_ad, sig_aload);
						else
							qval = module->MuxGate(NEW_ID, qval, ff.sig_ad, sig_aload);
					}

					if (ff.has_sr) {
						SigSpec setval = wrap_async_control(module, ff.sig_set, ff.pol_set, ff.is_fine, NEW_ID);
						SigSpec clrval = wrap_async_control(module, ff.sig_clr, ff.pol_clr, ff.is_fine, NEW_ID);
						if (!ff.is_fine) {
							clrval = module->Not(NEW_ID, clrval);
							qval = module->Or(NEW_ID, qval, setval);
							module->addAnd(NEW_ID, qval, clrval, ff.sig_q);
						} else {
							clrval = module->NotGate(NEW_ID, clrval);
							qval = module->OrGate(NEW_ID, qval, setval);
							module->addAndGate(NEW_ID, qval, clrval, ff.sig_q);
						}
					} else if (ff.has_arst) {
						IdString id = NEW_ID_SUFFIX(stringf("%s#past_arst#%s", sig_q_str.c_str(), log_signal(ff.sig_arst)));
						SigSpec arst = wrap_async_control(module, ff.sig_arst, ff.pol_arst, ff.is_fine, id);
						if (!ff.is_fine)
							module->addMux(NEW_ID, qval, ff.val_arst, arst, ff.sig_q);
						else
							module->addMuxGate(NEW_ID, qval, ff.val_arst[0], arst, ff.sig_q);
					} else {
						module->connect(ff.sig_q, qval);
					}
				}
			}
		}

	}
} Clk2fflogicPass;

PRIVATE_NAMESPACE_END
