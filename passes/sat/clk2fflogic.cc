/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
	SigSpec wrap_async_control(Module *module, SigSpec sig, bool polarity) {
		Wire *past_sig = module->addWire(NEW_ID, GetSize(sig));
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
	SigSpec wrap_async_control_gate(Module *module, SigSpec sig, bool polarity) {
		Wire *past_sig = module->addWire(NEW_ID);
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

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (cell->type.in(ID($mem)))
				{
					int abits = cell->getParam(ID::ABITS).as_int();
					int width = cell->getParam(ID::WIDTH).as_int();
					int rd_ports = cell->getParam(ID::RD_PORTS).as_int();
					int wr_ports = cell->getParam(ID::WR_PORTS).as_int();

					for (int i = 0; i < rd_ports; i++) {
						if (cell->getParam(ID::RD_CLK_ENABLE).extract(i).as_bool())
							log_error("Read port %d of memory %s.%s is clocked. This is not supported by \"clk2fflogic\"! "
									"Call \"memory\" with -nordff to avoid this error.\n", i, log_id(cell), log_id(module));
					}

					Const wr_clk_en_param = cell->getParam(ID::WR_CLK_ENABLE);
					Const wr_clk_pol_param = cell->getParam(ID::WR_CLK_POLARITY);

					SigSpec wr_clk_port = cell->getPort(ID::WR_CLK);
					SigSpec wr_en_port = cell->getPort(ID::WR_EN);
					SigSpec wr_addr_port = cell->getPort(ID::WR_ADDR);
					SigSpec wr_data_port = cell->getPort(ID::WR_DATA);

					for (int wport = 0; wport < wr_ports; wport++)
					{
						bool clken = wr_clk_en_param[wport] == State::S1;
						bool clkpol = wr_clk_pol_param[wport] == State::S1;

						if (!clken)
							continue;

						SigBit clk = wr_clk_port[wport];
						SigSpec en = wr_en_port.extract(wport*width, width);
						SigSpec addr = wr_addr_port.extract(wport*abits, abits);
						SigSpec data = wr_data_port.extract(wport*width, width);

						log("Modifying write port %d on memory %s.%s: CLK=%s, A=%s, D=%s\n",
								wport, log_id(module), log_id(cell), log_signal(clk),
								log_signal(addr), log_signal(data));

						Wire *past_clk = module->addWire(NEW_ID);
						past_clk->attributes[ID::init] = clkpol ? State::S1 : State::S0;
						module->addFf(NEW_ID, clk, past_clk);

						SigSpec clock_edge_pattern;

						if (clkpol) {
							clock_edge_pattern.append(State::S0);
							clock_edge_pattern.append(State::S1);
						} else {
							clock_edge_pattern.append(State::S1);
							clock_edge_pattern.append(State::S0);
						}

						SigSpec clock_edge = module->Eqx(NEW_ID, {clk, SigSpec(past_clk)}, clock_edge_pattern);

						SigSpec en_q = module->addWire(NEW_ID, GetSize(en));
						module->addFf(NEW_ID, en, en_q);

						SigSpec addr_q = module->addWire(NEW_ID, GetSize(addr));
						module->addFf(NEW_ID, addr, addr_q);

						SigSpec data_q = module->addWire(NEW_ID, GetSize(data));
						module->addFf(NEW_ID, data, data_q);

						wr_clk_port[wport] = State::S0;
						wr_en_port.replace(wport*width, module->Mux(NEW_ID, Const(0, GetSize(en_q)), en_q, clock_edge));
						wr_addr_port.replace(wport*abits, addr_q);
						wr_data_port.replace(wport*width, data_q);

						wr_clk_en_param[wport] = State::S0;
						wr_clk_pol_param[wport] = State::S0;
					}

					cell->setParam(ID::WR_CLK_ENABLE, wr_clk_en_param);
					cell->setParam(ID::WR_CLK_POLARITY, wr_clk_pol_param);

					cell->setPort(ID::WR_CLK, wr_clk_port);
					cell->setPort(ID::WR_EN, wr_en_port);
					cell->setPort(ID::WR_ADDR, wr_addr_port);
					cell->setPort(ID::WR_DATA, wr_data_port);
				}

				SigSpec qval;
				if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
					FfData ff(&initvals, cell);

					if (ff.has_d && !ff.has_clk && !ff.has_en) {
						// Already a $ff or $_FF_ cell.
						continue;
					}

					Wire *past_q = module->addWire(NEW_ID, ff.width);
					if (!ff.is_fine) {
						module->addFf(NEW_ID, ff.sig_q, past_q);
					} else {
						module->addFfGate(NEW_ID, ff.sig_q, past_q);
					}
					if (!ff.val_init.is_fully_undef())
						initvals.set_init(past_q, ff.val_init);

					if (ff.has_clk) {
						ff.unmap_ce_srst(module);

						Wire *past_clk = module->addWire(NEW_ID);
						initvals.set_init(past_clk, ff.pol_clk ? State::S1 : State::S0);

						if (!ff.is_fine)
							module->addFf(NEW_ID, ff.sig_clk, past_clk);
						else
							module->addFfGate(NEW_ID, ff.sig_clk, past_clk);

						log("Replacing %s.%s (%s): CLK=%s, D=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_clk), log_signal(ff.sig_d), log_signal(ff.sig_q));

						SigSpec clock_edge_pattern;

						if (ff.pol_clk) {
							clock_edge_pattern.append(State::S0);
							clock_edge_pattern.append(State::S1);
						} else {
							clock_edge_pattern.append(State::S1);
							clock_edge_pattern.append(State::S0);
						}

						SigSpec clock_edge = module->Eqx(NEW_ID, {ff.sig_clk, SigSpec(past_clk)}, clock_edge_pattern);

						Wire *past_d = module->addWire(NEW_ID, ff.width);
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
					} else if (ff.has_d) {

						log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_en), log_signal(ff.sig_d), log_signal(ff.sig_q));

						SigSpec sig_en = wrap_async_control(module, ff.sig_en, ff.pol_en);

						if (!ff.is_fine)
							qval = module->Mux(NEW_ID, past_q, ff.sig_d, sig_en);
						else
							qval = module->MuxGate(NEW_ID, past_q, ff.sig_d, sig_en);
					} else {

						log("Replacing %s.%s (%s): SET=%s, CLR=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_set), log_signal(ff.sig_clr), log_signal(ff.sig_q));

						qval = past_q;
					}

					if (ff.has_sr) {
						SigSpec setval = wrap_async_control(module, ff.sig_set, ff.pol_set);
						SigSpec clrval = wrap_async_control(module, ff.sig_clr, ff.pol_clr);
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
						SigSpec arst = wrap_async_control(module, ff.sig_arst, ff.pol_arst);
						if (!ff.is_fine)
							module->addMux(NEW_ID, qval, ff.val_arst, arst, ff.sig_q);
						else
							module->addMuxGate(NEW_ID, qval, ff.val_arst[0], arst, ff.sig_q);
					} else {
						module->connect(ff.sig_q, qval);
					}

					initvals.remove_init(ff.sig_q);
					module->remove(cell);
					continue;
				}
			}
		}

	}
} Clk2fflogicPass;

PRIVATE_NAMESPACE_END
