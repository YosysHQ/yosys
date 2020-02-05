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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Clk2fflogicPass : public Pass {
	Clk2fflogicPass() : Pass("clk2fflogic", "convert clocked FFs to generic $ff cells") { }
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			dict<SigBit, State> initbits;
			pool<SigBit> del_initbits;

			for (auto wire : module->wires())
				if (wire->attributes.count("\\init") > 0)
				{
					Const initval = wire->attributes.at("\\init");
					SigSpec initsig = sigmap(wire);

					for (int i = 0; i < GetSize(initval) && i < GetSize(initsig); i++)
						if (initval[i] == State::S0 || initval[i] == State::S1)
							initbits[initsig[i]] = initval[i];
				}

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (cell->type.in("$mem"))
				{
					int abits = cell->getParam("\\ABITS").as_int();
					int width = cell->getParam("\\WIDTH").as_int();
					int rd_ports = cell->getParam("\\RD_PORTS").as_int();
					int wr_ports = cell->getParam("\\WR_PORTS").as_int();

					for (int i = 0; i < rd_ports; i++) {
						if (cell->getParam("\\RD_CLK_ENABLE").extract(i).as_bool())
							log_error("Read port %d of memory %s.%s is clocked. This is not supported by \"clk2fflogic\"! "
									"Call \"memory\" with -nordff to avoid this error.\n", i, log_id(cell), log_id(module));
					}

					Const wr_clk_en_param = cell->getParam("\\WR_CLK_ENABLE");
					Const wr_clk_pol_param = cell->getParam("\\WR_CLK_POLARITY");

					SigSpec wr_clk_port = cell->getPort("\\WR_CLK");
					SigSpec wr_en_port = cell->getPort("\\WR_EN");
					SigSpec wr_addr_port = cell->getPort("\\WR_ADDR");
					SigSpec wr_data_port = cell->getPort("\\WR_DATA");

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
						past_clk->attributes["\\init"] = clkpol ? State::S1 : State::S0;
						module->addFf(NEW_ID, clk, past_clk);

						SigSpec clock_edge_pattern;

						if (clkpol) {
							clock_edge_pattern.append_bit(State::S0);
							clock_edge_pattern.append_bit(State::S1);
						} else {
							clock_edge_pattern.append_bit(State::S1);
							clock_edge_pattern.append_bit(State::S0);
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

					cell->setParam("\\WR_CLK_ENABLE", wr_clk_en_param);
					cell->setParam("\\WR_CLK_POLARITY", wr_clk_pol_param);

					cell->setPort("\\WR_CLK", wr_clk_port);
					cell->setPort("\\WR_EN", wr_en_port);
					cell->setPort("\\WR_ADDR", wr_addr_port);
					cell->setPort("\\WR_DATA", wr_data_port);
				}

				if (cell->type.in("$dlatch", "$dlatchsr"))
				{
					bool enpol = cell->parameters["\\EN_POLARITY"].as_bool();

					SigSpec sig_en = cell->getPort("\\EN");
					SigSpec sig_d = cell->getPort("\\D");
					SigSpec sig_q = cell->getPort("\\Q");

					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_en), log_signal(sig_d), log_signal(sig_q));

					Wire *past_q = module->addWire(NEW_ID, GetSize(sig_q));
					module->addFf(NEW_ID, sig_q, past_q);

					if (cell->type == "$dlatch")
					{
						if (enpol)
							module->addMux(NEW_ID, past_q, sig_d, sig_en, sig_q);
						else
							module->addMux(NEW_ID, sig_d, past_q, sig_en, sig_q);
					}
					else
					{
						SigSpec t;
						if (enpol)
							t = module->Mux(NEW_ID, past_q, sig_d, sig_en);
						else
							t = module->Mux(NEW_ID, sig_d, past_q, sig_en);

						SigSpec s = cell->getPort("\\SET");
						if (!cell->parameters["\\SET_POLARITY"].as_bool())
							s = module->Not(NEW_ID, s);
						t = module->Or(NEW_ID, t, s);

						SigSpec c = cell->getPort("\\CLR");
						if (cell->parameters["\\CLR_POLARITY"].as_bool())
							c = module->Not(NEW_ID, c);
						module->addAnd(NEW_ID, t, c, sig_q);
					}

					Const initval;
					bool assign_initval = false;
					for (int i = 0; i < GetSize(sig_d); i++) {
						SigBit qbit = sigmap(sig_q[i]);
						if (initbits.count(qbit)) {
							initval.bits.push_back(initbits.at(qbit));
							del_initbits.insert(qbit);
						} else
							initval.bits.push_back(State::Sx);
						if (initval.bits.back() != State::Sx)
							assign_initval = true;
					}

					if (assign_initval)
						past_q->attributes["\\init"] = initval;

					module->remove(cell);
					continue;
				}

				bool word_dff = cell->type.in("$dff", "$adff", "$dffsr");
				if (word_dff || cell->type.in(ID($_DFF_N_), ID($_DFF_P_),
						ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
						ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_),
						ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
						ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_)))
				{
					bool clkpol;
					SigSpec clk;
					if (word_dff) {
						clkpol = cell->parameters["\\CLK_POLARITY"].as_bool();
						clk = cell->getPort("\\CLK");
					}
					else {
						if (cell->type.in(ID($_DFF_P_), ID($_DFF_N_),
									ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
									ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_)))
							clkpol = cell->type[6] == 'P';
						else if (cell->type.in(ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
									ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_)))
							clkpol = cell->type[8] == 'P';
						else log_abort();
						clk = cell->getPort("\\C");
					}

					Wire *past_clk = module->addWire(NEW_ID);
					past_clk->attributes["\\init"] = clkpol ? State::S1 : State::S0;

					if (word_dff)
						module->addFf(NEW_ID, clk, past_clk);
					else
						module->addFfGate(NEW_ID, clk, past_clk);

					SigSpec sig_d = cell->getPort("\\D");
					SigSpec sig_q = cell->getPort("\\Q");

					log("Replacing %s.%s (%s): CLK=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(clk), log_signal(sig_d), log_signal(sig_q));

					SigSpec clock_edge_pattern;

					if (clkpol) {
						clock_edge_pattern.append_bit(State::S0);
						clock_edge_pattern.append_bit(State::S1);
					} else {
						clock_edge_pattern.append_bit(State::S1);
						clock_edge_pattern.append_bit(State::S0);
					}

					SigSpec clock_edge = module->Eqx(NEW_ID, {clk, SigSpec(past_clk)}, clock_edge_pattern);

					Wire *past_d = module->addWire(NEW_ID, GetSize(sig_d));
					Wire *past_q = module->addWire(NEW_ID, GetSize(sig_q));
					if (word_dff) {
						module->addFf(NEW_ID, sig_d, past_d);
						module->addFf(NEW_ID, sig_q, past_q);
					}
					else {
						module->addFfGate(NEW_ID, sig_d, past_d);
						module->addFfGate(NEW_ID, sig_q, past_q);
					}

					if (cell->type == "$adff")
					{
						SigSpec arst = cell->getPort("\\ARST");
						SigSpec qval = module->Mux(NEW_ID, past_q, past_d, clock_edge);
						Const rstval = cell->parameters["\\ARST_VALUE"];

						Wire *past_arst = module->addWire(NEW_ID);
						module->addFf(NEW_ID, arst, past_arst);
						if (cell->parameters["\\ARST_POLARITY"].as_bool())
							arst = module->LogicOr(NEW_ID, arst, past_arst);
						else
							arst = module->LogicAnd(NEW_ID, arst, past_arst);

						if (cell->parameters["\\ARST_POLARITY"].as_bool())
							module->addMux(NEW_ID, qval, rstval, arst, sig_q);
						else
							module->addMux(NEW_ID, rstval, qval, arst, sig_q);
					}
					else
					if (cell->type.in(ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
						ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_)))
					{
						SigSpec arst = cell->getPort("\\R");
						SigSpec qval = module->MuxGate(NEW_ID, past_q, past_d, clock_edge);
						SigBit rstval = (cell->type[8] == '1');

						Wire *past_arst = module->addWire(NEW_ID);
						module->addFfGate(NEW_ID, arst, past_arst);
						if (cell->type[7] == 'P')
							arst = module->OrGate(NEW_ID, arst, past_arst);
						else
							arst = module->AndGate(NEW_ID, arst, past_arst);

						if (cell->type[7] == 'P')
							module->addMuxGate(NEW_ID, qval, rstval, arst, sig_q);
						else
							module->addMuxGate(NEW_ID, rstval, qval, arst, sig_q);
					}
					else
					if (cell->type == "$dffsr")
					{
						SigSpec qval = module->Mux(NEW_ID, past_q, past_d, clock_edge);
						SigSpec setval = cell->getPort("\\SET");
						SigSpec clrval = cell->getPort("\\CLR");

						if (!cell->parameters["\\SET_POLARITY"].as_bool())
							setval = module->Not(NEW_ID, setval);

						if (cell->parameters["\\CLR_POLARITY"].as_bool())
							clrval = module->Not(NEW_ID, clrval);

						qval = module->Or(NEW_ID, qval, setval);
						module->addAnd(NEW_ID, qval, clrval, sig_q);
					}
					else
					if (cell->type.in(ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
						ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_)))
					{
						SigSpec qval = module->MuxGate(NEW_ID, past_q, past_d, clock_edge);
						SigSpec setval = cell->getPort("\\S");
						SigSpec clrval = cell->getPort("\\R");

						if (cell->type[9] != 'P')
							setval = module->Not(NEW_ID, setval);

						if (cell->type[10] == 'P')
							clrval = module->Not(NEW_ID, clrval);

						qval = module->OrGate(NEW_ID, qval, setval);
						module->addAndGate(NEW_ID, qval, clrval, sig_q);
					}
					else if (cell->type == "$dff")
					{
						module->addMux(NEW_ID, past_q, past_d, clock_edge, sig_q);
					}
					else
					{
						module->addMuxGate(NEW_ID, past_q, past_d, clock_edge, sig_q);
					}

					Const initval;
					bool assign_initval = false;
					for (int i = 0; i < GetSize(sig_d); i++) {
						SigBit qbit = sigmap(sig_q[i]);
						if (initbits.count(qbit)) {
							initval.bits.push_back(initbits.at(qbit));
							del_initbits.insert(qbit);
						} else
							initval.bits.push_back(State::Sx);
						if (initval.bits.back() != State::Sx)
							assign_initval = true;
					}

					if (assign_initval) {
						past_d->attributes["\\init"] = initval;
						past_q->attributes["\\init"] = initval;
					}

					module->remove(cell);
					continue;
				}
			}

			for (auto wire : module->wires())
				if (wire->attributes.count("\\init") > 0)
				{
					bool delete_initattr = true;
					Const initval = wire->attributes.at("\\init");
					SigSpec initsig = sigmap(wire);

					for (int i = 0; i < GetSize(initval) && i < GetSize(initsig); i++)
						if (del_initbits.count(initsig[i]) > 0)
							initval[i] = State::Sx;
						else if (initval[i] != State::Sx)
							delete_initattr = false;

					if (delete_initattr)
						wire->attributes.erase("\\init");
					else
						wire->attributes.at("\\init") = initval;
				}
		}

	}
} Clk2fflogicPass;

PRIVATE_NAMESPACE_END
