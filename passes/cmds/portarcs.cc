/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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


#include "kernel/timinginfo.h"
#include "kernel/rtlil.h"
#include "kernel/utils.h"
#include "kernel/celltypes.h"

PRIVATE_NAMESPACE_BEGIN
USING_YOSYS_NAMESPACE

static RTLIL::SigBit canonical_bit(RTLIL::SigBit bit)
{
	RTLIL::Wire *w;
	while ((w = bit.wire) != NULL && !w->port_input &&
			w->driverCell()->type.in(ID($buf), ID($_BUF_))) {
		bit = w->driverCell()->getPort(ID::A)[bit.offset];
	}
	return bit;
}

struct PortarcsPass : Pass {
	PortarcsPass() : Pass("portarcs", "derive port arcs for propagation delay") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    portarcs [options] [selection]\n");
		log("\n");
		log("This command characterizes the combinational content of selected modules and\n");
		log("derives timing arcs going from module inputs to module outputs representing the\n");
		log("propagation delay of the module.\n");
		log("\n");
		log("    -draw\n");
		log("        plot the computed delay table to the terminal\n");
		log("\n");
		log("    -icells\n");
		log("        assign unit delay to gates from the internal Yosys cell library\n");
		log("\n");
		log("    -write\n");
		log("        write the computed arcs back into the module as $specify2 instances\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing PORTARCS pass. (derive propagation arcs)\n");

		size_t argidx;
		bool icells_mode = false, write_mode = false, draw_mode = false;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-icells")
				icells_mode = true;
			else if (args[argidx] == "-write")
				write_mode = true;
			else if (args[argidx] == "-draw")
				draw_mode = true;
			else
				break;
		}
		extra_args(args, argidx, d);

		d->bufNormalize(true);
		TimingInfo tinfo(d);

		if (icells_mode) {
			CellTypes ct;
			ct.setup_stdcells_eval();
			for (auto [id, type] : ct.cell_types) {
				auto &tdata = tinfo.data[id];
				tdata.has_inputs = true;
				for (auto inp : type.inputs)
					for (auto out : type.outputs)
						tdata.comb[TimingInfo::BitBit({inp, 0}, {out, 0})] = 1000;
			}
		}

		for (auto m : d->selected_whole_modules_warn()) {
			bool ambiguous_ports = false;
			SigSpec inputs, outputs;
			for (auto port : m->ports) {
				Wire *w = m->wire(port);
				log_assert(w->port_input || w->port_output);
				if (w->port_input && w->port_output) {
					log_warning("Module '%s' with ambiguous direction on port %s ignored.\n",
								log_id(m), log_id(w));
					ambiguous_ports = true;
					break;
				}
				if (w->port_input)
					inputs.append(w);
				else
					outputs.append(w);
			}
			if (ambiguous_ports)
				continue;

			SigSpec ordering;
			{
				TopoSort<SigBit> sort;

				for (auto cell : m->cells())
				if (cell->type != ID($buf)) {
					auto tdata = tinfo.find(cell->type);
					if (tdata == tinfo.end())
						log_cmd_error("Missing timing data for module '%s'.\n", log_id(cell->type));
					for (auto [edge, delay] : tdata->second.comb) {
						auto from = edge.first.get_connection(cell);
						auto to = edge.second.get_connection(cell);
						if (from && to) {
							auto from_c = canonical_bit(from.value());
							if (from_c.wire)
								sort.edge(from_c, to.value());
						}
					}
				}

				if (!sort.sort())
					log_error("Failed to sort instances in module %s.\n", log_id(m));

				ordering = sort.sorted;
			}

			dict<SigBit, int*> annotations;
			std::vector<std::unique_ptr<int[]>> allocated;
			std::vector<int*> recycling;

			auto alloc_for_bit = [&](SigBit bit) {
				if (!recycling.empty()) {
					annotations[bit] = recycling.back();
					recycling.pop_back();
				} else {
					int *p = new int[std::max(1, inputs.size())];
					allocated.emplace_back(p);
					annotations[bit] = p;
				}
			};

			for (auto bit : outputs) {
				SigBit bit_c = canonical_bit(bit);
				alloc_for_bit(bit_c);

				// consistency check
				annotations.at(bit_c)[0] = (intptr_t) bit_c.wire;
			}

			for (int i = ordering.size() - 1; i >= 0; i--) {
				SigBit bit = ordering[i];

				if (!bit.wire->port_input) {
					auto cell = bit.wire->driverCell();
					auto tdata = tinfo.find(cell->type);
					log_assert(tdata != tinfo.end());
					for (auto [edge, delay] : tdata->second.comb) {
						auto from = edge.first.get_connection(cell);
						auto to = edge.second.get_connection(cell);
						if (from && to && to.value() == bit) {
							auto from_c = canonical_bit(from.value());
							if (from_c.wire) {
								if (!annotations.count(from_c)) {
									alloc_for_bit(from_c);

									// consistency check
									annotations.at(from_c)[0] = (intptr_t) from_c.wire;
								} else {
									// consistency check
									log_assert(annotations.at(from_c)[0] == ((int) (intptr_t) from_c.wire));
								}
							}
						}
					}
				}

				if (annotations.count(bit)) {
					// consistency check
					log_assert(annotations.at(bit)[0] == ((int) (intptr_t) bit.wire));
				} else {
					alloc_for_bit(bit);
				}

				recycling.push_back(annotations.at(ordering[i]));
			}
			log_debug("Allocated %lux%d\n", allocated.size(), inputs.size());

			for (auto bit : outputs) {
				int *p = annotations.at(canonical_bit(bit));
				for (int i = 0; i < inputs.size(); i++)
					p[i] = -1;
			}

			for (int i = 0; i < ordering.size(); i++) {
				SigBit bit = ordering[i];
				int *p = annotations.at(bit);
				if (bit.wire->port_input) {
					for (int j = 0; j < inputs.size(); j++)
						p[j] = (j == i) ? 0 : -1;
				} else {
					for (int j = 0; j < inputs.size(); j++)
						p[j] = -1;

					auto cell = ordering[i].wire->driverCell();
					auto tdata = tinfo.find(cell->type);
					log_assert(tdata != tinfo.end());
					for (auto [edge, delay] : tdata->second.comb) {
						auto from = edge.first.get_connection(cell);
						auto to = edge.second.get_connection(cell);
						if (from && to && to.value() == ordering[i]) {
							auto from_c = canonical_bit(from.value());
							if (from_c.wire) {
								int *q = annotations.at(from_c);
								for (int j = 0; j < inputs.size(); j++)
									if (q[j] >= 0)
										p[j] = std::max(p[j], q[j] + delay);
							}
						}
					}
				}
			}

			if (draw_mode) {
				auto bit_str = [](SigBit bit) {
					return stringf("%s%d", RTLIL::unescape_id(bit.wire->name.str()).c_str(), bit.offset);
				};

				std::vector<std::string> headings;
				int top_length = 0;
				for (auto bit : inputs) {
					headings.push_back(bit_str(bit));
					top_length = std::max(top_length, (int) headings.back().size());
				}

				int max_delay = 0;
				for (auto bit : outputs) {
					int *p = annotations.at(canonical_bit(bit));
					for (auto i = 0; i < inputs.size(); i++)
						if (p[i] > max_delay)
							max_delay = p[i];
				}

				log("Delay legend:\n\n");
				log("    ");
				for (int i = 0; i < 24; i++)
					log("\033[48;5;%dm ", 232+i);
				log("\033[0m\n");
				log("    |%22s|\n", "");
				log("    0%22s%d\n", "", max_delay);
				log("\n");
				for (int k = top_length - 1; k >= 0; k--) {
					log("  %10s  ", "");
					for (auto &h : headings)
						log("%c", (k < (int) h.size()) ? h[k] : ' ');
					log("\n");
				}
				log("\n");

				for (auto bit : outputs) {
					log("  %10s  ", bit_str(bit).c_str());
					int *p = annotations.at(canonical_bit(bit));
					for (auto i = 0; i < inputs.size(); i++)
						log("\033[48;5;%dm ", 232 + ((std::max(p[i], 0) * 24) - 1) / max_delay);
					log("\033[0m\n");
				}
			}

			if (write_mode) {
				for (auto bit : outputs) {
					int *p = annotations.at(canonical_bit(bit));
					for (auto i = 0; i < inputs.size(); i++) {
						if (p[i] >= 0) {
							Cell *spec = m->addCell(NEW_ID, ID($specify2));
							spec->setParam(ID::SRC_WIDTH, 1);
							spec->setParam(ID::DST_WIDTH, 1);
							spec->setParam(ID::T_FALL_MAX, p[i]);
							spec->setParam(ID::T_FALL_TYP, p[i]);
							spec->setParam(ID::T_FALL_MIN, p[i]);
							spec->setParam(ID::T_RISE_MAX, p[i]);
							spec->setParam(ID::T_RISE_TYP, p[i]);
							spec->setParam(ID::T_RISE_MIN, p[i]);
							spec->setParam(ID::SRC_DST_POL, false);
							spec->setParam(ID::SRC_DST_PEN, false);
							spec->setParam(ID::FULL, false);
							spec->setPort(ID::EN, Const(1, 1));
							spec->setPort(ID::SRC, inputs[i]);
							spec->setPort(ID::DST, bit);
						}
					}
				}
			}
		}
		d->bufNormalize(false);
	}
} PortarcsPass;

PRIVATE_NAMESPACE_END
