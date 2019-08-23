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

struct DeminoutPass : public Pass {
	DeminoutPass() : Pass("deminout", "demote inout ports to input or output") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    deminout [options] [selection]\n");
		log("\n");
		log("\"Demote\" inout ports to input or output ports, if possible.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing DEMINOUT pass (demote inout ports to input or output).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-bits") {
			// 	flag_bits = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		bool keep_running = true;

		while (keep_running)
		{
			keep_running = false;

			for (auto module : design->selected_modules())
			{
				SigMap sigmap(module);
				pool<SigBit> bits_written, bits_used, bits_inout, bits_tribuf;
				dict<SigBit, int> bits_numports;

				for (auto wire : module->wires())
					if (wire->port_id)
						for (auto bit : sigmap(wire))
							bits_numports[bit]++;

				for (auto cell : module->cells())
				for (auto &conn : cell->connections())
				{
					bool cellport_out = cell->output(conn.first) || !cell->known();
					bool cellport_in = cell->input(conn.first) || !cell->known();

					if (cellport_out && cellport_in)
						for (auto bit : sigmap(conn.second))
							bits_inout.insert(bit);

					if (cellport_out)
						for (auto bit : sigmap(conn.second))
							bits_written.insert(bit);

					if (cellport_in)
						for (auto bit : sigmap(conn.second))
							bits_used.insert(bit);

					if (conn.first == ID::Y && cell->type.in(ID($mux), ID($pmux), ID($_MUX_), ID($_TBUF_), ID($tribuf)))
					{
						bool tribuf = cell->type.in(ID($_TBUF_), ID($tribuf));

						if (!tribuf) {
							for (auto &c : cell->connections()) {
								if (!c.first.in(ID::A, ID::B))
									continue;
								for (auto b : sigmap(c.second))
									if (b == State::Sz)
										tribuf = true;
							}
						}

						if (tribuf)
							for (auto bit : sigmap(conn.second))
								bits_tribuf.insert(bit);
					}
				}

				for (auto wire : module->selected_wires())
					if (wire->port_input && wire->port_output)
					{
						bool new_input = false;
						bool new_output = false;

						for (auto bit : sigmap(wire))
						{
							if (bits_numports[bit] > 1 || bits_inout.count(bit))
								new_input = true, new_output = true;
							if (bit == State::S0 || bit == State::S1)
								new_output = true;
							if (bits_written.count(bit)) {
								new_output = true;
								if (bits_tribuf.count(bit))
									goto tribuf_bit;
							} else {
						tribuf_bit:
								if (bits_used.count(bit))
									new_input = true;
							}
						}

						if (new_input != new_output) {
							log("Demoting inout port %s.%s to %s.\n", log_id(module), log_id(wire), new_input ? "input" : "output");
							wire->port_input = new_input;
							wire->port_output = new_output;
							keep_running = true;
						}
					}
			}
		}
	}
} DeminoutPass;

PRIVATE_NAMESPACE_END
