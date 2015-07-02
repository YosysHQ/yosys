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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SetundefWorker
{
	int next_bit_mode;
	uint32_t next_bit_state;

	RTLIL::State next_bit()
	{
		if (next_bit_mode == 0)
			return RTLIL::State::S0;

		if (next_bit_mode == 1)
			return RTLIL::State::S1;

		// xorshift32
		next_bit_state ^= next_bit_state << 13;
		next_bit_state ^= next_bit_state >> 17;
		next_bit_state ^= next_bit_state << 5;
		log_assert(next_bit_state != 0);

		return ((next_bit_state >> (next_bit_state & 15)) & 16) ? RTLIL::State::S0 : RTLIL::State::S1;
	}

	void operator()(RTLIL::SigSpec &sig)
	{
		for (auto &bit : sig)
			if (bit.wire == NULL && bit.data > RTLIL::State::S1)
				bit = next_bit();
	}
};

struct SetundefPass : public Pass {
	SetundefPass() : Pass("setundef", "replace undef values with defined constants") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setundef [options] [selection]\n");
		log("\n");
		log("This command replaced undef (x) constants with defined (0/1) constants.\n");
		log("\n");
		log("    -undriven\n");
		log("        also set undriven nets to constant values\n");
		log("\n");
		log("    -zero\n");
		log("        replace with bits cleared (0)\n");
		log("\n");
		log("    -one\n");
		log("        replace with bits set (1)\n");
		log("\n");
		log("    -random <seed>\n");
		log("        replace with random bits using the specified integer als seed\n");
		log("        value for the random number generator.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool got_value = false;
		bool undriven_mode = false;
		SetundefWorker worker;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-undriven") {
				undriven_mode = true;
				continue;
			}
			if (args[argidx] == "-zero") {
				got_value = true;
				worker.next_bit_mode = 0;
				continue;
			}
			if (args[argidx] == "-one") {
				got_value = true;
				worker.next_bit_mode = 1;
				continue;
			}
			if (args[argidx] == "-random" && !got_value && argidx+1 < args.size()) {
				got_value = true;
				worker.next_bit_mode = 2;
				worker.next_bit_state = atoi(args[++argidx].c_str()) + 1;
				for (int i = 0; i < 10; i++)
					worker.next_bit();
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!got_value)
			log_cmd_error("One of the options -zero, -one, or -random <seed> must be specified.\n");

		for (auto &mod_it : design->modules_)
		{
			RTLIL::Module *module = mod_it.second;
			if (!design->selected(module))
				continue;

			if (undriven_mode)
			{
				if (!module->processes.empty())
					log_error("The 'setundef' command can't operate in -undriven mode on modules with processes. Run 'proc' first.\n");

				SigMap sigmap(module);
				SigPool undriven_signals;

				for (auto &it : module->wires_)
					if (!it.second->port_input)
						undriven_signals.add(sigmap(it.second));

				CellTypes ct(design);
				for (auto &it : module->cells_)
				for (auto &conn : it.second->connections())
					if (!ct.cell_known(it.second->type) || ct.cell_output(it.second->type, conn.first))
						undriven_signals.del(sigmap(conn.second));

				RTLIL::SigSpec sig = undriven_signals.export_all();
				for (auto &c : sig.chunks()) {
					RTLIL::SigSpec bits;
					for (int i = 0; i < c.width; i++)
						bits.append(worker.next_bit());
					module->connect(RTLIL::SigSig(c, bits));
				}
			}

			module->rewrite_sigspecs(worker);
		}
	}
} SetundefPass;

PRIVATE_NAMESPACE_END
