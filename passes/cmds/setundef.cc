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
		log("    -init\n");
		log("        also create/update init values for flip-flops\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool got_value = false;
		bool undriven_mode = false;
		bool init_mode = false;
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
			if (args[argidx] == "-init") {
				init_mode = true;
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

		for (auto module : design->selected_modules())
		{
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

			if (init_mode)
			{
				SigMap sigmap(module);
				pool<SigBit> ffbits;
				pool<Wire*> initwires;

				pool<IdString> fftypes;
				fftypes.insert("$dff");
				fftypes.insert("$dffe");
				fftypes.insert("$dffsr");
				fftypes.insert("$adff");

				std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

				for (auto c1 : list_np)
					fftypes.insert(stringf("$_DFF_%c_", c1));

				for (auto c1 : list_np)
				for (auto c2 : list_np)
					fftypes.insert(stringf("$_DFFE_%c%c_", c1, c2));

				for (auto c1 : list_np)
				for (auto c2 : list_np)
				for (auto c3 : list_01)
					fftypes.insert(stringf("$_DFF_%c%c%c_", c1, c2, c3));

				for (auto c1 : list_np)
				for (auto c2 : list_np)
				for (auto c3 : list_np)
					fftypes.insert(stringf("$_DFFSR_%c%c%c_", c1, c2, c3));

				for (auto cell : module->cells())
				{
					if (!fftypes.count(cell->type))
						continue;

					for (auto bit : sigmap(cell->getPort("\\Q")))
						ffbits.insert(bit);
				}

				for (auto wire : module->wires())
				{
					if (!wire->attributes.count("\\init"))
						continue;

					for (auto bit : sigmap(wire))
						ffbits.erase(bit);

					initwires.insert(wire);
				}

				for (int wire_types = 0; wire_types < 2; wire_types++)
					for (auto wire : module->wires())
					{
						if (wire->name[0] == (wire_types ? '\\' : '$'))
					next_wire:
							continue;

						for (auto bit : sigmap(wire))
							if (!ffbits.count(bit))
								goto next_wire;

						for (auto bit : sigmap(wire))
							ffbits.erase(bit);

						initwires.insert(wire);
					}

				for (auto wire : initwires)
				{
					Const &initval = wire->attributes["\\init"];

					for (int i = 0; i < GetSize(wire); i++)
						if (GetSize(initval) <= i)
							initval.bits.push_back(worker.next_bit());
						else if (initval.bits[i] == State::Sx)
							initval.bits[i] = worker.next_bit();
				}
			}

			module->rewrite_sigspecs(worker);
		}
	}
} SetundefPass;

PRIVATE_NAMESPACE_END
