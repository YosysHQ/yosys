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

#define MODE_ZERO     0
#define MODE_ONE      1
#define MODE_UNDEF    2
#define MODE_RANDOM   3
#define MODE_ANYSEQ   4
#define MODE_ANYCONST 5

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static RTLIL::Wire * add_wire(RTLIL::Module *module, std::string name, int width, bool flag_input, bool flag_output)
{
	RTLIL::Wire *wire = NULL;
	name = RTLIL::escape_id(name);

	if (module->count_id(name) != 0)
	{
		log("Module %s already has such an object %s.\n", module->name.c_str(), name.c_str());
		name += "$";
		return add_wire(module, name, width, flag_input, flag_output);
	}
	else
	{
		wire = module->addWire(name, width);
		wire->port_input = flag_input;
		wire->port_output = flag_output;

		if (flag_input || flag_output) {
			wire->port_id = module->wires_.size();
			module->fixup_ports();
		}

		log("Added wire %s to module %s.\n", name.c_str(), module->name.c_str());
	}

	return wire;
}

struct SetundefWorker
{
	int next_bit_mode;
	uint32_t next_bit_state;
	vector<SigSpec*> siglist;

	RTLIL::State next_bit()
	{
		if (next_bit_mode == MODE_ZERO)
			return RTLIL::State::S0;

		if (next_bit_mode == MODE_ONE)
			return RTLIL::State::S1;

		if (next_bit_mode == MODE_UNDEF)
			return RTLIL::State::Sx;

		if (next_bit_mode == MODE_RANDOM)
		{
			// xorshift32
			next_bit_state ^= next_bit_state << 13;
			next_bit_state ^= next_bit_state >> 17;
			next_bit_state ^= next_bit_state << 5;
			log_assert(next_bit_state != 0);

			return ((next_bit_state >> (next_bit_state & 15)) & 16) ? RTLIL::State::S0 : RTLIL::State::S1;
		}

		log_abort();
	}

	void operator()(RTLIL::SigSpec &sig)
	{
		if (next_bit_mode == MODE_ANYSEQ || next_bit_mode == MODE_ANYCONST) {
			siglist.push_back(&sig);
			return;
		}

		for (auto &bit : sig)
			if (bit.wire == NULL && bit.data > RTLIL::State::S1)
				bit = next_bit();
	}
};

struct SetundefPass : public Pass {
	SetundefPass() : Pass("setundef", "replace undef values with defined constants") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setundef [options] [selection]\n");
		log("\n");
		log("This command replaces undef (x) constants with defined (0/1) constants.\n");
		log("\n");
		log("    -undriven\n");
		log("        also set undriven nets to constant values\n");
		log("\n");
		log("    -expose\n");
		log("        also expose undriven nets as inputs (use with -undriven)\n");
		log("\n");
		log("    -zero\n");
		log("        replace with bits cleared (0)\n");
		log("\n");
		log("    -one\n");
		log("        replace with bits set (1)\n");
		log("\n");
		log("    -undef\n");
		log("        replace with undef (x) bits, may be used with -undriven\n");
		log("\n");
		log("    -anyseq\n");
		log("        replace with $anyseq drivers (for formal)\n");
		log("\n");
		log("    -anyconst\n");
		log("        replace with $anyconst drivers (for formal)\n");
		log("\n");
		log("    -random <seed>\n");
		log("        replace with random bits using the specified integer as seed\n");
		log("        value for the random number generator.\n");
		log("\n");
		log("    -init\n");
		log("        also create/update init values for flip-flops\n");
		log("\n");
		log("    -params\n");
		log("        replace undef in cell parameters\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool got_value = false;
		bool undriven_mode = false;
		bool expose_mode = false;
		bool init_mode = false;
		bool params_mode = false;
		SetundefWorker worker;

		log_header(design, "Executing SETUNDEF pass (replace undef values with defined constants).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-undriven") {
				undriven_mode = true;
				continue;
			}
			if (args[argidx] == "-expose") {
				expose_mode = true;
				continue;
			}
			if (args[argidx] == "-zero") {
				got_value = true;
				worker.next_bit_mode = MODE_ZERO;
				worker.next_bit_state = 0;
				continue;
			}
			if (args[argidx] == "-one") {
				got_value = true;
				worker.next_bit_mode = MODE_ONE;
				worker.next_bit_state = 0;
				continue;
			}
			if (args[argidx] == "-anyseq") {
				got_value = true;
				worker.next_bit_mode = MODE_ANYSEQ;
				worker.next_bit_state = 0;
				continue;
			}
			if (args[argidx] == "-anyconst") {
				got_value = true;
				worker.next_bit_mode = MODE_ANYCONST;
				worker.next_bit_state = 0;
				continue;
			}
			if (args[argidx] == "-undef") {
				got_value = true;
				worker.next_bit_mode = MODE_UNDEF;
				worker.next_bit_state = 0;
				continue;
			}
			if (args[argidx] == "-init") {
				init_mode = true;
				continue;
			}
			if (args[argidx] == "-params") {
				params_mode = true;
				continue;
			}
			if (args[argidx] == "-random" && !got_value && argidx+1 < args.size()) {
				got_value = true;
				worker.next_bit_mode = MODE_RANDOM;
				worker.next_bit_state = atoi(args[++argidx].c_str()) + 1;
				for (int i = 0; i < 10; i++)
					worker.next_bit();
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!got_value && expose_mode) {
			log("Using default as -undef with -expose.\n");
			got_value = true;
			worker.next_bit_mode = MODE_UNDEF;
			worker.next_bit_state = 0;
		}

		if (expose_mode && !undriven_mode)
			log_cmd_error("Option -expose must be used with option -undriven.\n");
		if (!got_value)
			log_cmd_error("One of the options -zero, -one, -anyseq, -anyconst, or -random <seed> must be specified.\n");

		if (init_mode && (worker.next_bit_mode == MODE_ANYSEQ || worker.next_bit_mode == MODE_ANYCONST))
			log_cmd_error("The options -init and -anyseq / -anyconst are exclusive.\n");

		for (auto module : design->selected_modules())
		{
			if (params_mode)
			{
				for (auto *cell : module->selected_cells()) {
					for (auto &parameter : cell->parameters) {
						for (auto &bit : parameter.second.bits) {
							if (bit > RTLIL::State::S1)
								bit = worker.next_bit();
						}
					}
				}
			}

			if (undriven_mode)
			{
				if (!module->processes.empty())
					log_error("The 'setundef' command can't operate in -undriven mode on modules with processes. Run 'proc' first.\n");

				if (expose_mode)
				{
					SigMap sigmap(module);
					dict<SigBit, bool> wire_drivers;
					pool<SigBit> used_wires;
					SigPool undriven_signals;

					for (auto cell : module->cells())
						for (auto &conn : cell->connections()) {
							SigSpec sig = sigmap(conn.second);
							if (cell->input(conn.first))
								for (auto bit : sig)
									if (bit.wire)
										used_wires.insert(bit);
							if (cell->output(conn.first))
								for (int i = 0; i < GetSize(sig); i++)
									if (sig[i].wire)
										wire_drivers[sig[i]] = true;
						}

					for (auto wire : module->wires()) {
						if (wire->port_input) {
							SigSpec sig = sigmap(wire);
							for (int i = 0; i < GetSize(sig); i++)
								wire_drivers[sig[i]] = true;
						}
						if (wire->port_output) {
							SigSpec sig = sigmap(wire);
							for (auto bit : sig)
								if (bit.wire)
									used_wires.insert(bit);
						}
					}

					pool<RTLIL::Wire*> undriven_wires;
					for (auto bit : used_wires)
						if (!wire_drivers.count(bit))
							undriven_wires.insert(bit.wire);

					for (auto &it : undriven_wires)
						undriven_signals.add(sigmap(it));

					for (auto &it : undriven_wires)
						if (it->port_input)
							undriven_signals.del(sigmap(it));

					CellTypes ct(design);
					for (auto &it : module->cells_)
					for (auto &conn : it.second->connections())
						if (!ct.cell_known(it.second->type) || ct.cell_output(it.second->type, conn.first))
							undriven_signals.del(sigmap(conn.second));

					RTLIL::SigSpec sig = undriven_signals.export_all();
					for (auto &c : sig.chunks()) {
						RTLIL::Wire * wire;
						if (c.wire->width == c.width) {
							wire = c.wire;
							wire->port_input = true;
						} else {
							string name = c.wire->name.str() + "$[" + std::to_string(c.width + c.offset) + ":" + std::to_string(c.offset) + "]";
							wire = add_wire(module, name, c.width, true, false);
							module->connect(RTLIL::SigSig(c, wire));
						}
						log("Exposing undriven wire %s as input.\n", wire->name.c_str());
					}
					module->fixup_ports();
				}
				else
				{
					SigMap sigmap(module);
					SigPool undriven_signals;

					for (auto &it : module->wires_)
						undriven_signals.add(sigmap(it.second));

					for (auto &it : module->wires_)
						if (it.second->port_input)
							undriven_signals.del(sigmap(it.second));

					CellTypes ct(design);
					for (auto &it : module->cells_)
					for (auto &conn : it.second->connections())
						if (!ct.cell_known(it.second->type) || ct.cell_output(it.second->type, conn.first))
							undriven_signals.del(sigmap(conn.second));

					RTLIL::SigSpec sig = undriven_signals.export_all();
					for (auto &c : sig.chunks()) {
						RTLIL::SigSpec bits;
						if (worker.next_bit_mode == MODE_ANYSEQ)
							bits = module->Anyseq(NEW_ID, c.width);
						else if (worker.next_bit_mode == MODE_ANYCONST)
							bits = module->Anyconst(NEW_ID, c.width);
						else
							for (int i = 0; i < c.width; i++)
								bits.append(worker.next_bit());
						module->connect(RTLIL::SigSig(c, bits));
					}
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

				auto process_initwires = [&]()
				{
					dict<Wire*, int> wire_weights;

					for (auto wire : initwires)
					{
						int weight = 0;

						for (auto bit : sigmap(wire))
							weight += ffbits.count(bit) ? +1 : -1;

						wire_weights[wire] = weight;
					}

					initwires.sort([&](Wire *a, Wire *b) { return wire_weights.at(a) > wire_weights.at(b); });

					for (auto wire : initwires)
					{
						Const &initval = wire->attributes["\\init"];
						initval.bits.resize(GetSize(wire), State::Sx);

						for (int i = 0; i < GetSize(wire); i++) {
							SigBit bit = sigmap(SigBit(wire, i));
							if (initval[i] == State::Sx && ffbits.count(bit)) {
								initval[i] = worker.next_bit();
								ffbits.erase(bit);
							}
						}

						if (initval.is_fully_undef())
							wire->attributes.erase("\\init");
					}

					initwires.clear();
				};

				for (int wire_types = 0; wire_types < 2; wire_types++)
				{
					// prioritize wires that already have an init attribute
					if (!ffbits.empty())
					{
						for (auto wire : module->wires())
						{
							if (wire->name[0] == (wire_types ? '\\' : '$'))
								continue;

							if (!wire->attributes.count("\\init"))
								continue;

							Const &initval = wire->attributes["\\init"];
							initval.bits.resize(GetSize(wire), State::Sx);

							if (initval.is_fully_undef()) {
								wire->attributes.erase("\\init");
								continue;
							}

							for (int i = 0; i < GetSize(wire); i++)
								if (initval[i] != State::Sx)
									ffbits.erase(sigmap(SigBit(wire, i)));

							initwires.insert(wire);
						}

						process_initwires();
					}

					// next consider wires that completely contain bits to be initialized
					if (!ffbits.empty())
					{
						for (auto wire : module->wires())
						{
							if (wire->name[0] == (wire_types ? '\\' : '$'))
								continue;

							for (auto bit : sigmap(wire))
								if (!ffbits.count(bit))
									goto next_wire;

							initwires.insert(wire);

						next_wire:
							continue;
						}

						process_initwires();
					}

					// finally use whatever wire we can find.
					if (!ffbits.empty())
					{
						for (auto wire : module->wires())
						{
							if (wire->name[0] == (wire_types ? '\\' : '$'))
								continue;

							for (auto bit : sigmap(wire))
								if (ffbits.count(bit))
									initwires.insert(wire);
						}

						process_initwires();
					}
				}

				log_assert(ffbits.empty());
			}

			module->rewrite_sigspecs(worker);

			if (worker.next_bit_mode == MODE_ANYSEQ || worker.next_bit_mode == MODE_ANYCONST)
			{
				vector<SigSpec*> siglist;
				siglist.swap(worker.siglist);

				for (auto sigptr : siglist)
				{
					SigSpec &sig = *sigptr;
					int cursor = 0;

					while (cursor < GetSize(sig))
					{
						int width = 0;
						while (cursor+width < GetSize(sig) && sig[cursor+width] == State::Sx)
							width++;

						if (width > 0) {
							if (worker.next_bit_mode == MODE_ANYSEQ)
								sig.replace(cursor, module->Anyseq(NEW_ID, width));
							else
								sig.replace(cursor, module->Anyconst(NEW_ID, width));
							cursor += width;
						} else {
							cursor++;
						}
					}
				}
			}
		}
	}
} SetundefPass;

PRIVATE_NAMESPACE_END
