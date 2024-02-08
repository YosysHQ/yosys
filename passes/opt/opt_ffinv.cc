/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/modtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptFfInvWorker
{
	int count = 0;
	RTLIL::Module *module;
	ModIndex index;
	FfInitVals initvals;

	// Case 1:
	// - FF is driven by inverter
	// - ... which has no other users
	// - all users of FF are LUTs
	bool push_d_inv(FfData &ff) {
		log_assert(ff.width == 1);
		if (index.query_is_input(ff.sig_d))
			return false;
		if (index.query_is_output(ff.sig_d))
			return false;
		auto d_ports = index.query_ports(ff.sig_d);
		if (d_ports.size() != 2)
			return false;
		Cell *d_inv = nullptr;
		for (auto &port: d_ports) {
			if (port.cell == ff.cell && port.port == ID::D)
				continue;
			if (port.port != ID::Y)
				return false;
			if (port.cell->type.in(ID($not), ID($_NOT_))) {
				// OK
			} else if (port.cell->type.in(ID($lut))) {
				if (port.cell->getParam(ID::WIDTH) != 1)
					return false;
				if (port.cell->getParam(ID::LUT).as_int() != 1)
					return false;
			} else {
				return false;
			}
			log_assert(d_inv == nullptr);
			d_inv = port.cell;
		}
		if (!d_inv) return false;

		if (index.query_is_output(ff.sig_q))
			return false;
		auto q_ports = index.query_ports(ff.sig_q);
		pool<Cell *> q_luts;
		for (auto &port: q_ports) {
			if (port.cell == ff.cell && port.port == ID::Q)
				continue;
			if (port.cell == d_inv)
				return false;
			if (port.port != ID::A)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_), ID($lut)))
				return false;
			q_luts.insert(port.cell);
		}

		ff.flip_rst_bits({0});
		ff.sig_d = d_inv->getPort(ID::A);

		for (Cell *lut: q_luts) {
			if (lut->type == ID($lut)) {
				int flip_mask = 0;
				SigSpec sig_a = lut->getPort(ID::A);
				for (int i = 0; i < GetSize(sig_a); i++) {
					if (index.sigmap(sig_a[i]) == index.sigmap(ff.sig_q[0])) {
						flip_mask |= 1 << i;
					}
				}
				Const mask = lut->getParam(ID::LUT);
				Const new_mask;
				for (int j = 0; j < (1 << GetSize(sig_a)); j++) {
					new_mask.bits.push_back(mask.bits[j ^ flip_mask]);
				}
				if (GetSize(sig_a) == 1 && new_mask.as_int() == 2) {
					module->connect(lut->getPort(ID::Y), ff.sig_q);
					module->remove(lut);
				} else {
					lut->setParam(ID::LUT, new_mask);
				}
			} else {
				// it was an inverter
				module->connect(lut->getPort(ID::Y), ff.sig_q);
				module->remove(lut);
			}
		}

		ff.emit();
		return true;
	}

	// Case 2:
	// - FF is driven by LUT
	// - ... which has no other users
	// - FF has one user
	// - ... which is an inverter
	bool push_q_inv(FfData &ff) {
		if (index.query_is_input(ff.sig_d))
			return false;
		if (index.query_is_output(ff.sig_d))
			return false;

		Cell *d_lut = nullptr;
		auto d_ports = index.query_ports(ff.sig_d);
		if (d_ports.size() != 2)
			return false;
		for (auto &port: d_ports) {
			if (port.cell == ff.cell && port.port == ID::D)
				continue;
			if (port.port != ID::Y)
				return false;
			if (!port.cell->type.in(ID($not), ID($_NOT_), ID($lut)))
				return false;
			log_assert(d_lut == nullptr);
			d_lut = port.cell;
		}
		if (!d_lut) return false;

		if (index.query_is_output(ff.sig_q))
			return false;
		auto q_ports = index.query_ports(ff.sig_q);
		if (q_ports.size() != 2)
			return false;
		Cell *q_inv = nullptr;
		for (auto &port: q_ports) {
			if (port.cell == ff.cell && port.port == ID::Q)
				continue;
			if (port.cell == d_lut)
				return false;
			if (port.port != ID::A)
				return false;
			if (port.cell->type.in(ID($not), ID($_NOT_))) {
				// OK
			} else if (port.cell->type.in(ID($lut))) {
				if (port.cell->getParam(ID::WIDTH) != 1)
					return false;
				if (port.cell->getParam(ID::LUT).as_int() != 1)
					return false;
			} else {
				return false;
			}
			log_assert(q_inv == nullptr);
			q_inv = port.cell;
		}
		if (!q_inv) return false;

		ff.flip_rst_bits({0});
		ff.sig_q = q_inv->getPort(ID::Y);
		module->remove(q_inv);

		if (d_lut->type == ID($lut)) {
			Const mask = d_lut->getParam(ID::LUT);
			Const new_mask;
			for (int i = 0; i < GetSize(mask); i++) {
				if (mask.bits[i] == State::S0)
					new_mask.bits.push_back(State::S1);
				else
					new_mask.bits.push_back(State::S0);
			}
			d_lut->setParam(ID::LUT, new_mask);
			if (d_lut->getParam(ID::WIDTH) == 1 && new_mask.as_int() == 2) {
				module->connect(ff.sig_d, d_lut->getPort(ID::A));
				module->remove(d_lut);
			}
		} else {
			// it was an inverter
			module->connect(ff.sig_d, d_lut->getPort(ID::A));
			module->remove(d_lut);
		}

		ff.emit();
		return true;
	}

	OptFfInvWorker(RTLIL::Module *module) :
		module(module), index(module), initvals(&index.sigmap, module)
	{
		log("Discovering LUTs.\n");

		std::vector<Cell *> ffs;

		for (Cell *cell : module->selected_cells())
			if (RTLIL::builtin_ff_cell_types().count(cell->type))
				ffs.push_back(cell);

		for (Cell *cell : ffs) {
			FfData ff(&initvals, cell);
			if (ff.has_sr)
				continue;
			if (!ff.has_clk)
				continue;
			if (ff.has_aload)
				continue;
			if (ff.width != 1)
				continue;

			if (push_d_inv(ff)) {
				count++;
			} else if (push_q_inv(ff)) {
				count++;
			}
		}
	}
};

struct OptFfInvPass : public Pass {
	OptFfInvPass() : Pass("opt_ffinv", "push inverters through FFs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_ffinv [selection]\n");
		log("\n");
		log("This pass pushes inverters to the other side of a FF when they can be merged\n");
		log("into LUTs on the other side.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_FFINV pass (push inverters through FFs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules())
		{
			OptFfInvWorker worker(module);
			total_count += worker.count;
		}
		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Pushed %d inverters.\n", total_count);
	}
} OptFfInvPass;

PRIVATE_NAMESPACE_END
