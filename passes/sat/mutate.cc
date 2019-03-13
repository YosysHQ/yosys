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

struct mutate_t {
	std::string mode, src;
	IdString modname, cellname, celltype, cellport;
	SigBit outsigbit;
	int portbit = -1;
};

struct mutate_opts_t {
	std::string mode;
	IdString module, cell, port;
	int bit = -1;

	IdString ctrl_name;
	int ctrl_width, ctrl_value;
};

void database_add(std::vector<mutate_t> &database, const mutate_opts_t &opts, const mutate_t &entry)
{
	if (!opts.mode.empty() && opts.mode != entry.mode)
		return;

	if (!opts.module.empty() && opts.module != entry.modname)
		return;

	if (!opts.cell.empty() && opts.cell != entry.cellname)
		return;

	if (!opts.port.empty() && opts.port != entry.cellport)
		return;

	if (opts.bit >= 0 && opts.bit != entry.portbit)
		return;

	database.push_back(entry);
}

void database_reduce(std::vector<mutate_t> &database, const mutate_opts_t &opts, int N)
{
}

void mutate_list(Design *design, const mutate_opts_t &opts, const string &filename, int N)
{
	std::vector<mutate_t> database;

	for (auto module : design->selected_modules())
	{
		if (!opts.module.empty() && module->name != opts.module)
			continue;

		SigMap sigmap(module);

		for (auto wire : module->selected_wires())
		{
			for (SigBit bit : SigSpec(wire))
			{
				SigBit sigbit = sigmap(bit);

				if (bit.wire == nullptr || sigbit.wire == nullptr)
					continue;

				if (!bit.wire->port_id != !sigbit.wire->port_id) {
					if (bit.wire->port_id)
						sigmap.add(bit);
					continue;
				}

				if (!bit.wire->name[0] != !sigbit.wire->name[0]) {
					if (bit.wire->name[0] == '\\')
						sigmap.add(bit);
					continue;
				}
			}
		}

		for (auto cell : module->selected_cells())
		{
			if (!opts.cell.empty() && cell->name != opts.cell)
				continue;

			for (auto &conn : cell->connections())
			{
				for (int i = 0; i < GetSize(conn.second); i++) {
					mutate_t entry;
					entry.mode = "inv";
					entry.src = cell->get_src_attribute();
					entry.modname = module->name;
					entry.cellname = cell->name;
					entry.celltype = cell->type;
					entry.cellport = conn.first;
					entry.portbit = i;

					if (cell->output(conn.first)) {
						SigBit bit = sigmap(conn.second[i]);
						if (bit.wire && bit.wire->name[0] == '\\')
							entry.outsigbit = bit;
					}

					database_add(database, opts, entry);
				}
			}
		}
	}

	log("Raw database size: %d\n", GetSize(database));
	if (N != 0) {
		database_reduce(database, opts, N);
		log("Reduced database size: %d\n", GetSize(database));
	}

	std::ofstream fout;

	if (!filename.empty()) {
		fout.open(filename, std::ios::out | std::ios::trunc);
		if (!fout.is_open())
			log_error("Could not open file \"%s\" with write access.\n", filename.c_str());
	}

	for (auto &entry : database) {
		string str = stringf("mutate -mode %s", entry.mode.c_str());
		if (!entry.modname.empty())
			str += stringf(" -module %s", log_id(entry.modname));
		if (!entry.cellname.empty())
			str += stringf(" -cell %s", log_id(entry.cellname));
		if (!entry.cellport.empty())
			str += stringf(" -port %s", log_id(entry.cellport));
		if (entry.portbit >= 0)
			str += stringf(" -bit %d", entry.portbit);
		if (entry.outsigbit.wire || !entry.src.empty()) {
			str += " #";
			if (!entry.src.empty())
				str += stringf(" %s", entry.src.c_str());
			if (entry.outsigbit.wire)
				str += stringf(" %s", log_signal(entry.outsigbit));
		}
		if (filename.empty())
			log("%s\n", str.c_str());
		else
			fout << str << std::endl;
	}
}

SigSpec mutate_ctrl_sig(Module *module, IdString name, int width)
{
	Wire *ctrl_wire = module->wire(name);

	if (ctrl_wire == nullptr)
	{
		log("Adding ctrl port %s to module %s.\n", log_id(name), log_id(module));

		ctrl_wire = module->addWire(name, width);
		ctrl_wire->port_input = true;
		module->fixup_ports();

		for (auto mod : module->design->modules())
		for (auto cell : mod->cells())
		{
			if (cell->type != module->name)
				continue;

			SigSpec ctrl = mutate_ctrl_sig(mod, name, width);

			log("Connecting ctrl port to cell %s in module %s.\n", log_id(cell), log_id(mod));
			cell->setPort(name, ctrl);
		}
	}

	log_assert(GetSize(ctrl_wire) == width);
	return ctrl_wire;
}

SigBit mutate_ctrl(Module *module, const mutate_opts_t &opts)
{
	if (opts.ctrl_name.empty())
		return State::S1;

	SigSpec sig = mutate_ctrl_sig(module, opts.ctrl_name, opts.ctrl_width);
	return module->Eq(NEW_ID, sig, Const(opts.ctrl_value, GetSize(sig)));
}

SigSpec mutate_ctrl_mux(Module *module, const mutate_opts_t &opts, SigSpec unchanged_sig, SigSpec changed_sig)
{
	SigBit ctrl_bit = mutate_ctrl(module, opts);
	if (ctrl_bit == State::S0)
		return unchanged_sig;
	if (ctrl_bit == State::S1)
		return changed_sig;
	return module->Mux(NEW_ID, unchanged_sig, changed_sig, ctrl_bit);
}

void mutate_inv(Design *design, const mutate_opts_t &opts)
{
	Module *module = design->module(opts.module);
	Cell *cell = module->cell(opts.cell);

	SigBit bit = cell->getPort(opts.port)[opts.bit];
	SigBit inbit, outbit;

	if (cell->input(opts.port))
	{
		log("Add input inverter at %s.%s.%s[%d].\n", log_id(module), log_id(cell), log_id(opts.port), opts.bit);
		SigBit outbit = module->Not(NEW_ID, bit);
		bit = mutate_ctrl_mux(module, opts, bit, outbit);
	}
	else
	{
		log("Add output inverter at %s.%s.%s[%d].\n", log_id(module), log_id(cell), log_id(opts.port), opts.bit);
		SigBit inbit = module->addWire(NEW_ID);
		SigBit outbit = module->Not(NEW_ID, inbit);
		module->connect(bit, mutate_ctrl_mux(module, opts, inbit, outbit));
		bit = inbit;
	}

	SigSpec s = cell->getPort(opts.port);
	s[opts.bit] = bit;
	cell->setPort(opts.port, s);
}

struct MutatePass : public Pass {
	MutatePass() : Pass("mutate", "generate or apply design mutations") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    mutate -list N [options] [selection]\n");
		log("\n");
		log("Create a list of N mutations using an even sampling.\n");
		log("\n");
		log("    -o filename\n");
		log("        Write list to this file instead of console output\n");
		log("\n");
		log("    -mode name\n");
		log("    -module name\n");
		log("    -cell name\n");
		log("    -port name\n");
		log("    -bit int\n");
		log("        Filter list of mutation candidates to those matching\n");
		log("        the given parameters.\n");
		log("\n");
		log("\n");
		log("    mutate -mode MODE [options]\n");
		log("\n");
		log("Apply the given mutation.\n");
		log("\n");
		log("    -ctrl name width value\n");
		log("        Add a control signal with the given name and width. The mutation is\n");
		log("        activated if the control signal equals the given value.\n");
		log("\n");
		log("    -module name\n");
		log("    -cell name\n");
		log("    -port name\n");
		log("    -bit int\n");
		log("        Mutation parameters, as generated by 'mutate -list N'.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		mutate_opts_t opts;
		string filename;
		int N = -1;

		log_header(design, "Executing MUTATE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-list" && argidx+1 < args.size()) {
				N = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-o" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-mode" && argidx+1 < args.size()) {
				opts.mode = args[++argidx];
				continue;
			}
			if (args[argidx] == "-ctrl" && argidx+3 < args.size()) {
				opts.ctrl_name = RTLIL::escape_id(args[++argidx]);
				opts.ctrl_width = atoi(args[++argidx].c_str());
				opts.ctrl_value = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-module" && argidx+1 < args.size()) {
				opts.module = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-cell" && argidx+1 < args.size()) {
				opts.cell = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-port" && argidx+1 < args.size()) {
				opts.port = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-bit" && argidx+1 < args.size()) {
				opts.bit = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (N >= 0) {
			mutate_list(design, opts, filename, N);
			return;
		}

		if (opts.mode == "inv") {
			mutate_inv(design, opts);
			return;
		}

		log_cmd_error("Invalid mode: %s\n", opts.mode.c_str());
	}
} MutatePass;

PRIVATE_NAMESPACE_END
