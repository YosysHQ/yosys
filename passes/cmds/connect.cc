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

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void unset_drivers(RTLIL::Design *design, RTLIL::Module *module, SigMap &sigmap, RTLIL::SigSpec &sig)
{
	CellTypes ct(design);

	RTLIL::Wire *dummy_wire = module->addWire(NEW_ID, sig.size());

	for (auto cell : module->cells())
	for (auto &port : cell->connections_)
		if (ct.cell_output(cell->type, port.first))
			sigmap(port.second).replace(sig, dummy_wire, &port.second);

	for (auto &conn : module->connections_)
		sigmap(conn.first).replace(sig, dummy_wire, &conn.first);
}

struct ConnectPass : public Pass {
	ConnectPass() : Pass("connect", "create or remove connections") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    connect [-nomap] [-nounset] -set <lhs-expr> <rhs-expr> [selection]\n");
		log("\n");
		log("Create a connection. This is equivalent to adding the statement 'assign\n");
		log("<lhs-expr> = <rhs-expr>;' to the Verilog input. Per default, all existing\n");
		log("drivers for <lhs-expr> are unconnected. This can be overwritten by using\n");
		log("the -nounset option.\n");
		log("\n");
		log("\n");
		log("    connect [-nomap] -unset <expr> [selection]\n");
		log("\n");
		log("Unconnect all existing drivers for the specified expression.\n");
		log("\n");
		log("\n");
		log("    connect [-nomap] [-assert] -port <cell> <port> <expr> [selection]\n");
		log("\n");
		log("Connect the specified cell port to the specified cell port.\n");
		log("\n");
		log("\n");
		log("Per default signal alias names are resolved and all signal names are mapped\n");
		log("the the signal name of the primary driver. Using the -nomap option deactivates\n");
		log("this behavior.\n");
		log("\n");
		log("The connect command operates in one module only. Either only one module must\n");
		log("be selected or an active module must be set using the 'cd' command.\n");
		log("\n");
		log("The -assert option verifies that the connection already exists, instead of\n");
		log("making it.\n");
		log("\n");
		log("This command does not operate on module with processes.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_nounset = false, flag_nomap = false, flag_assert = false;
		std::string set_lhs, set_rhs, unset_expr;
		std::string port_cell, port_port, port_expr;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-nounset") {
				flag_nounset = true;
				continue;
			}
			if (arg == "-nomap") {
				flag_nomap = true;
				continue;
			}
			if (arg == "-assert") {
				flag_assert = true;
				continue;
			}
			if (arg == "-set" && argidx+2 < args.size()) {
				set_lhs = args[++argidx];
				set_rhs = args[++argidx];
				continue;
			}
			if (arg == "-unset" && argidx+1 < args.size()) {
				unset_expr = args[++argidx];
				continue;
			}
			if (arg == "-port" && argidx+3 < args.size()) {
				port_cell = args[++argidx];
				port_port = args[++argidx];
				port_expr = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = nullptr;
		for (auto mod : design->selected_modules()) {
			if (module != nullptr)
				log_cmd_error("Multiple modules selected: %s, %s\n", log_id(module->name), log_id(mod->name));
			module = mod;
		}
		if (module == nullptr)
			log_cmd_error("No modules selected.\n");
		if (!module->processes.empty())
			log_cmd_error("Found processes in selected module.\n");

		SigMap sigmap;
		if (!flag_nomap)
			for (auto &it : module->connections()) {
				std::vector<RTLIL::SigBit> lhs = it.first.to_sigbit_vector();
				std::vector<RTLIL::SigBit> rhs = it.second.to_sigbit_vector();
				for (size_t i = 0; i < lhs.size(); i++)
					if (rhs[i].wire != nullptr)
						sigmap.add(lhs[i], rhs[i]);
			}

		if (!set_lhs.empty())
		{
			if (!unset_expr.empty() || !port_cell.empty())
				log_cmd_error("Can't use -set together with -unset and/or -port.\n");

			if (flag_assert)
				log_cmd_error("The -assert option is only supported with -port.\n");

			RTLIL::SigSpec sig_lhs, sig_rhs;
			if (!RTLIL::SigSpec::parse_sel(sig_lhs, design, module, set_lhs))
				log_cmd_error("Failed to parse set lhs expression `%s'.\n", set_lhs.c_str());
			if (!RTLIL::SigSpec::parse_rhs(sig_lhs, sig_rhs, module, set_rhs))
				log_cmd_error("Failed to parse set rhs expression `%s'.\n", set_rhs.c_str());

			sigmap.apply(sig_lhs);
			sigmap.apply(sig_rhs);

			if (!flag_nounset)
				unset_drivers(design, module, sigmap, sig_lhs);

			module->connect(RTLIL::SigSig(sig_lhs, sig_rhs));
		}
		else
		if (!unset_expr.empty())
		{
			if (!port_cell.empty() || flag_nounset)
				log_cmd_error("Can't use -unset together with -port and/or -nounset.\n");

			if (flag_assert)
				log_cmd_error("The -assert option is only supported with -port.\n");

			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, unset_expr))
				log_cmd_error("Failed to parse unset expression `%s'.\n", unset_expr.c_str());

			sigmap.apply(sig);
			unset_drivers(design, module, sigmap, sig);
		}
		else
		if (!port_cell.empty())
		{
			if (flag_nounset)
				log_cmd_error("Can't use -port together with -nounset.\n");

			if (module->cell(RTLIL::escape_id(port_cell)) == nullptr)
				log_cmd_error("Can't find cell %s.\n", port_cell.c_str());

			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, port_expr))
				log_cmd_error("Failed to parse port expression `%s'.\n", port_expr.c_str());

			if (!flag_assert) {
				module->cell(RTLIL::escape_id(port_cell))->setPort(RTLIL::escape_id(port_port), sigmap(sig));
			} else {
				SigSpec cur = module->cell(RTLIL::escape_id(port_cell))->getPort(RTLIL::escape_id(port_port));
				if (sigmap(sig) != sigmap(cur)) {
					log_cmd_error("Expected connection not present: expected %s, found %s.\n", log_signal(sig), log_signal(cur));
				}
			}
		}
		else
			log_cmd_error("Expected -set, -unset, or -port.\n");
	}
} ConnectPass;

PRIVATE_NAMESPACE_END
