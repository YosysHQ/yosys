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

struct FminitPass : public Pass {
	FminitPass() : Pass("fminit", "set init values/sequences for formal") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fminit [options] <selection>\n");
		log("\n");
		log("This pass creates init constraints (for example for reset sequences) in a formal\n");
		log("model.\n");
		log("\n");
		log("    -seq <signal> <sequence>\n");
		log("        Set sequence using comma-separated list of values, use 'z for\n");
		log("        unconstrained bits. The last value is used for the remainder of the\n");
		log("        trace.\n");
		log("\n");
		log("    -set <signal> <value>\n");
		log("        Add constant value constraint\n");
		log("\n");
		log("    -posedge <signal>\n");
		log("    -negedge <signal>\n");
		log("        Set clock for init sequences\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		vector<pair<string, vector<string>>> initdata;
		vector<pair<string, string>> setdata;
		string clocksignal;
		bool clockedge;

		log_header(design, "Executing FMINIT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-o" && argidx+1 < args.size()) {
			// 	filename = args[++argidx];
			// 	continue;
			// }
			if (args[argidx] == "-seq" && argidx+2 < args.size()) {
				string lhs = args[++argidx];
				string rhs = args[++argidx];
				initdata.push_back(make_pair(lhs, split_tokens(rhs, ",")));
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				string lhs = args[++argidx];
				string rhs = args[++argidx];
				setdata.push_back(make_pair(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-posedge" && argidx+1 < args.size()) {
				clocksignal = args[++argidx];
				clockedge = true;
				continue;
			}
			if (args[argidx] == "-negedge" && argidx+1 < args.size()) {
				clocksignal = args[++argidx];
				clockedge = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Module *module = nullptr;

		for (auto mod : design->selected_modules()) {
			if (module != nullptr)
				log_error("'fminit' requires exactly one module to be selected.\n");
			module = mod;
		}

		if (module == nullptr)
			log_error("'fminit' requires exactly one module to be selected.\n");

		SigSpec clksig;
		if (!clocksignal.empty()) {
			if (!SigSpec::parse(clksig, module, clocksignal))
				log_error("Error parsing expression '%s'.\n", clocksignal.c_str());
		}

		for (auto &it : setdata)
		{
			SigSpec lhs, rhs;

			if (!SigSpec::parse(lhs, module, it.first))
				log_error("Error parsing expression '%s'.\n", it.first.c_str());

			if (!SigSpec::parse_rhs(lhs, rhs, module, it.second))
				log_error("Error parsing expression '%s'.\n", it.second.c_str());

			SigSpec final_lhs, final_rhs;

			for (int i = 0; i < GetSize(rhs); i++)
				if (rhs[i] != State::Sz) {
					final_lhs.append(lhs[i]);
					final_rhs.append(rhs[i]);
				}

			if (!final_lhs.empty()) {
				SigSpec eq = module->Eq(NEW_ID, final_lhs, final_rhs);
				module->addAssume(NEW_ID, eq, State::S1);
			}
		}

		vector<SigSpec> ctrlsig;
		vector<SigSpec> ctrlsig_latched;

		for (auto &it : initdata)
		{
			SigSpec lhs, rhs;

			if (!SigSpec::parse(lhs, module, it.first))
				log_error("Error parsing expression '%s'.\n", it.first.c_str());

			for (int i = 0; i < GetSize(it.second); i++)
			{
				if (i >= GetSize(ctrlsig))
				{
					SigSpec insig = i > 0 ? ctrlsig.at(i-1) : State::S0;

					Wire *outwire = module->addWire(NEW_ID);
					outwire->attributes[ID(init)] = i > 0 ? State::S0 : State::S1;

					if (clksig.empty())
						module->addFf(NEW_ID, insig, outwire);
					else
						module->addDff(NEW_ID, clksig, insig, outwire, clockedge);

					ctrlsig.push_back(outwire);
					ctrlsig_latched.push_back(SigSpec());
				}

				if (i+1 == GetSize(it.second) && ctrlsig_latched[i].empty())
				{
					Wire *ffwire = module->addWire(NEW_ID);
					ffwire->attributes[ID(init)] = State::S0;
					SigSpec outsig = module->Or(NEW_ID, ffwire, ctrlsig[i]);

					if (clksig.empty())
						module->addFf(NEW_ID, outsig, ffwire);
					else
						module->addDff(NEW_ID, clksig, outsig, ffwire, clockedge);

					ctrlsig_latched[i] = outsig;
				}

				SigSpec ctrl = i+1 == GetSize(it.second) ? ctrlsig_latched[i] : ctrlsig[i];

				SigSpec final_lhs, final_rhs;

				if (!SigSpec::parse_rhs(lhs, rhs, module, it.second[i]))
					log_error("Error parsing expression '%s'.\n", it.second[i].c_str());

				for (int i = 0; i < GetSize(rhs); i++)
					if (rhs[i] != State::Sz) {
						final_lhs.append(lhs[i]);
						final_rhs.append(rhs[i]);
					}

				if (!final_lhs.empty()) {
					SigSpec eq = module->Eq(NEW_ID, final_lhs, final_rhs);
					module->addAssume(NEW_ID, eq, ctrl);
				}
			}
		}
	}
} FminitPass;

PRIVATE_NAMESPACE_END
