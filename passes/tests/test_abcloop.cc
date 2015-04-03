/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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
#include "kernel/satgen.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static uint32_t xorshift32_state = 123456789;

static uint32_t xorshift32(uint32_t limit) {
	xorshift32_state ^= xorshift32_state << 13;
	xorshift32_state ^= xorshift32_state >> 17;
	xorshift32_state ^= xorshift32_state << 5;
	return xorshift32_state % limit;
}

static RTLIL::Wire *getw(std::vector<RTLIL::Wire*> &wires, RTLIL::Wire *w)
{
	while (1) {
		int idx = xorshift32(GetSize(wires));
		if (wires[idx] != w && !wires[idx]->port_output)
			return wires[idx];
	}
}

static void test_abcloop()
{
	log("Rng seed value: %u\n", int(xorshift32_state));

	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module = nullptr;
	RTLIL::SigSpec in_sig, out_sig;

	bool truthtab[16][4];
	int create_cycles = 0;

	while (1)
	{
		module = design->addModule("\\uut");
		create_cycles++;

		in_sig = {};
		out_sig = {};

		std::vector<RTLIL::Wire*> wires;

		for (int i = 0; i < 4; i++) {
			RTLIL::Wire *w = module->addWire(stringf("\\i%d", i));
			w->port_input = true;
			wires.push_back(w);
			in_sig.append(w);
		}

		for (int i = 0; i < 4; i++) {
			RTLIL::Wire *w = module->addWire(stringf("\\o%d", i));
			w->port_output = true;
			wires.push_back(w);
			out_sig.append(w);
		}

		for (int i = 0; i < 16; i++) {
			RTLIL::Wire *w = module->addWire(stringf("\\t%d", i));
			wires.push_back(w);
		}

		for (auto w : wires)
			if (!w->port_input)
				switch (xorshift32(12))
				{
				case 0:
					module->addNotGate(w->name.str() + "g", getw(wires, w), w);
					break;
				case 1:
					module->addAndGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 2:
					module->addNandGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 3:
					module->addOrGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 4:
					module->addNorGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 5:
					module->addXorGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 6:
					module->addXnorGate(w->name.str() + "g", getw(wires, w), getw(wires, w), w);
					break;
				case 7:
					module->addMuxGate(w->name.str() + "g", getw(wires, w), getw(wires, w), getw(wires, w), w);
					break;
				case 8:
					module->addAoi3Gate(w->name.str() + "g", getw(wires, w), getw(wires, w), getw(wires, w), w);
					break;
				case 9:
					module->addOai3Gate(w->name.str() + "g", getw(wires, w), getw(wires, w), getw(wires, w), w);
					break;
				case 10:
					module->addAoi4Gate(w->name.str() + "g", getw(wires, w), getw(wires, w), getw(wires, w), getw(wires, w), w);
					break;
				case 11:
					module->addOai4Gate(w->name.str() + "g", getw(wires, w), getw(wires, w), getw(wires, w), getw(wires, w), w);
					break;
				}

		module->fixup_ports();
		Pass::call(design, "clean");

		ezSatPtr ez;
		SigMap sigmap(module);
		SatGen satgen(ez.get(), &sigmap);

		for (auto c : module->cells()) {
			bool ok YS_ATTRIBUTE(unused) = satgen.importCell(c);
			log_assert(ok);
		}

		std::vector<int> in_vec = satgen.importSigSpec(in_sig);
		std::vector<int> inverse_in_vec = ez->vec_not(in_vec);

		std::vector<int> out_vec = satgen.importSigSpec(out_sig);

		for (int i = 0; i < 16; i++)
		{
			std::vector<int> assumptions;
			for (int j = 0; j < GetSize(in_vec); j++)
				assumptions.push_back((i & (1 << j)) ? in_vec.at(j) : inverse_in_vec.at(j));

			std::vector<bool> results;
			if (!ez->solve(out_vec, results, assumptions)) {
				log("No stable solution for input %d found -> recreate module.\n", i);
				goto recreate_module;
			}

			for (int j = 0; j < 4; j++)
				truthtab[i][j] = results[j];

			assumptions.push_back(ez->vec_ne(out_vec, ez->vec_const(results)));

			std::vector<bool> results2;
			if (ez->solve(out_vec, results2, assumptions)) {
				log("Two stable solutions for input %d found -> recreate module.\n", i);
				goto recreate_module;
			}
		}
		break;

	recreate_module:
		design->remove(module);
	}

	log("Found viable UUT after %d cycles:\n", create_cycles);
	Pass::call(design, "write_ilang");
	Pass::call(design, "abc");

	log("\n");
	log("Pre- and post-abc truth table:\n");

	ezSatPtr ez;
	SigMap sigmap(module);
	SatGen satgen(ez.get(), &sigmap);

	for (auto c : module->cells()) {
		bool ok YS_ATTRIBUTE(unused) = satgen.importCell(c);
		log_assert(ok);
	}

	std::vector<int> in_vec = satgen.importSigSpec(in_sig);
	std::vector<int> inverse_in_vec = ez->vec_not(in_vec);

	std::vector<int> out_vec = satgen.importSigSpec(out_sig);

	bool found_error = false;
	bool truthtab2[16][4];

	for (int i = 0; i < 16; i++)
	{
		std::vector<int> assumptions;
		for (int j = 0; j < GetSize(in_vec); j++)
			assumptions.push_back((i & (1 << j)) ? in_vec.at(j) : inverse_in_vec.at(j));

		for (int j = 0; j < 4; j++)
			truthtab2[i][j] = truthtab[i][j];

		std::vector<bool> results;
		if (!ez->solve(out_vec, results, assumptions)) {
			log("No stable solution for input %d found.\n", i);
			found_error = true;
			continue;
		}

		for (int j = 0; j < 4; j++)
			truthtab2[i][j] = results[j];

		assumptions.push_back(ez->vec_ne(out_vec, ez->vec_const(results)));

		std::vector<bool> results2;
		if (ez->solve(out_vec, results2, assumptions)) {
			log("Two stable solutions for input %d found -> recreate module.\n", i);
			found_error = true;
		}
	}

	for (int i = 0; i < 16; i++) {
		log("%3d ", i);
		for (int j = 0; j < 4; j++)
			log("%c", truthtab[i][j] ? '1' : '0');
		log(" ");
		for (int j = 0; j < 4; j++)
			log("%c", truthtab2[i][j] ? '1' : '0');
		for (int j = 0; j < 4; j++)
			if (truthtab[i][j] != truthtab2[i][j]) {
				found_error = true;
				log(" !");
				break;
			}
		log("\n");
	}

	log_assert(found_error == false);
	log("\n");
}

struct TestAbcloopPass : public Pass {
	TestAbcloopPass() : Pass("test_abcloop", "automatically test handling of loops in abc command") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_abcloop [options]\n");
		log("\n");
		log("Test handling of logic loops in ABC.\n");
		log("\n");
		log("    -n {integer}\n");
		log("        create this number of circuits and test them (default = 100).\n");
		log("\n");
		log("    -s {positive_integer}\n");
		log("        use this value as rng seed value (default = unix time).\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design*)
	{
		int num_iter = 100;
		xorshift32_state = 0;

		int argidx;
		for (argidx = 1; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-n" && argidx+1 < GetSize(args)) {
				num_iter = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-s" && argidx+1 < GetSize(args)) {
				xorshift32_state = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}

		if (xorshift32_state == 0)
			xorshift32_state = time(NULL) & 0x7fffffff;

		for (int i = 0; i < num_iter; i++)
			test_abcloop();
	}
} TestAbcloopPass;

PRIVATE_NAMESPACE_END
