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
#include "kernel/consteval.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ExtractFaConfig
{
	bool enable_fa = false;
	bool enable_ha = false;
	bool verbose = false;
	int maxdepth = 20;
	int maxbreadth = 6;
};

// http://svn.clifford.at/handicraft/2016/bindec/bindec.c
int bindec(unsigned char v)
{
	int r = v & 1;
	r += (~((v & 2) - 1)) & 10;
	r += (~((v & 4) - 1)) & 100;
	r += (~((v & 8) - 1)) & 1000;
	r += (~((v & 16) - 1)) & 10000;
	r += (~((v & 32) - 1)) & 100000;
	r += (~((v & 64) - 1)) & 1000000;
	r += (~((v & 128) - 1)) & 10000000;
	return r;
}

struct ExtractFaWorker
{
	const ExtractFaConfig &config;
	Module *module;
	ConstEval ce;
	SigMap &sigmap;

	dict<SigBit, Cell*> driver;
	pool<SigBit> handled_bits;

	const int xor2_func = 0x6, xnor2_func = 0x9;
	const int xor3_func = 0x96, xnor3_func = 0x69;

	pool<tuple<SigBit, SigBit>> xorxnor2;
	pool<tuple<SigBit, SigBit, SigBit>> xorxnor3;

	dict<tuple<SigBit, SigBit>, dict<int, pool<SigBit>>> func2;
	dict<tuple<SigBit, SigBit, SigBit>, dict<int, pool<SigBit>>> func3;

	int count_func2;
	int count_func3;

	struct func2_and_info_t {
		bool inv_a, inv_b, inv_y;
	};

	struct func3_maj_info_t {
		bool inv_a, inv_b, inv_c, inv_y;
	};

	dict<int, func2_and_info_t> func2_and_info;
	dict<int, func3_maj_info_t> func3_maj_info;

	ExtractFaWorker(const ExtractFaConfig &config, Module *module) :
			config(config), module(module), ce(module), sigmap(ce.assign_map)
	{
		for (auto cell : module->selected_cells())
		{
			if (cell->type.in( ID($_BUF_), ID($_NOT_), ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_),
					ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_), ID($_MUX_), ID($_NMUX_),
					ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_)))
			{
				SigBit y = sigmap(SigBit(cell->getPort(ID::Y)));
				log_assert(driver.count(y) == 0);
				driver[y] = cell;
			}
		}

		for (int ia = 0; ia < 2; ia++)
		for (int ib = 0; ib < 2; ib++)
		{
			func2_and_info_t f2i;

			f2i.inv_a = ia;
			f2i.inv_b = ib;
			f2i.inv_y = false;

			int func = 0;
			for (int i = 0; i < 4; i++)
			{
				bool a = (i & 1) ? !f2i.inv_a : f2i.inv_a;
				bool b = (i & 2) ? !f2i.inv_b : f2i.inv_b;
				if (a && b) func |= 1 << i;
			}

			log_assert(func2_and_info.count(func) == 0);
			func2_and_info[func] = f2i;

			f2i.inv_y = true;
			func ^= 15;

			log_assert(func2_and_info.count(func) == 0);
			func2_and_info[func] = f2i;
		}

		for (int ia = 0; ia < 2; ia++)
		for (int ib = 0; ib < 2; ib++)
		for (int ic = 0; ic < 2; ic++)
		{
			func3_maj_info_t f3i;

			f3i.inv_a = ia;
			f3i.inv_b = ib;
			f3i.inv_c = ic;
			f3i.inv_y = false;

			int func = 0;
			for (int i = 0; i < 8; i++)
			{
				bool a = (i & 1) ? !f3i.inv_a : f3i.inv_a;
				bool b = (i & 2) ? !f3i.inv_b : f3i.inv_b;
				bool c = (i & 4) ? !f3i.inv_c : f3i.inv_c;
				if ((a && b) || (a && c) || (b &&c)) func |= 1 << i;
			}

			log_assert(func3_maj_info.count(func) == 0);
			func3_maj_info[func] = f3i;

			// f3i.inv_y = true;
			// func ^= 255;

			// log_assert(func3_maj_info.count(func) == 0);
			// func3_maj_info[func] = f3i;
		}
	}

	void check_partition(SigBit root, pool<SigBit> &leaves)
	{
		if (config.enable_ha && GetSize(leaves) == 2)
		{
			leaves.sort();

			SigBit A = SigSpec(leaves)[0];
			SigBit B = SigSpec(leaves)[1];

			int func = 0;
			for (int i = 0; i < 4; i++)
			{
				bool a_value = (i & 1) != 0;
				bool b_value = (i & 2) != 0;

				ce.push();
				ce.set(A, a_value ? State::S1 : State::S0);
				ce.set(B, b_value ? State::S1 : State::S0);

				SigSpec sig = root;

				if (!ce.eval(sig)) {
					ce.pop();
					return;
				}

				if (sig == State::S1)
					func |= 1 << i;

				ce.pop();
			}

			// log("%04d %s %s -> %s\n", bindec(func), log_signal(A), log_signal(B), log_signal(root));

			if (func == xor2_func || func == xnor2_func)
				xorxnor2.insert(tuple<SigBit, SigBit>(A, B));

			count_func2++;
			func2[tuple<SigBit, SigBit>(A, B)][func].insert(root);
		}

		if (config.enable_fa && GetSize(leaves) == 3)
		{
			leaves.sort();

			SigBit A = SigSpec(leaves)[0];
			SigBit B = SigSpec(leaves)[1];
			SigBit C = SigSpec(leaves)[2];

			int func = 0;
			for (int i = 0; i < 8; i++)
			{
				bool a_value = (i & 1) != 0;
				bool b_value = (i & 2) != 0;
				bool c_value = (i & 4) != 0;

				ce.push();
				ce.set(A, a_value ? State::S1 : State::S0);
				ce.set(B, b_value ? State::S1 : State::S0);
				ce.set(C, c_value ? State::S1 : State::S0);

				SigSpec sig = root;

				if (!ce.eval(sig)) {
					ce.pop();
					return;
				}

				if (sig == State::S1)
					func |= 1 << i;

				ce.pop();
			}

			// log("%08d %s %s %s -> %s\n", bindec(func), log_signal(A), log_signal(B), log_signal(C), log_signal(root));

			if (func == xor3_func || func == xnor3_func)
				xorxnor3.insert(tuple<SigBit, SigBit, SigBit>(A, B, C));

			count_func3++;
			func3[tuple<SigBit, SigBit, SigBit>(A, B, C)][func].insert(root);
		}
	}

	void find_partitions(SigBit root, pool<SigBit> &leaves, pool<pool<SigBit>> &cache, int maxdepth, int maxbreadth)
	{
		if (cache.count(leaves))
			return;

		// log("%*s[%d] %s:", 20-maxdepth, "", maxdepth, log_signal(root));
		// for (auto bit : leaves)
		// 	log(" %s", log_signal(bit));
		// log("\n");

		cache.insert(leaves);
		check_partition(root, leaves);

		if (maxdepth == 0)
			return;

		for (SigBit bit : leaves)
		{
			if (driver.count(bit) == 0)
				continue;

			Cell *cell = driver.at(bit);
			pool<SigBit> new_leaves = leaves;

			new_leaves.erase(bit);
			for (auto port : {ID::A, ID::B, ID(C), ID(D)}) {
				if (!cell->hasPort(port))
					continue;
				auto bit = sigmap(SigBit(cell->getPort(port)));
				if (!bit.wire)
					continue;
				new_leaves.insert(bit);
			}

			if (GetSize(new_leaves) > maxbreadth)
				continue;

			find_partitions(root, new_leaves, cache, maxdepth-1, maxbreadth);
		}
	}

	void assign_new_driver(SigBit bit, SigBit new_driver)
	{
		Cell *cell = driver.at(bit);
		if (sigmap(cell->getPort(ID::Y)) == bit) {
			cell->setPort(ID::Y, module->addWire(NEW_ID));
			module->connect(bit, new_driver);
		}
	}

	void run()
	{
		log("Extracting full/half adders from %s:\n", log_id(module));

		for (auto it : driver)
		{
			if (it.second->type.in(ID($_BUF_), ID($_NOT_)))
				continue;

			SigBit root = it.first;
			pool<SigBit> leaves = { root };
			pool<pool<SigBit>> cache;

			if (config.verbose)
				log("  checking %s\n", log_signal(it.first));

			count_func2 = 0;
			count_func3 = 0;

			find_partitions(root, leaves, cache, config.maxdepth, config.maxbreadth);

			if (config.verbose && count_func2 > 0)
				log("    extracted %d two-input functions\n", count_func2);

			if (config.verbose && count_func3 > 0)
				log("    extracted %d three-input functions\n", count_func3);
		}

		for (auto &key : xorxnor3)
		{
			SigBit A = get<0>(key);
			SigBit B = get<1>(key);
			SigBit C = get<2>(key);

			log("  3-Input XOR/XNOR %s %s %s:\n", log_signal(A), log_signal(B), log_signal(C));

			for (auto &it : func3.at(key))
			{
				if (it.first != xor3_func && it.first != xnor3_func)
					continue;

				log("      %08d ->", bindec(it.first));
				for (auto bit : it.second)
					log(" %s", log_signal(bit));
				log("\n");
			}

			dict<int, tuple<SigBit, SigBit, Cell*>> facache;

			for (auto &it : func3_maj_info)
			{
				int func = it.first;
				auto f3i = it.second;

				if (func3.at(key).count(func) == 0)
					continue;

				if (func3.at(key).count(xor3_func) == 0 && func3.at(key).count(xnor3_func) != 0) {
					f3i.inv_a = !f3i.inv_a;
					f3i.inv_b = !f3i.inv_b;
					f3i.inv_c = !f3i.inv_c;
					f3i.inv_y = !f3i.inv_y;
				}

				if (!f3i.inv_a && !f3i.inv_b && !f3i.inv_c && !f3i.inv_y) {
					log("    Majority without inversions:\n");
				} else {
					log("    Majority with inverted");
					if (f3i.inv_a) log(" A");
					if (f3i.inv_b) log(" B");
					if (f3i.inv_c) log(" C");
					if (f3i.inv_y) log(" Y");
					log(":\n");
				}

				log("      %08d ->", bindec(func));
				for (auto bit : func3.at(key).at(func))
					log(" %s", log_signal(bit));
				log("\n");

				int fakey = 0;
				if (f3i.inv_a) fakey |= 1;
				if (f3i.inv_b) fakey |= 2;
				if (f3i.inv_c) fakey |= 4;

				int fakey_inv = fakey ^ 7;
				bool invert_xy = false;
				SigBit X, Y;

				if (facache.count(fakey))
				{
					auto &fa = facache.at(fakey);
					X = get<0>(fa);
					Y = get<1>(fa);
					log("      Reusing $fa cell %s.\n", log_id(get<2>(fa)));
				}
				else
				if (facache.count(fakey_inv))
				{
					auto &fa = facache.at(fakey_inv);
					invert_xy = true;
					X = get<0>(fa);
					Y = get<1>(fa);
					log("      Reusing $fa cell %s.\n", log_id(get<2>(fa)));
				}
				else
				{
					Cell *cell = module->addCell(NEW_ID, ID($fa));
					cell->setParam(ID(WIDTH), 1);

					log("      Created $fa cell %s.\n", log_id(cell));

					cell->setPort(ID::A, f3i.inv_a ? module->NotGate(NEW_ID, A) : A);
					cell->setPort(ID::B, f3i.inv_b ? module->NotGate(NEW_ID, B) : B);
					cell->setPort(ID(C), f3i.inv_c ? module->NotGate(NEW_ID, C) : C);

					X = module->addWire(NEW_ID);
					Y = module->addWire(NEW_ID);

					cell->setPort(ID(X), X);
					cell->setPort(ID::Y, Y);

					facache[fakey] = make_tuple(X, Y, cell);
				}

				if (func3.at(key).count(xor3_func)) {
					SigBit YY = invert_xy ? module->NotGate(NEW_ID, Y) : Y;
					for (auto bit : func3.at(key).at(xor3_func))
						assign_new_driver(bit, YY);
				}

				if (func3.at(key).count(xnor3_func)) {
					SigBit YY = invert_xy ? Y : module->NotGate(NEW_ID, Y);
					for (auto bit : func3.at(key).at(xnor3_func))
						assign_new_driver(bit, YY);
				}

				SigBit XX = invert_xy != f3i.inv_y ? module->NotGate(NEW_ID, X) : X;

				for (auto bit : func3.at(key).at(func))
					assign_new_driver(bit, XX);
			}
		}

		for (auto &key : xorxnor2)
		{
			SigBit A = get<0>(key);
			SigBit B = get<1>(key);

			log("  2-Input XOR/XNOR %s %s:\n", log_signal(A), log_signal(B));

			for (auto &it : func2.at(key))
			{
				if (it.first != xor2_func && it.first != xnor2_func)
					continue;

				log("    %04d ->", bindec(it.first));
				for (auto bit : it.second)
					log(" %s", log_signal(bit));
				log("\n");
			}

			dict<int, tuple<SigBit, SigBit, Cell*>> facache;

			for (auto &it : func2_and_info)
			{
				int func = it.first;
				auto &f2i = it.second;

				if (func2.at(key).count(func) == 0)
					continue;

				if (!f2i.inv_a && !f2i.inv_b && !f2i.inv_y) {
					log("    AND without inversions:\n");
				} else {
					log("    AND with inverted");
					if (f2i.inv_a) log(" A");
					if (f2i.inv_b) log(" B");
					if (f2i.inv_y) log(" Y");
					log(":\n");
				}

				log("      %04d ->", bindec(func));
				for (auto bit : func2.at(key).at(func))
					log(" %s", log_signal(bit));
				log("\n");

				int fakey = 0;
				if (f2i.inv_a) fakey |= 1;
				if (f2i.inv_b) fakey |= 2;

				int fakey_inv = fakey ^ 3;
				bool invert_xy = false;
				SigBit X, Y;

				if (facache.count(fakey))
				{
					auto &fa = facache.at(fakey);
					X = get<0>(fa);
					Y = get<1>(fa);
					log("      Reusing $fa cell %s.\n", log_id(get<2>(fa)));
				}
				else
				if (facache.count(fakey_inv))
				{
					auto &fa = facache.at(fakey_inv);
					invert_xy = true;
					X = get<0>(fa);
					Y = get<1>(fa);
					log("      Reusing $fa cell %s.\n", log_id(get<2>(fa)));
				}
				else
				{
					Cell *cell = module->addCell(NEW_ID, ID($fa));
					cell->setParam(ID(WIDTH), 1);

					log("      Created $fa cell %s.\n", log_id(cell));

					cell->setPort(ID::A, f2i.inv_a ? module->NotGate(NEW_ID, A) : A);
					cell->setPort(ID::B, f2i.inv_b ? module->NotGate(NEW_ID, B) : B);
					cell->setPort(ID(C), State::S0);

					X = module->addWire(NEW_ID);
					Y = module->addWire(NEW_ID);

					cell->setPort(ID(X), X);
					cell->setPort(ID::Y, Y);
				}

				if (func2.at(key).count(xor2_func)) {
					SigBit YY = invert_xy || (f2i.inv_a && !f2i.inv_b) || (!f2i.inv_a && f2i.inv_b) ? module->NotGate(NEW_ID, Y) : Y;
					for (auto bit : func2.at(key).at(xor2_func))
						assign_new_driver(bit, YY);
				}

				if (func2.at(key).count(xnor2_func)) {
					SigBit YY = invert_xy || (f2i.inv_a && !f2i.inv_b) || (!f2i.inv_a && f2i.inv_b) ? Y : module->NotGate(NEW_ID, Y);
					for (auto bit : func2.at(key).at(xnor2_func))
						assign_new_driver(bit, YY);
				}

				SigBit XX = invert_xy != f2i.inv_y ? module->NotGate(NEW_ID, X) : X;

				for (auto bit : func2.at(key).at(func))
					assign_new_driver(bit, XX);
			}
		}
	}
};

struct ExtractFaPass : public Pass {
	ExtractFaPass() : Pass("extract_fa", "find and extract full/half adders") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    extract_fa [options] [selection]\n");
		log("\n");
		log("This pass extracts full/half adders from a gate-level design.\n");
		log("\n");
		log("    -fa, -ha\n");
		log("        Enable cell types (fa=full adder, ha=half adder)\n");
		log("        All types are enabled if none of this options is used\n");
		log("\n");
		log("    -d <int>\n");
		log("        Set maximum depth for extracted logic cones (default=20)\n");
		log("\n");
		log("    -b <int>\n");
		log("        Set maximum breadth for extracted logic cones (default=6)\n");
		log("\n");
		log("    -v\n");
		log("        Verbose output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		ExtractFaConfig config;

		log_header(design, "Executing EXTRACT_FA pass (find and extract full/half adders).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-fa") {
				config.enable_fa = true;
				continue;
			}
			if (args[argidx] == "-ha") {
				config.enable_ha = true;
				continue;
			}
			if (args[argidx] == "-v") {
				config.verbose = true;
				continue;
			}
			if (args[argidx] == "-d" && argidx+2 < args.size()) {
				config.maxdepth = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-b" && argidx+2 < args.size()) {
				config.maxbreadth = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!config.enable_fa && !config.enable_ha) {
			config.enable_fa = true;
			config.enable_ha = true;
		}

		for (auto module : design->selected_modules())
		{
			ExtractFaWorker worker(config, module);
			worker.run();
		}

		log_pop();
	}
} ExtractFaPass;

PRIVATE_NAMESPACE_END
