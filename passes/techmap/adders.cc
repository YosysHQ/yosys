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

struct AddersConfig
{
	bool enable_fa = false;
	bool enable_ha = false;
	bool enable_fs = false;
	bool enable_hs = false;
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

struct AddersWorker
{
	const AddersConfig &config;
	Module *module;
	ConstEval ce;
	SigMap &sigmap;

	dict<SigBit, Cell*> driver;
	pool<SigBit> handled_bits;

	pool<tuple<SigBit, SigBit>> xorxnor2;
	pool<tuple<SigBit, SigBit, SigBit>> xorxnor3;

	dict<tuple<SigBit, SigBit>, dict<int, pool<SigBit>>> func2;
	dict<tuple<SigBit, SigBit, SigBit>, dict<int, pool<SigBit>>> func3;

	AddersWorker(const AddersConfig &config, Module *module) :
			config(config), module(module), ce(module), sigmap(ce.assign_map)
	{
		for (auto cell : module->selected_cells())
		{
			if (cell->type.in( "$_BUF_", "$_NOT_", "$_AND_", "$_NAND_", "$_OR_", "$_NOR_",
					"$_XOR_", "$_XNOR_", "$_ANDNOT_", "$_ORNOT_", "$_MUX_",
					"$_AOI3_", "$_OAI3_", "$_AOI4_", "$_OAI4_"))
			{
				SigBit y = sigmap(SigBit(cell->getPort("\\Y")));
				log_assert(driver.count(y) == 0);
				driver[y] = cell;
			}
		}
	}

	void check_partition(SigBit root, pool<SigBit> &leaves)
	{
		if (GetSize(leaves) == 2)
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

				if (!ce.eval(sig))
					log_abort();

				if (sig == State::S1)
					func |= 1 << i;

				ce.pop();
			}

			// log("%04d %s %s -> %s\n", bindec(func), log_signal(A), log_signal(B), log_signal(root));

			if (func == 0x6 || func == 0x9)
				xorxnor2.insert(tuple<SigBit, SigBit>(A, B));

			func2[tuple<SigBit, SigBit>(A, B)][func].insert(root);
		}

		if (GetSize(leaves) == 3)
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

				if (!ce.eval(sig))
					log_abort();

				if (sig == State::S1)
					func |= 1 << i;

				ce.pop();
			}

			// log("%08d %s %s %s -> %s\n", bindec(func), log_signal(A), log_signal(B), log_signal(C), log_signal(root));

			if (func == 0x69 || func == 0x96)
				xorxnor3.insert(tuple<SigBit, SigBit, SigBit>(A, B, C));

			func3[tuple<SigBit, SigBit, SigBit>(A, B, C)][func].insert(root);
		}
	}

	void find_partitions(SigBit root, pool<SigBit> &leaves, pool<pool<SigBit>> &cache, int maxdepth, int maxbreadth)
	{
		if (cache.count(leaves))
			return;

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
			if (cell->hasPort("\\A")) new_leaves.insert(sigmap(SigBit(cell->getPort("\\A"))));
			if (cell->hasPort("\\B")) new_leaves.insert(sigmap(SigBit(cell->getPort("\\B"))));
			if (cell->hasPort("\\C")) new_leaves.insert(sigmap(SigBit(cell->getPort("\\C"))));
			if (cell->hasPort("\\D")) new_leaves.insert(sigmap(SigBit(cell->getPort("\\D"))));

			if (GetSize(new_leaves) > maxbreadth)
				continue;

			find_partitions(root, new_leaves, cache, maxdepth-1, maxbreadth);
		}
	}

	void run()
	{
		for (auto it : driver)
		{
			SigBit root = it.first;
			pool<SigBit> leaves = { root };
			pool<pool<SigBit>> cache;

			find_partitions(root, leaves, cache, 5, 10);
		}

		for (auto &key : xorxnor3)
		{
			SigBit A = get<0>(key);
			SigBit B = get<1>(key);
			SigBit C = get<2>(key);

			log("3-Input XOR/XNOR %s %s %s:\n", log_signal(A), log_signal(B), log_signal(C));

			for (auto &it : func3.at(key)) {
				log("    %08d ->", bindec(it.first));
				for (auto bit : it.second)
					log(" %s", log_signal(bit));
				log("\n");
			}
		}

		for (auto &key : xorxnor2)
		{
			SigBit A = get<0>(key);
			SigBit B = get<1>(key);

			log("2-Input XOR/XNOR %s %s:\n", log_signal(A), log_signal(B));

			for (auto &it : func2.at(key)) {
				log("    %04d ->", bindec(it.first));
				for (auto bit : it.second)
					log(" %s", log_signal(bit));
				log("\n");
			}
		}
	}
};

struct AddersPass : public Pass {
	AddersPass() : Pass("adders", "find and extract full/half adders/subtractors") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    adders [options] [selection]\n");
		log("\n");
		log("This pass extracts full/half adders/subtractors from a gate-level design.\n");
		log("\n");
		log("    -fa, -ha, -fs, -hs\n");
		log("        Enable cell types (f=full, h=half, a=adder, s=subtractor)\n");
		log("        All types are enabled if none of this options is used\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		AddersConfig config;

		log_header(design, "Executing ADDERS pass (find and extract full/half adders/subtractors).\n");
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
			if (args[argidx] == "-fs") {
				config.enable_fs = true;
				continue;
			}
			if (args[argidx] == "-hs") {
				config.enable_hs = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!config.enable_fa && !config.enable_ha && !config.enable_fs && !config.enable_hs) {
			config.enable_fa = true;
			config.enable_ha = true;
			config.enable_fs = true;
			config.enable_hs = true;
		}

		for (auto module : design->selected_modules())
		{
			AddersWorker worker(config, module);
			worker.run();
		}

		log_pop();
	}
} AddersPass;

PRIVATE_NAMESPACE_END
