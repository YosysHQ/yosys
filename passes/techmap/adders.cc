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

struct AddersWorker
{
	const AddersConfig &config;
	Module *module;
	ConstEval ce;
	SigMap &sigmap;

	dict<SigBit, Cell*> driver;
	pool<SigBit> handled_bits;

	dict<tuple<SigBit, SigBit>, pool<SigBit>> part_xor;
	dict<tuple<SigBit, SigBit>, pool<SigBit>> part_and;
	dict<tuple<SigBit, SigBit>, pool<SigBit>> part_andnot;

	dict<tuple<SigBit, SigBit, SigBit>, pool<SigBit>> part_xor3;
	dict<tuple<SigBit, SigBit, SigBit>, pool<SigBit>> part_maj;
	dict<tuple<SigBit, SigBit, SigBit>, pool<SigBit>> part_majnot;

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

			bool is_xor = true;
			bool is_and = true;
			bool is_andnot_a = true;
			bool is_andnot_b = true;

			for (int i = 0; i < 4; i++)
			{
				bool a_value = (i & 1) != 0;
				bool b_value = (i & 2) != 0;
				bool xor_value = a_value != b_value;
				bool and_value = a_value && b_value;
				bool andnot_a_value = !a_value && b_value;
				bool andnot_b_value = a_value && !b_value;

				ce.push();
				ce.set(A, a_value ? State::S1 : State::S0);
				ce.set(B, b_value ? State::S1 : State::S0);

				SigSpec sig = root;

				if (!ce.eval(sig))
					log_abort();

				if (sig != xor_value)
					is_xor = false;

				if (sig != and_value)
					is_and = false;

				if (sig != andnot_a_value)
					is_andnot_a = false;

				if (sig != andnot_b_value)
					is_andnot_b = false;

				ce.pop();
			}

			if (is_xor)
				part_xor[tuple<SigBit, SigBit>(A, B)].insert(root);

			if (is_and)
				part_and[tuple<SigBit, SigBit>(A, B)].insert(root);

			if (is_andnot_a)
				part_andnot[tuple<SigBit, SigBit>(B, A)].insert(root);

			if (is_andnot_b)
				part_andnot[tuple<SigBit, SigBit>(A, B)].insert(root);
		}

		if (GetSize(leaves) == 3)
		{
			leaves.sort();

			SigBit A = SigSpec(leaves)[0];
			SigBit B = SigSpec(leaves)[1];
			SigBit C = SigSpec(leaves)[2];

			bool is_xor3 = true;
			bool is_maj = true;
			bool is_maj_nota = true;
			bool is_maj_notb = true;
			bool is_maj_notc = true;

			for (int i = 0; i < 8; i++)
			{
				bool a_value = (i & 1) != 0;
				bool b_value = (i & 2) != 0;
				bool c_value = (i & 4) != 0;

				bool xor3_value = (a_value != b_value) != c_value;
				bool maj_value = (a_value && b_value) || (a_value && c_value) || (b_value && c_value);
				bool maj_nota_value = (!a_value && b_value) || (!a_value && c_value) || (b_value && c_value);
				bool maj_notb_value = (a_value && !b_value) || (a_value && c_value) || (!b_value && c_value);
				bool maj_notc_value = (a_value && b_value) || (a_value && !c_value) || (b_value && !c_value);

				ce.push();
				ce.set(A, a_value ? State::S1 : State::S0);
				ce.set(B, b_value ? State::S1 : State::S0);
				ce.set(C, c_value ? State::S1 : State::S0);

				SigSpec sig = root;

				if (!ce.eval(sig))
					log_abort();

				if (sig != xor3_value)
					is_xor3 = false;

				if (sig != maj_value)
					is_maj = false;

				if (sig != maj_nota_value)
					is_maj_nota = false;

				if (sig != maj_notb_value)
					is_maj_notb = false;

				if (sig != maj_notc_value)
					is_maj_notc = false;

				ce.pop();
			}

			if (is_xor3)
				part_xor3[tuple<SigBit, SigBit, SigBit>(A, B, C)].insert(root);

			if (is_maj)
				part_maj[tuple<SigBit, SigBit, SigBit>(A, B, C)].insert(root);

			if (is_maj_nota)
				part_majnot[tuple<SigBit, SigBit, SigBit>(B, C, A)].insert(root);

			if (is_maj_notb)
				part_majnot[tuple<SigBit, SigBit, SigBit>(A, C, B)].insert(root);

			if (is_maj_notc)
				part_majnot[tuple<SigBit, SigBit, SigBit>(A, B, C)].insert(root);
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

	void make_fa(SigBit A, SigBit B, SigBit C, const pool<SigBit> &sum_out, const pool<SigBit> &carry_out)
	{
		if (!config.enable_fa)
			return;

		Wire *so = module->addWire(NEW_ID);
		Wire *co = module->addWire(NEW_ID);

		Cell *cell = module->addCell(NEW_ID, "$__fa");
		cell->setPort("\\A", A);
		cell->setPort("\\B", B);
		cell->setPort("\\C", C);
		cell->setPort("\\SO", so);
		cell->setPort("\\CO", co);

		log("New full adder %s in module %s: A=%s B=%s C=%s\n", log_id(cell), log_id(module), log_signal(A), log_signal(B), log_signal(C));

		for (auto bit : sum_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, so);
			handled_bits.insert(bit);
			log("  sum out: %s\n", log_signal(bit));
		}

		for (auto bit : carry_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, co);
			handled_bits.insert(bit);
			log("  carry out: %s\n", log_signal(bit));
		}
	}

	void make_ha(SigBit A, SigBit B, const pool<SigBit> &sum_out, const pool<SigBit> &carry_out)
	{
		if (!config.enable_ha)
			return;

		Wire *so = module->addWire(NEW_ID);
		Wire *co = module->addWire(NEW_ID);

		Cell *cell = module->addCell(NEW_ID, "$__ha");
		cell->setPort("\\A", A);
		cell->setPort("\\B", B);
		cell->setPort("\\SO", so);
		cell->setPort("\\CO", co);

		log("New half adder %s in module %s: A=%s B=%s\n", log_id(cell), log_id(module), log_signal(A), log_signal(B));

		for (auto bit : sum_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, so);
			handled_bits.insert(bit);
			log("  sum out: %s\n", log_signal(bit));
		}

		for (auto bit : carry_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, co);
			handled_bits.insert(bit);
			log("  carry out: %s\n", log_signal(bit));
		}
	}

	void make_hs(SigBit A, SigBit B, const pool<SigBit> &sum_out, const pool<SigBit> &carry_out)
	{
		if (!config.enable_hs)
			return;

		Wire *so = module->addWire(NEW_ID);
		Wire *co = module->addWire(NEW_ID);

		Cell *cell = module->addCell(NEW_ID, "$__hs");
		cell->setPort("\\A", A);
		cell->setPort("\\B", B);
		cell->setPort("\\SO", so);
		cell->setPort("\\CO", co);

		log("New half subtractor %s in module %s: A=%s B=%s\n", log_id(cell), log_id(module), log_signal(A), log_signal(B));

		for (auto bit : sum_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, so);
			handled_bits.insert(bit);
			log("  sum out: %s\n", log_signal(bit));
		}

		for (auto bit : carry_out) {
			if (handled_bits.count(bit))
				continue;
			Cell *drv = driver.at(bit);
			drv->setPort("\\Y", module->addWire(NEW_ID));
			module->connect(bit, co);
			handled_bits.insert(bit);
			log("  carry out: %s\n", log_signal(bit));
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

		for (auto &it : part_xor3)
		{
			SigBit A = get<0>(it.first);
			SigBit B = get<1>(it.first);
			SigBit C = get<2>(it.first);

			// FIXME: Add support for full subtractors

			if (part_maj.count(tuple<SigBit, SigBit, SigBit>(A, B, C)))
				make_fa(A, B, C, it.second, part_maj.at(tuple<SigBit, SigBit, SigBit>(A, B, C)));
		}

		for (auto &it : part_xor)
		{
			SigBit A = get<0>(it.first);
			SigBit B = get<1>(it.first);

			if (part_andnot.count(tuple<SigBit, SigBit>(A, B)))
				make_hs(A, B, it.second, part_andnot.at(tuple<SigBit, SigBit>(A, B)));

			if (part_andnot.count(tuple<SigBit, SigBit>(B, A)))
				make_hs(B, A, it.second, part_andnot.at(tuple<SigBit, SigBit>(B, A)));

			if (part_and.count(tuple<SigBit, SigBit>(A, B)))
				make_ha(A, B, it.second, part_and.at(tuple<SigBit, SigBit>(A, B)));
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
