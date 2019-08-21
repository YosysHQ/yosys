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

#define COST_DMUX   90
#define COST_MUX2  100
#define COST_MUX4  220
#define COST_MUX8  460
#define COST_MUX16 940

struct MuxcoverWorker
{
	Module *module;
	SigMap sigmap;

	struct newmux_t
	{
		int cost;
		vector<SigBit> inputs, selects;
		newmux_t() : cost(0) {}
	};

	struct tree_t
	{
		SigBit root;
		dict<SigBit, Cell*> muxes;
		dict<SigBit, newmux_t> newmuxes;
	};

	vector<tree_t> tree_list;

	dict<tuple<SigBit, SigBit, SigBit>, tuple<SigBit, pool<SigBit>, bool>> decode_mux_cache;
	dict<SigBit, tuple<SigBit, SigBit, SigBit>> decode_mux_reverse_cache;
	int decode_mux_counter;

	bool use_mux4;
	bool use_mux8;
	bool use_mux16;
	bool nodecode;
	bool nopartial;

	int cost_dmux;
	int cost_mux2;
	int cost_mux4;
	int cost_mux8;
	int cost_mux16;

	MuxcoverWorker(Module *module) : module(module), sigmap(module)
	{
		use_mux4 = false;
		use_mux8 = false;
		use_mux16 = false;
		nodecode = false;
		nopartial = false;
		cost_dmux = COST_DMUX;
		cost_mux2 = COST_MUX2;
		cost_mux4 = COST_MUX4;
		cost_mux8 = COST_MUX8;
		cost_mux16 = COST_MUX16;
		decode_mux_counter = 0;
	}

	bool xcmp(std::initializer_list<SigBit> list)
	{
		auto cursor = list.begin(), end = list.end();
		log_assert(cursor != end);
		SigBit tmp = *(cursor++);
		while (cursor != end) {
			SigBit bit = *(cursor++);
			if (bit == State::Sx)
				continue;
			if (tmp == State::Sx)
				tmp = bit;
			if (bit != tmp)
				return false;
		}
		return true;
	}

	void treeify()
	{
		pool<SigBit> roots;
		pool<SigBit> used_once;
		dict<SigBit, Cell*> sig_to_mux;

		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			for (auto bit : sigmap(wire))
				roots.insert(bit);
		}

		for (auto cell : module->cells()) {
			for (auto conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (used_once.count(bit) || cell->type != ID($_MUX_) || conn.first == ID(S))
						roots.insert(bit);
					used_once.insert(bit);
				}
			}
			if (cell->type == ID($_MUX_))
				sig_to_mux[sigmap(cell->getPort(ID::Y))] = cell;
		}

		log("  Treeifying %d MUXes:\n", GetSize(sig_to_mux));

		roots.sort();
		for (auto rootsig : roots)
		{
			tree_t tree;
			tree.root = rootsig;

			pool<SigBit> wavefront;
			wavefront.insert(rootsig);

			while (!wavefront.empty()) {
				SigBit bit = wavefront.pop();
				if (sig_to_mux.count(bit) && (bit == rootsig || !roots.count(bit))) {
					Cell *c = sig_to_mux.at(bit);
					tree.muxes[bit] = c;
					wavefront.insert(sigmap(c->getPort(ID::A)));
					wavefront.insert(sigmap(c->getPort(ID::B)));
				}
			}

			if (!tree.muxes.empty()) {
				log("    Found tree with %d MUXes at root %s.\n", GetSize(tree.muxes), log_signal(tree.root));
				tree_list.push_back(tree);
			}
		}

		log("    Finished treeification: Found %d trees.\n", GetSize(tree_list));
	}

	bool follow_muxtree(SigBit &ret_bit, tree_t &tree, SigBit bit, const char *path, bool first_layer = true)
	{
		if (*path) {
			if (tree.muxes.count(bit) == 0) {
				if (first_layer || nopartial)
					return false;
				while (path[0] && path[1])
					path++;
				if (path[0] == 'S')
					ret_bit = State::Sx;
				else
					ret_bit = bit;
				return true;
			}
			char port_name[3] = {'\\', *path, 0};
			return follow_muxtree(ret_bit, tree, sigmap(tree.muxes.at(bit)->getPort(port_name)), path+1, false);
		} else {
			ret_bit = bit;
			return true;
		}
	}

	int prepare_decode_mux(SigBit &A, SigBit B, SigBit sel, SigBit bit)
	{
		if (A == B || sel == State::Sx)
			return 0;

		tuple<SigBit, SigBit, SigBit> key(A, B, sel);
		if (decode_mux_cache.count(key) == 0) {
			auto &entry = decode_mux_cache[key];
			std::get<0>(entry) = module->addWire(NEW_ID);
			std::get<2>(entry) = false;
			decode_mux_reverse_cache[std::get<0>(entry)] = key;
		}

		auto &entry = decode_mux_cache[key];
		A = std::get<0>(entry);
		std::get<1>(entry).insert(bit);

		if (std::get<2>(entry))
			return 0;

		if (A == State::Sx || B == State::Sx)
			return 0;

		return cost_dmux / GetSize(std::get<1>(entry));
	}

	void implement_decode_mux(SigBit ctrl_bit)
	{
		if (decode_mux_reverse_cache.count(ctrl_bit) == 0)
			return;

		auto &key = decode_mux_reverse_cache.at(ctrl_bit);
		auto &entry = decode_mux_cache[key];

		if (std::get<2>(entry))
			return;

		implement_decode_mux(std::get<0>(key));
		implement_decode_mux(std::get<1>(key));

		if (std::get<0>(key) == State::Sx) {
			module->addBufGate(NEW_ID, std::get<1>(key), ctrl_bit);
		} else if (std::get<1>(key) == State::Sx) {
			module->addBufGate(NEW_ID, std::get<0>(key), ctrl_bit);
		} else {
			module->addMuxGate(NEW_ID, std::get<0>(key), std::get<1>(key), std::get<2>(key), ctrl_bit);
			decode_mux_counter++;
		}
		std::get<2>(entry) = true;
	}

	void find_best_covers(tree_t &tree, const vector<SigBit> &bits)
	{
		for (auto bit : bits)
			find_best_cover(tree, bit);
	}

	int sum_best_covers(tree_t &tree, const vector<SigBit> &bits)
	{
		int sum = 0;
		for (auto bit : pool<SigBit>(bits.begin(), bits.end())) {
			int cost = tree.newmuxes.at(bit).cost;
			log_debug("        Best cost for %s: %d\n", log_signal(bit), cost);
			sum += cost;
		}
		return sum;
	}

	int find_best_cover(tree_t &tree, SigBit bit)
	{
		if (tree.newmuxes.count(bit)) {
			return tree.newmuxes.at(bit).cost;
		}

		SigBit A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P;
		SigBit S1, S2, S3, S4, S5, S6, S7, S8;
		SigBit T1, T2, T3, T4;
		SigBit U1, U2;
		SigBit V1;

		newmux_t best_mux;
		bool ok = true;

		// 2-Input MUX

		ok = ok && follow_muxtree(A, tree, bit, "A");
		ok = ok && follow_muxtree(B, tree, bit, "B");

		ok = ok && follow_muxtree(S1, tree, bit, "S");

		if (ok)
		{
			newmux_t mux;

			mux.inputs.push_back(A);
			mux.inputs.push_back(B);
			mux.selects.push_back(S1);

			find_best_covers(tree, mux.inputs);
			log_debug("        Decode cost for mux2 at %s: %d\n", log_signal(bit), mux.cost);

			mux.cost += cost_mux2;
			mux.cost += sum_best_covers(tree, mux.inputs);

			log_debug("      Cost of mux2 at %s: %d\n", log_signal(bit), mux.cost);

			best_mux = mux;
		}

		// 4-Input MUX

		if (use_mux4)
		{
			ok = ok && follow_muxtree(A, tree, bit, "AA");
			ok = ok && follow_muxtree(B, tree, bit, "AB");
			ok = ok && follow_muxtree(C, tree, bit, "BA");
			ok = ok && follow_muxtree(D, tree, bit, "BB");

			ok = ok && follow_muxtree(S1, tree, bit, "AS");
			ok = ok && follow_muxtree(S2, tree, bit, "BS");

			if (nodecode)
				ok = ok && xcmp({S1, S2});

			ok = ok && follow_muxtree(T1, tree, bit, "S");

			if (ok)
			{
				newmux_t mux;

				mux.inputs.push_back(A);
				mux.inputs.push_back(B);
				mux.inputs.push_back(C);
				mux.inputs.push_back(D);

				mux.cost += prepare_decode_mux(S1, S2, T1, bit);

				mux.selects.push_back(S1);
				mux.selects.push_back(T1);

				find_best_covers(tree, mux.inputs);
				log_debug("        Decode cost for mux4 at %s: %d\n", log_signal(bit), mux.cost);

				mux.cost += cost_mux4;
				mux.cost += sum_best_covers(tree, mux.inputs);

				log_debug("      Cost of mux4 at %s: %d\n", log_signal(bit), mux.cost);

				if (best_mux.cost >= mux.cost)
					best_mux = mux;
			}
		}

		// 8-Input MUX

		if (use_mux8)
		{
			ok = ok && follow_muxtree(A, tree, bit, "AAA");
			ok = ok && follow_muxtree(B, tree, bit, "AAB");
			ok = ok && follow_muxtree(C, tree, bit, "ABA");
			ok = ok && follow_muxtree(D, tree, bit, "ABB");
			ok = ok && follow_muxtree(E, tree, bit, "BAA");
			ok = ok && follow_muxtree(F, tree, bit, "BAB");
			ok = ok && follow_muxtree(G, tree, bit, "BBA");
			ok = ok && follow_muxtree(H, tree, bit, "BBB");

			ok = ok && follow_muxtree(S1, tree, bit, "AAS");
			ok = ok && follow_muxtree(S2, tree, bit, "ABS");
			ok = ok && follow_muxtree(S3, tree, bit, "BAS");
			ok = ok && follow_muxtree(S4, tree, bit, "BBS");

			if (nodecode)
				ok = ok && xcmp({S1, S2, S3, S4});

			ok = ok && follow_muxtree(T1, tree, bit, "AS");
			ok = ok && follow_muxtree(T2, tree, bit, "BS");

			if (nodecode)
				ok = ok && xcmp({T1, T2});

			ok = ok && follow_muxtree(U1, tree, bit, "S");

			if (ok)
			{
				newmux_t mux;

				mux.inputs.push_back(A);
				mux.inputs.push_back(B);
				mux.inputs.push_back(C);
				mux.inputs.push_back(D);
				mux.inputs.push_back(E);
				mux.inputs.push_back(F);
				mux.inputs.push_back(G);
				mux.inputs.push_back(H);

				mux.cost += prepare_decode_mux(S1, S2, T1, bit);
				mux.cost += prepare_decode_mux(S3, S4, T2, bit);
				mux.cost += prepare_decode_mux(S1, S3, U1, bit);

				mux.cost += prepare_decode_mux(T1, T2, U1, bit);

				mux.selects.push_back(S1);
				mux.selects.push_back(T1);
				mux.selects.push_back(U1);

				find_best_covers(tree, mux.inputs);
				log_debug("        Decode cost for mux8 at %s: %d\n", log_signal(bit), mux.cost);

				mux.cost += cost_mux8;
				mux.cost += sum_best_covers(tree, mux.inputs);

				log_debug("      Cost of mux8 at %s: %d\n", log_signal(bit), mux.cost);

				if (best_mux.cost >= mux.cost)
					best_mux = mux;
			}
		}

		// 16-Input MUX

		if (use_mux16)
		{
			ok = ok && follow_muxtree(A, tree, bit, "AAAA");
			ok = ok && follow_muxtree(B, tree, bit, "AAAB");
			ok = ok && follow_muxtree(C, tree, bit, "AABA");
			ok = ok && follow_muxtree(D, tree, bit, "AABB");
			ok = ok && follow_muxtree(E, tree, bit, "ABAA");
			ok = ok && follow_muxtree(F, tree, bit, "ABAB");
			ok = ok && follow_muxtree(G, tree, bit, "ABBA");
			ok = ok && follow_muxtree(H, tree, bit, "ABBB");
			ok = ok && follow_muxtree(I, tree, bit, "BAAA");
			ok = ok && follow_muxtree(J, tree, bit, "BAAB");
			ok = ok && follow_muxtree(K, tree, bit, "BABA");
			ok = ok && follow_muxtree(L, tree, bit, "BABB");
			ok = ok && follow_muxtree(M, tree, bit, "BBAA");
			ok = ok && follow_muxtree(N, tree, bit, "BBAB");
			ok = ok && follow_muxtree(O, tree, bit, "BBBA");
			ok = ok && follow_muxtree(P, tree, bit, "BBBB");

			ok = ok && follow_muxtree(S1, tree, bit, "AAAS");
			ok = ok && follow_muxtree(S2, tree, bit, "AABS");
			ok = ok && follow_muxtree(S3, tree, bit, "ABAS");
			ok = ok && follow_muxtree(S4, tree, bit, "ABBS");
			ok = ok && follow_muxtree(S5, tree, bit, "BAAS");
			ok = ok && follow_muxtree(S6, tree, bit, "BABS");
			ok = ok && follow_muxtree(S7, tree, bit, "BBAS");
			ok = ok && follow_muxtree(S8, tree, bit, "BBBS");

			if (nodecode)
				ok = ok && xcmp({S1, S2, S3, S4, S5, S6, S7, S8});

			ok = ok && follow_muxtree(T1, tree, bit, "AAS");
			ok = ok && follow_muxtree(T2, tree, bit, "ABS");
			ok = ok && follow_muxtree(T3, tree, bit, "BAS");
			ok = ok && follow_muxtree(T4, tree, bit, "BBS");

			if (nodecode)
				ok = ok && xcmp({T1, T2, T3, T4});

			ok = ok && follow_muxtree(U1, tree, bit, "AS");
			ok = ok && follow_muxtree(U2, tree, bit, "BS");

			if (nodecode)
				ok = ok && xcmp({U1, U2});

			ok = ok && follow_muxtree(V1, tree, bit, "S");

			if (ok)
			{
				newmux_t mux;

				mux.inputs.push_back(A);
				mux.inputs.push_back(B);
				mux.inputs.push_back(C);
				mux.inputs.push_back(D);
				mux.inputs.push_back(E);
				mux.inputs.push_back(F);
				mux.inputs.push_back(G);
				mux.inputs.push_back(H);
				mux.inputs.push_back(I);
				mux.inputs.push_back(J);
				mux.inputs.push_back(K);
				mux.inputs.push_back(L);
				mux.inputs.push_back(M);
				mux.inputs.push_back(N);
				mux.inputs.push_back(O);
				mux.inputs.push_back(P);

				mux.cost += prepare_decode_mux(S1, S2, T1, bit);
				mux.cost += prepare_decode_mux(S3, S4, T2, bit);
				mux.cost += prepare_decode_mux(S5, S6, T3, bit);
				mux.cost += prepare_decode_mux(S7, S8, T4, bit);
				mux.cost += prepare_decode_mux(S1, S3, U1, bit);
				mux.cost += prepare_decode_mux(S5, S7, U2, bit);
				mux.cost += prepare_decode_mux(S1, S5, V1, bit);

				mux.cost += prepare_decode_mux(T1, T2, U1, bit);
				mux.cost += prepare_decode_mux(T3, T4, U2, bit);
				mux.cost += prepare_decode_mux(T1, T3, V1, bit);

				mux.cost += prepare_decode_mux(U1, U2, V1, bit);

				mux.selects.push_back(S1);
				mux.selects.push_back(T1);
				mux.selects.push_back(U1);
				mux.selects.push_back(V1);

				find_best_covers(tree, mux.inputs);
				log_debug("        Decode cost for mux16 at %s: %d\n", log_signal(bit), mux.cost);

				mux.cost += cost_mux16;
				mux.cost += sum_best_covers(tree, mux.inputs);

				log_debug("      Cost of mux16 at %s: %d\n", log_signal(bit), mux.cost);

				if (best_mux.cost >= mux.cost)
					best_mux = mux;
			}
		}

		tree.newmuxes[bit] = best_mux;
		return best_mux.cost;
	}

	void implement_best_cover(tree_t &tree, SigBit bit, int count_muxes_by_type[4])
	{
		newmux_t mux = tree.newmuxes.at(bit);

		for (auto inbit : mux.inputs)
			implement_best_cover(tree, inbit, count_muxes_by_type);

		for (auto selbit : mux.selects)
			implement_decode_mux(selbit);

		if (GetSize(mux.inputs) == 0)
			return;

		if (GetSize(mux.inputs) == 2) {
			count_muxes_by_type[0]++;
			Cell *cell = module->addCell(NEW_ID, ID($_MUX_));
			cell->setPort(ID::A, mux.inputs[0]);
			cell->setPort(ID::B, mux.inputs[1]);
			cell->setPort(ID(S), mux.selects[0]);
			cell->setPort(ID::Y, bit);
			return;
		}

		if (GetSize(mux.inputs) == 4) {
			count_muxes_by_type[1]++;
			Cell *cell = module->addCell(NEW_ID, ID($_MUX4_));
			cell->setPort(ID::A, mux.inputs[0]);
			cell->setPort(ID::B, mux.inputs[1]);
			cell->setPort(ID(C), mux.inputs[2]);
			cell->setPort(ID(D), mux.inputs[3]);
			cell->setPort(ID(S), mux.selects[0]);
			cell->setPort(ID(T), mux.selects[1]);
			cell->setPort(ID::Y, bit);
			return;
		}

		if (GetSize(mux.inputs) == 8) {
			count_muxes_by_type[2]++;
			Cell *cell = module->addCell(NEW_ID, ID($_MUX8_));
			cell->setPort(ID::A, mux.inputs[0]);
			cell->setPort(ID::B, mux.inputs[1]);
			cell->setPort(ID(C), mux.inputs[2]);
			cell->setPort(ID(D), mux.inputs[3]);
			cell->setPort(ID(E), mux.inputs[4]);
			cell->setPort(ID(F), mux.inputs[5]);
			cell->setPort(ID(G), mux.inputs[6]);
			cell->setPort(ID(H), mux.inputs[7]);
			cell->setPort(ID(S), mux.selects[0]);
			cell->setPort(ID(T), mux.selects[1]);
			cell->setPort(ID(U), mux.selects[2]);
			cell->setPort(ID::Y, bit);
			return;
		}

		if (GetSize(mux.inputs) == 16) {
			count_muxes_by_type[3]++;
			Cell *cell = module->addCell(NEW_ID, ID($_MUX16_));
			cell->setPort(ID::A, mux.inputs[0]);
			cell->setPort(ID::B, mux.inputs[1]);
			cell->setPort(ID(C), mux.inputs[2]);
			cell->setPort(ID(D), mux.inputs[3]);
			cell->setPort(ID(E), mux.inputs[4]);
			cell->setPort(ID(F), mux.inputs[5]);
			cell->setPort(ID(G), mux.inputs[6]);
			cell->setPort(ID(H), mux.inputs[7]);
			cell->setPort(ID(I), mux.inputs[8]);
			cell->setPort(ID(J), mux.inputs[9]);
			cell->setPort(ID(K), mux.inputs[10]);
			cell->setPort(ID(L), mux.inputs[11]);
			cell->setPort(ID(M), mux.inputs[12]);
			cell->setPort(ID(N), mux.inputs[13]);
			cell->setPort(ID(O), mux.inputs[14]);
			cell->setPort(ID(P), mux.inputs[15]);
			cell->setPort(ID(S), mux.selects[0]);
			cell->setPort(ID(T), mux.selects[1]);
			cell->setPort(ID(U), mux.selects[2]);
			cell->setPort(ID(V), mux.selects[3]);
			cell->setPort(ID::Y, bit);
			return;
		}

		log_abort();
	}

	void treecover(tree_t &tree)
	{
		int count_muxes_by_type[4] = {0, 0, 0, 0};
		log_debug("    Searching for best cover for tree at %s.\n", log_signal(tree.root));
		find_best_cover(tree, tree.root);
		implement_best_cover(tree, tree.root, count_muxes_by_type);
		log("    Replaced tree at %s: %d MUX2, %d MUX4, %d MUX8, %d MUX16\n", log_signal(tree.root),
				count_muxes_by_type[0], count_muxes_by_type[1], count_muxes_by_type[2], count_muxes_by_type[3]);
		for (auto &it : tree.muxes)
			module->remove(it.second);
	}

	void run()
	{
		log("Covering MUX trees in module %s..\n", log_id(module));

		treeify();

		log("  Covering trees:\n");

		if (!nodecode) {
			log_debug("    Populating cache of decoder muxes.\n");
			for (auto &tree : tree_list) {
				find_best_cover(tree, tree.root);
				tree.newmuxes.clear();
			}
		}

		for (auto &tree : tree_list)
			treecover(tree);

		if (!nodecode)
			log("  Added a total of %d decoder MUXes.\n", decode_mux_counter);
	}
};

struct MuxcoverPass : public Pass {
	MuxcoverPass() : Pass("muxcover", "cover trees of MUX cells with wider MUXes") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    muxcover [options] [selection]\n");
		log("\n");
		log("Cover trees of $_MUX_ cells with $_MUX{4,8,16}_ cells\n");
		log("\n");
		log("    -mux4[=cost], -mux8[=cost], -mux16[=cost]\n");
		log("        Cover $_MUX_ trees using the specified types of MUXes (with optional\n");
		log("        integer costs). If none of these options are given, the effect is the\n");
		log("        same as if all of them are.\n");
		log("        Default costs: $_MUX4_ = %d, $_MUX8_ = %d, \n", COST_MUX4, COST_MUX8);
		log("                       $_MUX16_ = %d\n", COST_MUX16);
		log("\n");
		log("    -mux2=cost\n");
		log("        Use the specified cost for $_MUX_ cells when making covering decisions.\n");
		log("        Default cost: $_MUX_ = %d\n", COST_MUX2);
		log("\n");
		log("    -dmux=cost\n");
		log("        Use the specified cost for $_MUX_ cells used in decoders.\n");
		log("        Default cost: %d\n", COST_DMUX);
		log("\n");
		log("    -nodecode\n");
		log("        Do not insert decoder logic. This reduces the number of possible\n");
		log("        substitutions, but guarantees that the resulting circuit is not\n");
		log("        less efficient than the original circuit.\n");
		log("\n");
		log("    -nopartial\n");
		log("        Do not consider mappings that use $_MUX<N>_ to select from less\n");
		log("        than <N> different signals.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing MUXCOVER pass (mapping to wider MUXes).\n");

		bool use_mux4 = false;
		bool use_mux8 = false;
		bool use_mux16 = false;
		bool nodecode = false;
		bool nopartial = false;
		int cost_dmux = COST_DMUX;
		int cost_mux2 = COST_MUX2;
		int cost_mux4 = COST_MUX4;
		int cost_mux8 = COST_MUX8;
		int cost_mux16 = COST_MUX16;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			const auto &arg = args[argidx];
			if (arg.size() >= 6 && arg.compare(0,6,"-mux2=") == 0) {
				cost_mux2 = atoi(arg.substr(6).c_str());
				continue;
			}
			if (arg.size() >= 5 && arg.compare(0,5,"-mux4") == 0) {
				use_mux4 = true;
				if (arg.size() > 5) {
					if (arg[5] != '=') break;
					cost_mux4 = atoi(arg.substr(6).c_str());
				}
				continue;
			}
			if (arg.size() >= 5 && arg.compare(0,5,"-mux8") == 0) {
				use_mux8 = true;
				if (arg.size() > 5) {
					if (arg[5] != '=') break;
					cost_mux8 = atoi(arg.substr(6).c_str());
				}
				continue;
			}
			if (arg.size() >= 6 && arg.compare(0,6,"-mux16") == 0) {
				use_mux16 = true;
				if (arg.size() > 6) {
					if (arg[6] != '=') break;
					cost_mux16 = atoi(arg.substr(7).c_str());
				}
				continue;
			}
			if (arg.size() >= 6 && arg.compare(0,6,"-dmux=") == 0) {
				cost_dmux = atoi(arg.substr(6).c_str());
				continue;
			}
			if (arg == "-nodecode") {
				nodecode = true;
				continue;
			}
			if (arg == "-nopartial") {
				nopartial = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!use_mux4 && !use_mux8 && !use_mux16) {
			use_mux4 = true;
			use_mux8 = true;
			use_mux16 = true;
		}

		for (auto module : design->selected_modules())
		{
			MuxcoverWorker worker(module);
			worker.use_mux4 = use_mux4;
			worker.use_mux8 = use_mux8;
			worker.use_mux16 = use_mux16;
			worker.cost_dmux = cost_dmux;
			worker.cost_mux2 = cost_mux2;
			worker.cost_mux4 = cost_mux4;
			worker.cost_mux8 = cost_mux8;
			worker.cost_mux16 = cost_mux16;
			worker.nodecode = nodecode;
			worker.nopartial = nopartial;
			worker.run();
		}
	}
} MuxcoverPass;

PRIVATE_NAMESPACE_END
