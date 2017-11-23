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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BtorWorker
{
	std::ostream &f;
	SigMap sigmap;
	RTLIL::Module *module;
	bool verbose;
	int next_nid;

	// <width> => <sid>
	dict<int, int> sorts_bv;

	// (<address-width>, <data-width>) => <sid>
	dict<pair<int, int>, int> sorts_mem;

	// SigBit => (<nid>, <bitidx>)
	dict<SigBit, pair<int, int>> bit_nid;

	// <nid> => <bvwidth>
	dict<int, int> nid_width;

	// SigSpec => <nid>
	dict<SigSpec, int> sig_nid;

	// bit to driving cell
	dict<SigBit, Cell*> bit_cell;

	// nids for constants
	dict<Const, int> consts;

	pool<Cell*> cell_recursion_guard;

	int get_bv_sid(int width)
	{
		if (sorts_bv.count(width) == 0) {
			int nid = next_nid++;
			f << stringf("%d sort bitvec %d\n", nid, width);
			sorts_bv[width] = nid;
		}
		return sorts_bv.at(width);
	}

	void export_cell(Cell *cell)
	{
		log_assert(cell_recursion_guard.count(cell) == 0);
		cell_recursion_guard.insert(cell);

		if (cell->type.in("$add", "$sub"))
		{
			string btor_op;
			if (cell->type == "$add") btor_op = "add";
			if (cell->type == "$sub") btor_op = "sub";
			log_assert(!btor_op.empty());

			int width = GetSize(cell->getPort("\\Y"));
			width = std::max(width, GetSize(cell->getPort("\\A")));
			width = std::max(width, GetSize(cell->getPort("\\B")));

			bool a_signed = cell->hasParam("\\A_SIGNED") ? cell->getParam("\\A_SIGNED").as_bool() : false;
			bool b_signed = cell->hasParam("\\B_SIGNED") ? cell->getParam("\\B_SIGNED").as_bool() : false;

			int sid = get_bv_sid(width);
			int nid_a = get_sig_nid(cell->getPort("\\A"), width, a_signed);
			int nid_b = get_sig_nid(cell->getPort("\\B"), width, b_signed);

			int nid = next_nid++;
			f << stringf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);

			SigSpec sig = sigmap(cell->getPort("\\Y"));

			if (GetSize(sig) < width) {
				int sid = get_bv_sid(GetSize(sig));
				int nid2 = next_nid++;
				f << stringf("%d slice %d %d %d 0\n", nid2, sid, nid, GetSize(sig)-1);
				nid = nid2;
			}

			for (int i = 0; i < GetSize(sig); i++)
				bit_nid[sig[i]] = make_pair(nid, i);

			sig_nid[sig] = nid;
			nid_width[nid] = GetSize(sig);

			goto okay;
		}

		log_error("Unsupported cell type: %s\n", log_id(cell));

	okay:
		cell_recursion_guard.erase(cell);
	}

	int get_sig_nid(SigSpec sig, int to_width = -1, bool is_signed = false)
	{
		sigmap.apply(sig);

		if (sig_nid.count(sig) == 0)
		{
			// <nid>, <bitidx>
			vector<pair<int, int>> nidbits;

			// collect all bits
			for (int i = 0; i < GetSize(sig); i++)
			{
				SigBit bit = sig[i];

				if (bit_nid.count(bit) == 0)
				{
					if (bit.wire == nullptr)
					{
						Const c(bit.data);

						while (i+GetSize(c) < GetSize(sig) && sig[i+GetSize(c)].wire == nullptr)
							c.bits.push_back(sig[i+GetSize(c)].data);

						if (consts.count(c) == 0) {
							int sid = get_bv_sid(GetSize(c));
							int nid = next_nid++;
							f << stringf("%d const %d %s\n", nid, sid, c.as_string().c_str());
							consts[c] = nid;
						}

						int nid = consts.at(c);

						for (int j = 0; j < GetSize(c); j++)
							nidbits.push_back(make_pair(nid, j));

						i += GetSize(c)-1;
						continue;
					}
					else
					{
						export_cell(bit_cell.at(bit));
						log_assert(bit_nid.count(bit));
					}
				}

				nidbits.push_back(bit_nid.at(bit));
			}

			int width = 0;
			int nid = -1;

			// group bits and emit slice-concat chain
			for (int i = 0; i < GetSize(nidbits); i++)
			{
				int nid2 = nidbits[i].first;
				int lower =  nidbits[i].second;
				int upper = lower;

				while (i+1 < GetSize(nidbits) && nidbits[i+1].first == nidbits[i].first &&
						nidbits[i+1].second == nidbits[i].second+1)
					upper++, i++;

				int nid3 = nid2;

				if (lower != 0 && upper+1 != nid_width.at(nid2)) {
					int sid = get_bv_sid(upper-lower+1);
					nid3 = next_nid++;
					f << stringf("%d slice %d %d %d %d\n", nid3, sid, nid, upper, lower);
				}

				int nid4 = nid3;

				if (nid >= 0) {
					int sid = get_bv_sid(width+upper-lower+1);
					int nid4 = next_nid++;
					f << stringf("%d concat %d %d %d\n", nid4, sid, nid, nid3);
				}

				width += upper-lower+1;
				nid = nid4;
			}

			sig_nid[sig] = nid;
			nid_width[nid] = width;
		}

		int nid = sig_nid.at(sig);

		if (to_width >= 0 && to_width != GetSize(sig))
		{
			if (to_width < GetSize(sig))
			{
				int sid = get_bv_sid(to_width);
				int nid2 = next_nid++;
				f << stringf("%d slice %d %d %d 0\n", nid2, sid, nid, to_width-1);
				nid = nid2;
			}
			else
			{
				int sid = get_bv_sid(to_width);
				int nid2 = next_nid++;
				f << stringf("%d %s %d %d %d\n", nid2, is_signed ? "sext" : "uext",
						sid, nid, to_width - GetSize(sig));
				nid = nid2;
			}
		}

		return nid;
	}

	BtorWorker(std::ostream &f, RTLIL::Module *module, bool verbose) :
			f(f), sigmap(module), module(module), verbose(verbose), next_nid(1)
	{
		for (auto wire : module->wires())
		{
			if (!wire->port_id || !wire->port_input)
				continue;

			SigSpec sig = sigmap(wire);
			int sid = get_bv_sid(GetSize(sig));
			int nid = next_nid++;

			f << stringf("%d input %d %s\n", nid, sid, log_id(wire));

			for (int i = 0; i < GetSize(sig); i++)
				bit_nid[sig[i]] = make_pair(nid, i);
			sig_nid[sig] = nid;
			nid_width[nid] = GetSize(sig);
		}

		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
		{
			if (!cell->output(conn.first))
				continue;

			for (auto bit : sigmap(conn.second))
				bit_cell[bit] = cell;
		}

		for (auto wire : module->wires())
		{
			if (!wire->port_id || !wire->port_output)
				continue;

			int nid = get_sig_nid(wire);
			f << stringf("%d output %d %s\n", next_nid++, nid, log_id(wire));
		}
	}
};

struct BtorBackend : public Backend {
	BtorBackend() : Backend("btor", "write design to BTOR file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_btor [options] [filename]\n");
		log("\n");
		log("Write a BTOR description of the current design.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool verbose = false;

		log_header(design, "Executing BTOR backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-verbose") {
			// 	verbose = true;
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		RTLIL::Module *topmod = design->top_module();

		if (topmod == nullptr)
			log_cmd_error("No top module found.\n");

		*f << stringf("; BTOR description generated by %s for module %s.\n",
				yosys_version_str, log_id(topmod));

		BtorWorker(*f, topmod, verbose);

		*f << stringf("; end of yosys output\n");
	}
} BtorBackend;

PRIVATE_NAMESPACE_END
