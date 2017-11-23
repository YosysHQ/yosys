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

	int next_nid = 1;
	int initstate_nid = -1;

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

	// ff inputs that need to be evaluated (<nid>, <ff_cell>)
	vector<pair<int, Cell*>> ff_todo;

	pool<Cell*> cell_recursion_guard;
	pool<string> output_symbols;
	string indent;

	void btorf(const char *fmt, ...)
	{
		va_list ap;
		va_start(ap, fmt);
		f << indent << vstringf(fmt, ap);
		va_end(ap);
	}

	void btorf_push(const string &id)
	{
		if (verbose) {
			f << indent << stringf("  ; begin %s\n", id.c_str());
			indent += "    ";
		}
	}

	void btorf_pop(const string &id)
	{
		if (verbose) {
			indent = indent.substr(4);
			f << indent << stringf("  ; end %s\n", id.c_str());
		}
	}

	int get_bv_sid(int width)
	{
		if (sorts_bv.count(width) == 0) {
			int nid = next_nid++;
			btorf("%d sort bitvec %d\n", nid, width);
			sorts_bv[width] = nid;
		}
		return sorts_bv.at(width);
	}

	void add_nid_sig(int nid, const SigSpec &sig)
	{
		for (int i = 0; i < GetSize(sig); i++)
			bit_nid[sig[i]] = make_pair(nid, i);

		sig_nid[sig] = nid;
		nid_width[nid] = GetSize(sig);
	}

	void export_cell(Cell *cell)
	{
		log_assert(cell_recursion_guard.count(cell) == 0);
		cell_recursion_guard.insert(cell);
		btorf_push(log_id(cell));

		if (cell->type.in("$add", "$sub", "$xor"))
		{
			string btor_op;
			if (cell->type == "$add") btor_op = "add";
			if (cell->type == "$sub") btor_op = "sub";
			if (cell->type == "$xor") btor_op = "xor";
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
			btorf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);

			SigSpec sig = sigmap(cell->getPort("\\Y"));

			if (GetSize(sig) < width) {
				int sid = get_bv_sid(GetSize(sig));
				int nid2 = next_nid++;
				btorf("%d slice %d %d %d 0\n", nid2, sid, nid, GetSize(sig)-1);
				nid = nid2;
			}

			add_nid_sig(nid, sig);
			goto okay;
		}

		if (cell->type.in("$logic_and", "$logic_or"))
		{
			string btor_op;
			if (cell->type == "$logic_and") btor_op = "and";
			if (cell->type == "$logic_or")  btor_op = "or";
			log_assert(!btor_op.empty());

			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));
			int nid_b = get_sig_nid(cell->getPort("\\B"));

			if (GetSize(cell->getPort("\\A")) > 1) {
				int nid_red_a = next_nid++;
				btorf("%d redor %d %d\n", nid_red_a, sid, nid_a);
				nid_a = nid_red_a;
			}

			if (GetSize(cell->getPort("\\B")) > 1) {
				int nid_red_b = next_nid++;
				btorf("%d redor %d %d\n", nid_red_b, sid, nid_b);
				nid_b = nid_red_b;
			}

			int nid = next_nid++;
			btorf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);

			SigSpec sig = sigmap(cell->getPort("\\Y"));

			if (GetSize(sig) > 1) {
				int sid = get_bv_sid(GetSize(sig));
				int zeros_nid = get_sig_nid(Const(0, GetSize(sig)-1));
				int nid2 = next_nid++;
				btorf("%d concat %d %d %d\n", nid2, sid, zeros_nid, nid);
				nid = nid2;
			}

			add_nid_sig(nid, sig);
			goto okay;
		}

		if (cell->type.in("$mux", "$_MUX_"))
		{
			SigSpec sig_a = sigmap(cell->getPort("\\A"));
			SigSpec sig_b = sigmap(cell->getPort("\\B"));
			SigSpec sig_s = sigmap(cell->getPort("\\S"));
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			int nid_a = get_sig_nid(sig_a);
			int nid_b = get_sig_nid(sig_b);
			int nid_s = get_sig_nid(sig_s);

			int sid = get_bv_sid(GetSize(sig_y));
			int nid = next_nid++;
			btorf("%d ite %d %d %d %d\n", nid, sid, nid_s, nid_b, nid_a);

			add_nid_sig(nid, sig_y);
			goto okay;
		}

		if (cell->type.in("$dff", "$ff", "$_DFF_P_", "$_DFF_N", "$_FF_"))
		{
			SigSpec sig_d = sigmap(cell->getPort("\\D"));
			SigSpec sig_q = sigmap(cell->getPort("\\Q"));

			string symbol = log_signal(sig_q);
			if (symbol.find(' ') != string::npos)
				symbol = log_id(cell);

			if (symbol[0] == '\\')
				symbol = symbol.substr(1);

			int sid = get_bv_sid(GetSize(sig_q));
			int nid = next_nid++;

			if (output_symbols.count(symbol))
				btorf("%d state %d\n", nid, sid);
			else
				btorf("%d state %d %s\n", nid, sid, symbol.c_str());

			ff_todo.push_back(make_pair(nid, cell));
			add_nid_sig(nid, sig_q);
			goto okay;
		}

		if (cell->type == "$initstate")
		{
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			if (initstate_nid < 0)
			{
				int sid = get_bv_sid(1);
				int one_nid = get_sig_nid(Const(1, 1));
				int zero_nid = get_sig_nid(Const(0, 1));
				initstate_nid = next_nid++;
				btorf("%d state %d\n", initstate_nid, sid);
				btorf("%d init %d %d %d\n", next_nid++, sid, initstate_nid, one_nid);
				btorf("%d next %d %d %d\n", next_nid++, sid, initstate_nid, zero_nid);
			}

			add_nid_sig(initstate_nid, sig_y);
			goto okay;
		}

		log_error("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));

	okay:
		btorf_pop(log_id(cell));
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
							btorf("%d const %d %s\n", nid, sid, c.as_string().c_str());
							consts[c] = nid;
							nid_width[nid] = GetSize(c);
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

				if (lower != 0 || upper+1 != nid_width.at(nid2)) {
					int sid = get_bv_sid(upper-lower+1);
					nid3 = next_nid++;
					btorf("%d slice %d %d %d %d\n", nid3, sid, nid2, upper, lower);
				}

				int nid4 = nid3;

				if (nid >= 0) {
					int sid = get_bv_sid(width+upper-lower+1);
					int nid4 = next_nid++;
					btorf("%d concat %d %d %d\n", nid4, sid, nid, nid3);
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
				btorf("%d slice %d %d %d 0\n", nid2, sid, nid, to_width-1);
				nid = nid2;
			}
			else
			{
				int sid = get_bv_sid(to_width);
				int nid2 = next_nid++;
				btorf("%d %s %d %d %d\n", nid2, is_signed ? "sext" : "uext",
						sid, nid, to_width - GetSize(sig));
				nid = nid2;
			}
		}

		return nid;
	}

	BtorWorker(std::ostream &f, RTLIL::Module *module, bool verbose) :
			f(f), sigmap(module), module(module), verbose(verbose)
	{
		btorf_push("inputs");

		for (auto wire : module->wires())
		{
			if (!wire->port_id || !wire->port_input)
				continue;

			SigSpec sig = sigmap(wire);
			int sid = get_bv_sid(GetSize(sig));
			int nid = next_nid++;

			btorf("%d input %d %s\n", nid, sid, log_id(wire));
			add_nid_sig(nid, sig);
		}

		btorf_pop("inputs");

		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
		{
			if (!cell->output(conn.first))
				continue;

			for (auto bit : sigmap(conn.second))
				bit_cell[bit] = cell;
		}

		for (auto wire : module->wires())
			if (wire->port_output)
				output_symbols.insert(log_id(wire));

		for (auto wire : module->wires())
		{
			if (!wire->port_id || !wire->port_output)
				continue;

			btorf_push(stringf("output %s", log_id(wire)));

			int nid = get_sig_nid(wire);
			btorf("%d output %d %s\n", next_nid++, nid, log_id(wire));

			btorf_pop(stringf("output %s", log_id(wire)));
		}

		for (auto cell : module->cells())
		{
			if (cell->type == "$assume")
			{
				btorf_push(log_id(cell));

				int sid = get_bv_sid(1);
				int nid_a = get_sig_nid(cell->getPort("\\A"));
				int nid_en = get_sig_nid(cell->getPort("\\EN"));
				int nid_not_en = next_nid++;
				int nid_a_or_not_en = next_nid++;
				int nid = next_nid++;

				btorf("%d not %d %d\n", nid_not_en, sid, nid_en);
				btorf("%d or %d %d %d\n", nid_a_or_not_en, sid, nid_a, nid_not_en);
				btorf("%d constraint %d\n", nid, nid_a_or_not_en);

				btorf_pop(log_id(cell));
			}

			if (cell->type == "$assert")
			{
				btorf_push(log_id(cell));

				int sid = get_bv_sid(1);
				int nid_a = get_sig_nid(cell->getPort("\\A"));
				int nid_en = get_sig_nid(cell->getPort("\\EN"));
				int nid_not_a = next_nid++;
				int nid_en_and_not_a = next_nid++;
				int nid = next_nid++;

				btorf("%d not %d %d\n", nid_not_a, sid, nid_a);
				btorf("%d and %d %d %d\n", nid_en_and_not_a, sid, nid_en, nid_not_a);
				btorf("%d bad %d\n", nid, nid_en_and_not_a);

				btorf_pop(log_id(cell));
			}
		}

		while (!ff_todo.empty())
		{
			vector<pair<int, Cell*>> todo;
			todo.swap(ff_todo);

			for (auto &it : todo)
			{
				btorf_push(stringf("next %s", log_id(it.second)));

				SigSpec sig = sigmap(it.second->getPort("\\D"));

				int nid = get_sig_nid(sig);
				int sid = get_bv_sid(GetSize(sig));
				btorf("%d next %d %d %d\n", next_nid++, sid, it.first, nid);

				btorf_pop(stringf("next %s", log_id(it.second)));
			}
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
		log("  -v\n");
		log("    Add comments and indentation to BTOR output file\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool verbose = false;

		log_header(design, "Executing BTOR backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
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
