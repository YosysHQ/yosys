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

// [[CITE]] Btor2 , BtorMC and Boolector 3.0
// Aina Niemetz, Mathias Preiner, Clifford Wolf, Armin Biere
// Computer Aided Verification - 30th International Conference, CAV 2018
// https://cs.stanford.edu/people/niemetz/publication/2018/niemetzpreinerwolfbiere-cav18/

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
	bool single_bad;

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
	vector<int> bad_properties;
	dict<SigBit, bool> initbits;
	pool<Wire*> statewires;
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

	int get_mem_sid(int abits, int dbits)
	{
		pair<int, int> key(abits, dbits);
		if (sorts_mem.count(key) == 0) {
			int addr_sid = get_bv_sid(abits);
			int data_sid = get_bv_sid(dbits);
			int nid = next_nid++;
			btorf("%d sort array %d %d\n", nid, addr_sid, data_sid);
			sorts_mem[key] = nid;
		}
		return sorts_mem.at(key);
	}

	void add_nid_sig(int nid, const SigSpec &sig)
	{
		if (verbose)
			f << indent << stringf("; %d %s\n", nid, log_signal(sig));

		for (int i = 0; i < GetSize(sig); i++)
			bit_nid[sig[i]] = make_pair(nid, i);

		sig_nid[sig] = nid;
		nid_width[nid] = GetSize(sig);
	}

	void export_cell(Cell *cell)
	{
		if (cell_recursion_guard.count(cell)) {
			string cell_list;
			for (auto c : cell_recursion_guard)
				cell_list += stringf("\n    %s", log_id(c));
			log_error("Found topological loop while processing cell %s. Active cells:%s\n", log_id(cell), cell_list.c_str());
		}

		cell_recursion_guard.insert(cell);
		btorf_push(log_id(cell));

		if (cell->type.in("$add", "$sub", "$mul", "$and", "$or", "$xor", "$xnor", "$shl", "$sshl", "$shr", "$sshr", "$shift", "$shiftx",
				"$concat", "$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_"))
		{
			string btor_op;
			if (cell->type == "$add") btor_op = "add";
			if (cell->type == "$sub") btor_op = "sub";
			if (cell->type == "$mul") btor_op = "mul";
			if (cell->type.in("$shl", "$sshl")) btor_op = "sll";
			if (cell->type == "$shr") btor_op = "srl";
			if (cell->type == "$sshr") btor_op = "sra";
			if (cell->type.in("$shift", "$shiftx")) btor_op = "shift";
			if (cell->type.in("$and", "$_AND_")) btor_op = "and";
			if (cell->type.in("$or", "$_OR_")) btor_op = "or";
			if (cell->type.in("$xor", "$_XOR_")) btor_op = "xor";
			if (cell->type == "$concat") btor_op = "concat";
			if (cell->type == "$_NAND_") btor_op = "nand";
			if (cell->type == "$_NOR_") btor_op = "nor";
			if (cell->type.in("$xnor", "$_XNOR_")) btor_op = "xnor";
			log_assert(!btor_op.empty());

			int width = GetSize(cell->getPort("\\Y"));
			width = std::max(width, GetSize(cell->getPort("\\A")));
			width = std::max(width, GetSize(cell->getPort("\\B")));

			bool a_signed = cell->hasParam("\\A_SIGNED") ? cell->getParam("\\A_SIGNED").as_bool() : false;
			bool b_signed = cell->hasParam("\\B_SIGNED") ? cell->getParam("\\B_SIGNED").as_bool() : false;

			if (btor_op == "shift" && !b_signed)
				btor_op = "srl";

			if (cell->type.in("$shl", "$sshl", "$shr", "$sshr"))
				b_signed = false;

			if (cell->type == "$sshr" && !a_signed)
				btor_op = "srl";

			int sid = get_bv_sid(width);
			int nid;

			if (btor_op == "shift")
			{
				int nid_a = get_sig_nid(cell->getPort("\\A"), width, false);
				int nid_b = get_sig_nid(cell->getPort("\\B"), width, b_signed);

				int nid_r = next_nid++;
				btorf("%d srl %d %d %d\n", nid_r, sid, nid_a, nid_b);

				int nid_b_neg = next_nid++;
				btorf("%d neg %d %d\n", nid_b_neg, sid, nid_b);

				int nid_l = next_nid++;
				btorf("%d sll %d %d %d\n", nid_l, sid, nid_a, nid_b_neg);

				int sid_bit = get_bv_sid(1);
				int nid_zero = get_sig_nid(Const(0, width));
				int nid_b_ltz = next_nid++;
				btorf("%d slt %d %d %d\n", nid_b_ltz, sid_bit, nid_b, nid_zero);

				nid = next_nid++;
				btorf("%d ite %d %d %d %d\n", nid, sid, nid_b_ltz, nid_l, nid_r);
			}
			else
			{
				int nid_a = get_sig_nid(cell->getPort("\\A"), width, a_signed);
				int nid_b = get_sig_nid(cell->getPort("\\B"), width, b_signed);

				nid = next_nid++;
				btorf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);
			}

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

		if (cell->type.in("$div", "$mod"))
		{
			string btor_op;
			if (cell->type == "$div") btor_op = "div";
			if (cell->type == "$mod") btor_op = "rem";
			log_assert(!btor_op.empty());

			int width = GetSize(cell->getPort("\\Y"));
			width = std::max(width, GetSize(cell->getPort("\\A")));
			width = std::max(width, GetSize(cell->getPort("\\B")));

			bool a_signed = cell->hasParam("\\A_SIGNED") ? cell->getParam("\\A_SIGNED").as_bool() : false;
			bool b_signed = cell->hasParam("\\B_SIGNED") ? cell->getParam("\\B_SIGNED").as_bool() : false;

			int nid_a = get_sig_nid(cell->getPort("\\A"), width, a_signed);
			int nid_b = get_sig_nid(cell->getPort("\\B"), width, b_signed);

			int sid = get_bv_sid(width);
			int nid = next_nid++;
			btorf("%d %c%s %d %d %d\n", nid, a_signed || b_signed ? 's' : 'u', btor_op.c_str(), sid, nid_a, nid_b);

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

		if (cell->type.in("$_ANDNOT_", "$_ORNOT_"))
		{
			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));
			int nid_b = get_sig_nid(cell->getPort("\\B"));

			int nid1 = next_nid++;
			int nid2 = next_nid++;

			if (cell->type == "$_ANDNOT_") {
				btorf("%d not %d %d\n", nid1, sid, nid_b);
				btorf("%d and %d %d %d\n", nid2, sid, nid_a, nid1);
			}

			if (cell->type == "$_ORNOT_") {
				btorf("%d not %d %d\n", nid1, sid, nid_b);
				btorf("%d or %d %d %d\n", nid2, sid, nid_a, nid1);
			}

			SigSpec sig = sigmap(cell->getPort("\\Y"));
			add_nid_sig(nid2, sig);
			goto okay;
		}

		if (cell->type.in("$_OAI3_", "$_AOI3_"))
		{
			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));
			int nid_b = get_sig_nid(cell->getPort("\\B"));
			int nid_c = get_sig_nid(cell->getPort("\\C"));

			int nid1 = next_nid++;
			int nid2 = next_nid++;
			int nid3 = next_nid++;

			if (cell->type == "$_OAI3_") {
				btorf("%d or %d %d %d\n", nid1, sid, nid_a, nid_b);
				btorf("%d and %d %d %d\n", nid2, sid, nid1, nid_c);
				btorf("%d not %d %d\n", nid3, sid, nid2);
			}

			if (cell->type == "$_AOI3_") {
				btorf("%d and %d %d %d\n", nid1, sid, nid_a, nid_b);
				btorf("%d or %d %d %d\n", nid2, sid, nid1, nid_c);
				btorf("%d not %d %d\n", nid3, sid, nid2);
			}

			SigSpec sig = sigmap(cell->getPort("\\Y"));
			add_nid_sig(nid3, sig);
			goto okay;
		}

		if (cell->type.in("$_OAI4_", "$_AOI4_"))
		{
			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));
			int nid_b = get_sig_nid(cell->getPort("\\B"));
			int nid_c = get_sig_nid(cell->getPort("\\C"));
			int nid_d = get_sig_nid(cell->getPort("\\D"));

			int nid1 = next_nid++;
			int nid2 = next_nid++;
			int nid3 = next_nid++;
			int nid4 = next_nid++;

			if (cell->type == "$_OAI4_") {
				btorf("%d or %d %d %d\n", nid1, sid, nid_a, nid_b);
				btorf("%d or %d %d %d\n", nid2, sid, nid_c, nid_d);
				btorf("%d and %d %d %d\n", nid3, sid, nid1, nid2);
				btorf("%d not %d %d\n", nid4, sid, nid3);
			}

			if (cell->type == "$_AOI4_") {
				btorf("%d and %d %d %d\n", nid1, sid, nid_a, nid_b);
				btorf("%d and %d %d %d\n", nid2, sid, nid_c, nid_d);
				btorf("%d or %d %d %d\n", nid3, sid, nid1, nid2);
				btorf("%d not %d %d\n", nid4, sid, nid3);
			}

			SigSpec sig = sigmap(cell->getPort("\\Y"));
			add_nid_sig(nid4, sig);
			goto okay;
		}

		if (cell->type.in("$lt", "$le", "$eq", "$eqx", "$ne", "$nex", "$ge", "$gt"))
		{
			string btor_op;
			if (cell->type == "$lt") btor_op = "lt";
			if (cell->type == "$le") btor_op = "lte";
			if (cell->type.in("$eq", "$eqx")) btor_op = "eq";
			if (cell->type.in("$ne", "$nex")) btor_op = "neq";
			if (cell->type == "$ge") btor_op = "gte";
			if (cell->type == "$gt") btor_op = "gt";
			log_assert(!btor_op.empty());

			int width = 1;
			width = std::max(width, GetSize(cell->getPort("\\A")));
			width = std::max(width, GetSize(cell->getPort("\\B")));

			bool a_signed = cell->hasParam("\\A_SIGNED") ? cell->getParam("\\A_SIGNED").as_bool() : false;
			bool b_signed = cell->hasParam("\\B_SIGNED") ? cell->getParam("\\B_SIGNED").as_bool() : false;

			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"), width, a_signed);
			int nid_b = get_sig_nid(cell->getPort("\\B"), width, b_signed);

			int nid = next_nid++;
			if (cell->type.in("$lt", "$le", "$ge", "$gt")) {
				btorf("%d %c%s %d %d %d\n", nid, a_signed || b_signed ? 's' : 'u', btor_op.c_str(), sid, nid_a, nid_b);
			} else {
				btorf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);
			}

			SigSpec sig = sigmap(cell->getPort("\\Y"));

			if (GetSize(sig) > 1) {
				int sid = get_bv_sid(GetSize(sig));
				int nid2 = next_nid++;
				btorf("%d uext %d %d %d\n", nid2, sid, nid, GetSize(sig) - 1);
				nid = nid2;
			}

			add_nid_sig(nid, sig);
			goto okay;
		}

		if (cell->type.in("$not", "$neg", "$_NOT_"))
		{
			string btor_op;
			if (cell->type.in("$not", "$_NOT_")) btor_op = "not";
			if (cell->type == "$neg") btor_op = "neg";
			log_assert(!btor_op.empty());

			int width = GetSize(cell->getPort("\\Y"));
			width = std::max(width, GetSize(cell->getPort("\\A")));

			bool a_signed = cell->hasParam("\\A_SIGNED") ? cell->getParam("\\A_SIGNED").as_bool() : false;

			int sid = get_bv_sid(width);
			int nid_a = get_sig_nid(cell->getPort("\\A"), width, a_signed);

			int nid = next_nid++;
			btorf("%d %s %d %d\n", nid, btor_op.c_str(), sid, nid_a);

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

		if (cell->type.in("$logic_and", "$logic_or", "$logic_not"))
		{
			string btor_op;
			if (cell->type == "$logic_and") btor_op = "and";
			if (cell->type == "$logic_or")  btor_op = "or";
			if (cell->type == "$logic_not") btor_op = "not";
			log_assert(!btor_op.empty());

			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));
			int nid_b = btor_op != "not" ? get_sig_nid(cell->getPort("\\B")) : 0;

			if (GetSize(cell->getPort("\\A")) > 1) {
				int nid_red_a = next_nid++;
				btorf("%d redor %d %d\n", nid_red_a, sid, nid_a);
				nid_a = nid_red_a;
			}

			if (btor_op != "not" && GetSize(cell->getPort("\\B")) > 1) {
				int nid_red_b = next_nid++;
				btorf("%d redor %d %d\n", nid_red_b, sid, nid_b);
				nid_b = nid_red_b;
			}

			int nid = next_nid++;
			if (btor_op != "not")
				btorf("%d %s %d %d %d\n", nid, btor_op.c_str(), sid, nid_a, nid_b);
			else
				btorf("%d %s %d %d\n", nid, btor_op.c_str(), sid, nid_a);

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

		if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_bool", "$reduce_xor", "$reduce_xnor"))
		{
			string btor_op;
			if (cell->type == "$reduce_and") btor_op = "redand";
			if (cell->type.in("$reduce_or", "$reduce_bool")) btor_op = "redor";
			if (cell->type.in("$reduce_xor", "$reduce_xnor")) btor_op = "redxor";
			log_assert(!btor_op.empty());

			int sid = get_bv_sid(1);
			int nid_a = get_sig_nid(cell->getPort("\\A"));

			int nid = next_nid++;
			btorf("%d %s %d %d\n", nid, btor_op.c_str(), sid, nid_a);

			if (cell->type == "$reduce_xnor") {
				int nid2 = next_nid++;
				btorf("%d not %d %d %d\n", nid2, sid, nid);
				nid = nid2;
			}

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

		if (cell->type.in("$mux", "$_MUX_", "$_NMUX_"))
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

			if (cell->type == "$_NMUX_") {
				int tmp = nid;
				nid = next_nid++;
				btorf("%d not %d %d\n", nid, sid, tmp);
			}

			add_nid_sig(nid, sig_y);
			goto okay;
		}

		if (cell->type == "$pmux")
		{
			SigSpec sig_a = sigmap(cell->getPort("\\A"));
			SigSpec sig_b = sigmap(cell->getPort("\\B"));
			SigSpec sig_s = sigmap(cell->getPort("\\S"));
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			int width = GetSize(sig_a);
			int sid = get_bv_sid(width);
			int nid = get_sig_nid(sig_a);

			for (int i = 0; i < GetSize(sig_s); i++) {
				int nid_b = get_sig_nid(sig_b.extract(i*width, width));
				int nid_s = get_sig_nid(sig_s.extract(i));
				int nid2 = next_nid++;
				btorf("%d ite %d %d %d %d\n", nid2, sid, nid_s, nid_b, nid);
				nid = nid2;
			}

			add_nid_sig(nid, sig_y);
			goto okay;
		}

		if (cell->type.in("$dff", "$ff", "$_DFF_P_", "$_DFF_N", "$_FF_"))
		{
			SigSpec sig_d = sigmap(cell->getPort("\\D"));
			SigSpec sig_q = sigmap(cell->getPort("\\Q"));

			IdString symbol;

			if (sig_q.is_wire()) {
				Wire *w = sig_q.as_wire();
				if (w->port_id == 0) {
					statewires.insert(w);
					symbol = w->name;
				}
			}

			Const initval;
			for (int i = 0; i < GetSize(sig_q); i++)
				if (initbits.count(sig_q[i]))
					initval.bits.push_back(initbits.at(sig_q[i]) ? State::S1 : State::S0);
				else
					initval.bits.push_back(State::Sx);

			int nid_init_val = -1;

			if (!initval.is_fully_undef())
				nid_init_val = get_sig_nid(initval, -1, false, true);

			int sid = get_bv_sid(GetSize(sig_q));
			int nid = next_nid++;

			if (symbol.empty())
				btorf("%d state %d\n", nid, sid);
			else
				btorf("%d state %d %s\n", nid, sid, log_id(symbol));

			if (nid_init_val >= 0) {
				int nid_init = next_nid++;
				if (verbose)
					btorf("; initval = %s\n", log_signal(initval));
				btorf("%d init %d %d %d\n", nid_init, sid, nid, nid_init_val);
			}

			ff_todo.push_back(make_pair(nid, cell));
			add_nid_sig(nid, sig_q);
			goto okay;
		}

		if (cell->type.in("$anyconst", "$anyseq"))
		{
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			int sid = get_bv_sid(GetSize(sig_y));
			int nid = next_nid++;

			btorf("%d state %d\n", nid, sid);

			if (cell->type == "$anyconst") {
				int nid2 = next_nid++;
				btorf("%d next %d %d %d\n", nid2, sid, nid, nid);
			}

			add_nid_sig(nid, sig_y);
			goto okay;
		}

		if (cell->type == "$initstate")
		{
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			if (initstate_nid < 0)
			{
				int sid = get_bv_sid(1);
				int one_nid = get_sig_nid(State::S1);
				int zero_nid = get_sig_nid(State::S0);
				initstate_nid = next_nid++;
				btorf("%d state %d\n", initstate_nid, sid);
				btorf("%d init %d %d %d\n", next_nid++, sid, initstate_nid, one_nid);
				btorf("%d next %d %d %d\n", next_nid++, sid, initstate_nid, zero_nid);
			}

			add_nid_sig(initstate_nid, sig_y);
			goto okay;
		}

		if (cell->type == "$mem")
		{
			int abits = cell->getParam("\\ABITS").as_int();
			int width = cell->getParam("\\WIDTH").as_int();
			int nwords = cell->getParam("\\SIZE").as_int();
			int rdports = cell->getParam("\\RD_PORTS").as_int();
			int wrports = cell->getParam("\\WR_PORTS").as_int();

			Const wr_clk_en = cell->getParam("\\WR_CLK_ENABLE");
			Const rd_clk_en = cell->getParam("\\RD_CLK_ENABLE");

			bool asyncwr = wr_clk_en.is_fully_zero();

			if (!asyncwr && !wr_clk_en.is_fully_ones())
				log_error("Memory %s.%s has mixed async/sync write ports.\n",
						log_id(module), log_id(cell));

			if (!rd_clk_en.is_fully_zero())
				log_error("Memory %s.%s has sync read ports.\n",
						log_id(module), log_id(cell));

			SigSpec sig_rd_addr = sigmap(cell->getPort("\\RD_ADDR"));
			SigSpec sig_rd_data = sigmap(cell->getPort("\\RD_DATA"));

			SigSpec sig_wr_addr = sigmap(cell->getPort("\\WR_ADDR"));
			SigSpec sig_wr_data = sigmap(cell->getPort("\\WR_DATA"));
			SigSpec sig_wr_en = sigmap(cell->getPort("\\WR_EN"));

			int data_sid = get_bv_sid(width);
			int bool_sid = get_bv_sid(1);
			int sid = get_mem_sid(abits, width);

			Const initdata = cell->getParam("\\INIT");
			initdata.exts(nwords*width);
			int nid_init_val = -1;

			if (!initdata.is_fully_undef())
			{
				bool constword = true;
				Const firstword = initdata.extract(0, width);

				for (int i = 1; i < nwords; i++) {
					Const thisword = initdata.extract(i*width, width);
					if (thisword != firstword) {
						constword = false;
						break;
					}
				}

				if (constword)
				{
					if (verbose)
						btorf("; initval = %s\n", log_signal(firstword));
					nid_init_val = get_sig_nid(firstword, -1, false, true);
				}
				else
				{
					nid_init_val = next_nid++;
					btorf("%d state %d\n", nid_init_val, sid);

					for (int i = 0; i < nwords; i++) {
						Const thisword = initdata.extract(i*width, width);
						if (thisword.is_fully_undef())
							continue;
						Const thisaddr(i, abits);
						int nid_thisword = get_sig_nid(thisword, -1, false, true);
						int nid_thisaddr = get_sig_nid(thisaddr, -1, false, true);
						int last_nid_init_val = nid_init_val;
						nid_init_val = next_nid++;
						if (verbose)
							btorf("; initval[%d] = %s\n", i, log_signal(thisword));
						btorf("%d write %d %d %d %d\n", nid_init_val, sid, last_nid_init_val, nid_thisaddr, nid_thisword);
					}
				}
			}


			int nid = next_nid++;
			int nid_head = nid;

			if (cell->name[0] == '$')
				btorf("%d state %d\n", nid, sid);
			else
				btorf("%d state %d %s\n", nid, sid, log_id(cell));

			if (nid_init_val >= 0)
			{
				int nid_init = next_nid++;
				btorf("%d init %d %d %d\n", nid_init, sid, nid, nid_init_val);
			}

			if (asyncwr)
			{
				for (int port = 0; port < wrports; port++)
				{
					SigSpec wa = sig_wr_addr.extract(port*abits, abits);
					SigSpec wd = sig_wr_data.extract(port*width, width);
					SigSpec we = sig_wr_en.extract(port*width, width);

					int wa_nid = get_sig_nid(wa);
					int wd_nid = get_sig_nid(wd);
					int we_nid = get_sig_nid(we);

					int nid2 = next_nid++;
					btorf("%d read %d %d %d\n", nid2, data_sid, nid_head, wa_nid);

					int nid3 = next_nid++;
					btorf("%d not %d %d\n", nid3, data_sid, we_nid);

					int nid4 = next_nid++;
					btorf("%d and %d %d %d\n", nid4, data_sid, nid2, nid3);

					int nid5 = next_nid++;
					btorf("%d and %d %d %d\n", nid5, data_sid, wd_nid, we_nid);

					int nid6 = next_nid++;
					btorf("%d or %d %d %d\n", nid6, data_sid, nid5, nid4);

					int nid7 = next_nid++;
					btorf("%d write %d %d %d %d\n", nid7, sid, nid_head, wa_nid, nid6);

					int nid8 = next_nid++;
					btorf("%d redor %d %d\n", nid8, bool_sid, we_nid);

					int nid9 = next_nid++;
					btorf("%d ite %d %d %d %d\n", nid9, sid, nid8, nid7, nid_head);

					nid_head = nid9;
				}
			}

			for (int port = 0; port < rdports; port++)
			{
				SigSpec ra = sig_rd_addr.extract(port*abits, abits);
				SigSpec rd = sig_rd_data.extract(port*width, width);

				int ra_nid = get_sig_nid(ra);
				int rd_nid = next_nid++;

				btorf("%d read %d %d %d\n", rd_nid, data_sid, nid_head, ra_nid);

				add_nid_sig(rd_nid, rd);
			}

			if (!asyncwr)
			{
				ff_todo.push_back(make_pair(nid, cell));
			}
			else
			{
				int nid2 = next_nid++;
				btorf("%d next %d %d %d\n", nid2, sid, nid, nid_head);
			}

			goto okay;
		}

		log_error("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));

	okay:
		btorf_pop(log_id(cell));
		cell_recursion_guard.erase(cell);
	}

	int get_sig_nid(SigSpec sig, int to_width = -1, bool is_signed = false, bool is_init = false)
	{
		int nid = -1;
		sigmap.apply(sig);

		for (auto bit : sig)
			if (bit == State::Sx)
				goto has_undef_bits;

		if (0)
		{
	has_undef_bits:
			SigSpec sig_mask_undef, sig_noundef;
			int first_undef = -1;

			for (int i = 0; i < GetSize(sig); i++)
				if (sig[i] == State::Sx) {
					if (first_undef < 0)
						first_undef = i;
					sig_mask_undef.append(State::S1);
					sig_noundef.append(State::S0);
				} else {
					sig_mask_undef.append(State::S0);
					sig_noundef.append(sig[i]);
				}

			if (to_width < 0 || first_undef < to_width)
			{
				int sid = get_bv_sid(GetSize(sig));

				int nid_input = next_nid++;
				if (is_init)
					btorf("%d state %d\n", nid_input, sid);
				else
					btorf("%d input %d\n", nid_input, sid);

				int nid_masked_input;
				if (sig_mask_undef.is_fully_ones()) {
					nid_masked_input = nid_input;
				} else {
					int nid_mask_undef = get_sig_nid(sig_mask_undef);
					nid_masked_input = next_nid++;
					btorf("%d and %d %d %d\n", nid_masked_input, sid, nid_input, nid_mask_undef);
				}

				if (sig_noundef.is_fully_zero()) {
					nid = nid_masked_input;
				} else {
					int nid_noundef = get_sig_nid(sig_noundef);
					nid = next_nid++;
					btorf("%d or %d %d %d\n", nid, sid, nid_masked_input, nid_noundef);
				}

				goto extend_or_trim;
			}

			sig = sig_noundef;
		}

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
						if (bit_cell.count(bit) == 0)
						{
							SigSpec s = bit;

							while (i+GetSize(s) < GetSize(sig) && sig[i+GetSize(s)].wire != nullptr &&
									bit_cell.count(sig[i+GetSize(s)]) == 0)
								s.append(sig[i+GetSize(s)]);

							log_warning("No driver for signal %s.\n", log_signal(s));

							int sid = get_bv_sid(GetSize(s));
							int nid = next_nid++;
							btorf("%d input %d\n", nid, sid);
							nid_width[nid] = GetSize(s);

							for (int j = 0; j < GetSize(s); j++)
								nidbits.push_back(make_pair(nid, j));

							i += GetSize(s)-1;
							continue;
						}
						else
						{
							export_cell(bit_cell.at(bit));
							log_assert(bit_nid.count(bit));
						}
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
					nid4 = next_nid++;
					btorf("%d concat %d %d %d\n", nid4, sid, nid3, nid);
				}

				width += upper-lower+1;
				nid = nid4;
			}

			sig_nid[sig] = nid;
			nid_width[nid] = width;
		}

		nid = sig_nid.at(sig);

	extend_or_trim:
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

	BtorWorker(std::ostream &f, RTLIL::Module *module, bool verbose, bool single_bad) :
			f(f), sigmap(module), module(module), verbose(verbose), single_bad(single_bad)
	{
		btorf_push("inputs");

		for (auto wire : module->wires())
		{
			if (wire->attributes.count("\\init")) {
				Const attrval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(wire) && i < GetSize(attrval); i++)
					if (attrval[i] == State::S0 || attrval[i] == State::S1)
						initbits[sigmap(SigBit(wire, i))] = (attrval[i] == State::S1);
			}

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

				btorf("%d not %d %d\n", nid_not_a, sid, nid_a);
				btorf("%d and %d %d %d\n", nid_en_and_not_a, sid, nid_en, nid_not_a);

				if (single_bad) {
					bad_properties.push_back(nid_en_and_not_a);
				} else {
					int nid = next_nid++;
					string infostr = log_id(cell);
					if (infostr[0] == '$' && cell->attributes.count("\\src")) {
						infostr = cell->attributes.at("\\src").decode_string().c_str();
						std::replace(infostr.begin(), infostr.end(), ' ', '_');
					}
					btorf("%d bad %d %s\n", nid, nid_en_and_not_a, infostr.c_str());
				}

				btorf_pop(log_id(cell));
			}
		}

		for (auto wire : module->wires())
		{
			if (wire->port_id || wire->name[0] == '$')
				continue;

			btorf_push(stringf("wire %s", log_id(wire)));

			int sid = get_bv_sid(GetSize(wire));
			int nid = get_sig_nid(sigmap(wire));

			if (statewires.count(wire))
				continue;

			int this_nid = next_nid++;
			btorf("%d uext %d %d %d %s\n", this_nid, sid, nid, 0, log_id(wire));

			btorf_pop(stringf("wire %s", log_id(wire)));
			continue;
		}

		while (!ff_todo.empty())
		{
			vector<pair<int, Cell*>> todo;
			todo.swap(ff_todo);

			for (auto &it : todo)
			{
				int nid = it.first;
				Cell *cell = it.second;

				btorf_push(stringf("next %s", log_id(cell)));

				if (cell->type == "$mem")
				{
					int abits = cell->getParam("\\ABITS").as_int();
					int width = cell->getParam("\\WIDTH").as_int();
					int wrports = cell->getParam("\\WR_PORTS").as_int();

					SigSpec sig_wr_addr = sigmap(cell->getPort("\\WR_ADDR"));
					SigSpec sig_wr_data = sigmap(cell->getPort("\\WR_DATA"));
					SigSpec sig_wr_en = sigmap(cell->getPort("\\WR_EN"));

					int data_sid = get_bv_sid(width);
					int bool_sid = get_bv_sid(1);
					int sid = get_mem_sid(abits, width);
					int nid_head = nid;

					for (int port = 0; port < wrports; port++)
					{
						SigSpec wa = sig_wr_addr.extract(port*abits, abits);
						SigSpec wd = sig_wr_data.extract(port*width, width);
						SigSpec we = sig_wr_en.extract(port*width, width);

						int wa_nid = get_sig_nid(wa);
						int wd_nid = get_sig_nid(wd);
						int we_nid = get_sig_nid(we);

						int nid2 = next_nid++;
						btorf("%d read %d %d %d\n", nid2, data_sid, nid_head, wa_nid);

						int nid3 = next_nid++;
						btorf("%d not %d %d\n", nid3, data_sid, we_nid);

						int nid4 = next_nid++;
						btorf("%d and %d %d %d\n", nid4, data_sid, nid2, nid3);

						int nid5 = next_nid++;
						btorf("%d and %d %d %d\n", nid5, data_sid, wd_nid, we_nid);

						int nid6 = next_nid++;
						btorf("%d or %d %d %d\n", nid6, data_sid, nid5, nid4);

						int nid7 = next_nid++;
						btorf("%d write %d %d %d %d\n", nid7, sid, nid_head, wa_nid, nid6);

						int nid8 = next_nid++;
						btorf("%d redor %d %d\n", nid8, bool_sid, we_nid);

						int nid9 = next_nid++;
						btorf("%d ite %d %d %d %d\n", nid9, sid, nid8, nid7, nid_head);

						nid_head = nid9;
					}

					int nid2 = next_nid++;
					btorf("%d next %d %d %d\n", nid2, sid, nid, nid_head);
				}
				else
				{
					SigSpec sig = sigmap(cell->getPort("\\D"));
					int nid_q = get_sig_nid(sig);
					int sid = get_bv_sid(GetSize(sig));
					btorf("%d next %d %d %d\n", next_nid++, sid, nid, nid_q);
				}

				btorf_pop(stringf("next %s", log_id(cell)));
			}
		}

		while (!bad_properties.empty())
		{
			vector<int> todo;
			bad_properties.swap(todo);

			int sid = get_bv_sid(1);
			int cursor = 0;

			while (cursor+1 < GetSize(todo))
			{
				int nid_a = todo[cursor++];
				int nid_b = todo[cursor++];
				int nid = next_nid++;

				bad_properties.push_back(nid);
				btorf("%d or %d %d %d\n", nid, sid, nid_a, nid_b);
			}

			if (!bad_properties.empty()) {
				if (cursor < GetSize(todo))
					bad_properties.push_back(todo[cursor++]);
				log_assert(cursor == GetSize(todo));
			} else {
				int nid = next_nid++;
				log_assert(cursor == 0);
				log_assert(GetSize(todo) == 1);
				btorf("%d bad %d\n", nid, todo[cursor]);
			}
		}
	}
};

struct BtorBackend : public Backend {
	BtorBackend() : Backend("btor", "write design to BTOR file") { }
	void help() YS_OVERRIDE
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
		log("  -s\n");
		log("    Output only a single bad property for all asserts\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool verbose = false, single_bad = false;

		log_header(design, "Executing BTOR backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-s") {
				single_bad = true;
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

		BtorWorker(*f, topmod, verbose, single_bad);

		*f << stringf("; end of yosys output\n");
	}
} BtorBackend;

PRIVATE_NAMESPACE_END
