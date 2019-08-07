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

struct Smt2Worker
{
	CellTypes ct;
	SigMap sigmap;
	RTLIL::Module *module;
	bool bvmode, memmode, wiresmode, verbose, statebv, statedt, forallmode;
	dict<IdString, int> &mod_stbv_width;
	int idcounter = 0, statebv_width = 0;

	std::vector<std::string> decls, trans, hier, dtmembers;
	std::map<RTLIL::SigBit, RTLIL::Cell*> bit_driver;
	std::set<RTLIL::Cell*> exported_cells, hiercells, hiercells_queue;
	pool<Cell*> recursive_cells, registers;

	pool<SigBit> clock_posedge, clock_negedge;
	vector<string> ex_state_eq, ex_input_eq;

	std::map<RTLIL::SigBit, std::pair<int, int>> fcache;
	std::map<Cell*, int> memarrays;
	std::map<int, int> bvsizes;
	dict<IdString, char*> ids;

	const char *get_id(IdString n)
	{
		if (ids.count(n) == 0) {
			std::string str = log_id(n);
			for (int i = 0; i < GetSize(str); i++) {
				if (str[i] == '\\')
					str[i] = '/';
			}
			ids[n] = strdup(str.c_str());
		}
		return ids[n];
	}

	template<typename T>
	const char *get_id(T *obj) {
		return get_id(obj->name);
	}

	void makebits(std::string name, int width = 0, std::string comment = std::string())
	{
		std::string decl_str;

		if (statebv)
		{
			if (width == 0) {
				decl_str = stringf("(define-fun |%s| ((state |%s_s|)) Bool (= ((_ extract %d %d) state) #b1))", name.c_str(), get_id(module), statebv_width, statebv_width);
				statebv_width += 1;
			} else {
				decl_str = stringf("(define-fun |%s| ((state |%s_s|)) (_ BitVec %d) ((_ extract %d %d) state))", name.c_str(), get_id(module), width, statebv_width+width-1, statebv_width);
				statebv_width += width;
			}
		}
		else if (statedt)
		{
			if (width == 0) {
				decl_str = stringf("  (|%s| Bool)", name.c_str());
			} else {
				decl_str = stringf("  (|%s| (_ BitVec %d))", name.c_str(), width);
			}
		}
		else
		{
			if (width == 0) {
				decl_str = stringf("(declare-fun |%s| (|%s_s|) Bool)", name.c_str(), get_id(module));
			} else {
				decl_str = stringf("(declare-fun |%s| (|%s_s|) (_ BitVec %d))", name.c_str(), get_id(module), width);
			}
		}

		if (!comment.empty())
			decl_str += " ; " + comment;

		if (statedt)
			dtmembers.push_back(decl_str + "\n");
		else
			decls.push_back(decl_str + "\n");
	}

	Smt2Worker(RTLIL::Module *module, bool bvmode, bool memmode, bool wiresmode, bool verbose, bool statebv, bool statedt, bool forallmode,
			dict<IdString, int> &mod_stbv_width, dict<IdString, dict<IdString, pair<bool, bool>>> &mod_clk_cache) :
			ct(module->design), sigmap(module), module(module), bvmode(bvmode), memmode(memmode), wiresmode(wiresmode),
			verbose(verbose), statebv(statebv), statedt(statedt), forallmode(forallmode), mod_stbv_width(mod_stbv_width)
	{
		pool<SigBit> noclock;

		makebits(stringf("%s_is", get_id(module)));

		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
		{
			if (GetSize(conn.second) == 0)
				continue;

			bool is_input = ct.cell_input(cell->type, conn.first);
			bool is_output = ct.cell_output(cell->type, conn.first);

			if (is_output && !is_input)
				for (auto bit : sigmap(conn.second)) {
					if (bit_driver.count(bit))
						log_error("Found multiple drivers for %s.\n", log_signal(bit));
					bit_driver[bit] = cell;
				}
			else if (is_output || !is_input)
				log_error("Unsupported or unknown directionality on port %s of cell %s.%s (%s).\n",
						log_id(conn.first), log_id(module), log_id(cell), log_id(cell->type));

			if (cell->type.in("$mem") && conn.first.in("\\RD_CLK", "\\WR_CLK"))
			{
				SigSpec clk = sigmap(conn.second);
				for (int i = 0; i < GetSize(clk); i++)
				{
					if (clk[i].wire == nullptr)
						continue;

					if (cell->getParam(conn.first == "\\RD_CLK" ? "\\RD_CLK_ENABLE" : "\\WR_CLK_ENABLE")[i] != State::S1)
						continue;

					if (cell->getParam(conn.first == "\\RD_CLK" ? "\\RD_CLK_POLARITY" : "\\WR_CLK_POLARITY")[i] == State::S1)
						clock_posedge.insert(clk[i]);
					else
						clock_negedge.insert(clk[i]);
				}
			}
			else
			if (cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_") && conn.first.in("\\CLK", "\\C"))
			{
				bool posedge = (cell->type == "$_DFF_N_") || (cell->type == "$dff" && cell->getParam("\\CLK_POLARITY").as_bool());
				for (auto bit : sigmap(conn.second)) {
					if (posedge)
						clock_posedge.insert(bit);
					else
						clock_negedge.insert(bit);
				}
			}
			else
			if (mod_clk_cache.count(cell->type) && mod_clk_cache.at(cell->type).count(conn.first))
			{
				for (auto bit : sigmap(conn.second)) {
					if (mod_clk_cache.at(cell->type).at(conn.first).first)
						clock_posedge.insert(bit);
					if (mod_clk_cache.at(cell->type).at(conn.first).second)
						clock_negedge.insert(bit);
				}
			}
			else
			{
				for (auto bit : sigmap(conn.second))
					noclock.insert(bit);
			}
		}

		for (auto bit : noclock) {
			clock_posedge.erase(bit);
			clock_negedge.erase(bit);
		}

		for (auto wire : module->wires())
		{
			if (!wire->port_input || GetSize(wire) != 1)
				continue;
			SigBit bit = sigmap(wire);
			if (clock_posedge.count(bit))
				mod_clk_cache[module->name][wire->name].first = true;
			if (clock_negedge.count(bit))
				mod_clk_cache[module->name][wire->name].second = true;
		}
	}

	~Smt2Worker()
	{
		for (auto &it : ids)
			free(it.second);
		ids.clear();
	}

	const char *get_id(Module *m)
	{
		return get_id(m->name);
	}

	const char *get_id(Cell *c)
	{
		return get_id(c->name);
	}

	const char *get_id(Wire *w)
	{
		return get_id(w->name);
	}

	void register_bool(RTLIL::SigBit bit, int id)
	{
		if (verbose) log("%*s-> register_bool: %s %d\n", 2+2*GetSize(recursive_cells), "",
				log_signal(bit), id);

		sigmap.apply(bit);
		log_assert(fcache.count(bit) == 0);
		fcache[bit] = std::pair<int, int>(id, -1);
	}

	void register_bv(RTLIL::SigSpec sig, int id)
	{
		if (verbose) log("%*s-> register_bv: %s %d\n", 2+2*GetSize(recursive_cells), "",
				log_signal(sig), id);

		log_assert(bvmode);
		sigmap.apply(sig);

		log_assert(bvsizes.count(id) == 0);
		bvsizes[id] = GetSize(sig);

		for (int i = 0; i < GetSize(sig); i++) {
			log_assert(fcache.count(sig[i]) == 0);
			fcache[sig[i]] = std::pair<int, int>(id, i);
		}
	}

	void register_boolvec(RTLIL::SigSpec sig, int id)
	{
		if (verbose) log("%*s-> register_boolvec: %s %d\n", 2+2*GetSize(recursive_cells), "",
				log_signal(sig), id);

		log_assert(bvmode);
		sigmap.apply(sig);
		register_bool(sig[0], id);

		for (int i = 1; i < GetSize(sig); i++)
			sigmap.add(sig[i], RTLIL::State::S0);
	}

	std::string get_bool(RTLIL::SigBit bit, const char *state_name = "state")
	{
		sigmap.apply(bit);

		if (bit.wire == nullptr)
			return bit == RTLIL::State::S1 ? "true" : "false";

		if (bit_driver.count(bit))
			export_cell(bit_driver.at(bit));
		sigmap.apply(bit);

		if (fcache.count(bit) == 0) {
			if (verbose) log("%*s-> external bool: %s\n", 2+2*GetSize(recursive_cells), "",
					log_signal(bit));
			makebits(stringf("%s#%d", get_id(module), idcounter), 0, log_signal(bit));
			register_bool(bit, idcounter++);
		}

		auto f = fcache.at(bit);
		if (f.second >= 0)
			return stringf("(= ((_ extract %d %d) (|%s#%d| %s)) #b1)", f.second, f.second, get_id(module), f.first, state_name);
		return stringf("(|%s#%d| %s)", get_id(module), f.first, state_name);
	}

	std::string get_bool(RTLIL::SigSpec sig, const char *state_name = "state")
	{
		return get_bool(sig.as_bit(), state_name);
	}

	std::string get_bv(RTLIL::SigSpec sig, const char *state_name = "state")
	{
		log_assert(bvmode);
		sigmap.apply(sig);

		std::vector<std::string> subexpr;

		SigSpec orig_sig;
		while (orig_sig != sig) {
			for (auto bit : sig)
				if (bit_driver.count(bit))
					export_cell(bit_driver.at(bit));
			orig_sig = sig;
			sigmap.apply(sig);
		}

		for (int i = 0, j = 1; i < GetSize(sig); i += j, j = 1)
		{
			if (sig[i].wire == nullptr) {
				while (i+j < GetSize(sig) && sig[i+j].wire == nullptr) j++;
				subexpr.push_back("#b");
				for (int k = i+j-1; k >= i; k--)
					subexpr.back() += sig[k] == RTLIL::State::S1 ? "1" : "0";
				continue;
			}

			if (fcache.count(sig[i]) && fcache.at(sig[i]).second == -1) {
				subexpr.push_back(stringf("(ite %s #b1 #b0)", get_bool(sig[i], state_name).c_str()));
				continue;
			}

			if (fcache.count(sig[i])) {
				auto t1 = fcache.at(sig[i]);
				while (i+j < GetSize(sig)) {
					if (fcache.count(sig[i+j]) == 0)
						break;
					auto t2 = fcache.at(sig[i+j]);
					if (t1.first != t2.first)
						break;
					if (t1.second+j != t2.second)
						break;
					j++;
				}
				if (t1.second == 0 && j == bvsizes.at(t1.first))
					subexpr.push_back(stringf("(|%s#%d| %s)", get_id(module), t1.first, state_name));
				else
					subexpr.push_back(stringf("((_ extract %d %d) (|%s#%d| %s))",
							t1.second + j - 1, t1.second, get_id(module), t1.first, state_name));
				continue;
			}

			std::set<RTLIL::SigBit> seen_bits = { sig[i] };
			while (i+j < GetSize(sig) && sig[i+j].wire && !fcache.count(sig[i+j]) && !seen_bits.count(sig[i+j]))
				seen_bits.insert(sig[i+j]), j++;

			if (verbose) log("%*s-> external bv: %s\n", 2+2*GetSize(recursive_cells), "",
					log_signal(sig.extract(i, j)));
			for (auto bit : sig.extract(i, j))
				log_assert(bit_driver.count(bit) == 0);
			makebits(stringf("%s#%d", get_id(module), idcounter), j, log_signal(sig.extract(i, j)));
			subexpr.push_back(stringf("(|%s#%d| %s)", get_id(module), idcounter, state_name));
			register_bv(sig.extract(i, j), idcounter++);
		}

		if (GetSize(subexpr) > 1) {
			std::string expr = "", end_str = "";
			for (int i = GetSize(subexpr)-1; i >= 0; i--) {
				if (i > 0) expr += " (concat", end_str += ")";
				expr += " " + subexpr[i];
			}
			return expr.substr(1) + end_str;
		} else {
			log_assert(GetSize(subexpr) == 1);
			return subexpr[0];
		}
	}

	void export_gate(RTLIL::Cell *cell, std::string expr)
	{
		RTLIL::SigBit bit = sigmap(cell->getPort("\\Y").as_bit());
		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bool(cell->getPort("\\A"));
			else if (ch == 'B') processed_expr += get_bool(cell->getPort("\\B"));
			else if (ch == 'C') processed_expr += get_bool(cell->getPort("\\C"));
			else if (ch == 'D') processed_expr += get_bool(cell->getPort("\\D"));
			else if (ch == 'S') processed_expr += get_bool(cell->getPort("\\S"));
			else processed_expr += ch;
		}

		if (verbose)
			log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "", log_id(cell));

		decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
				get_id(module), idcounter, get_id(module), processed_expr.c_str(), log_signal(bit)));
		register_bool(bit, idcounter++);
		recursive_cells.erase(cell);
	}

	void export_bvop(RTLIL::Cell *cell, std::string expr, char type = 0)
	{
		RTLIL::SigSpec sig_a, sig_b;
		RTLIL::SigSpec sig_y = sigmap(cell->getPort("\\Y"));
		bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
		int width = GetSize(sig_y);

		if (type == 's' || type == 'd' || type == 'b') {
			width = max(width, GetSize(cell->getPort("\\A")));
			if (cell->hasPort("\\B"))
				width = max(width, GetSize(cell->getPort("\\B")));
		}

		if (cell->hasPort("\\A")) {
			sig_a = cell->getPort("\\A");
			sig_a.extend_u0(width, is_signed);
		}

		if (cell->hasPort("\\B")) {
			sig_b = cell->getPort("\\B");
			sig_b.extend_u0(width, is_signed && !(type == 's'));
		}

		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bv(sig_a);
			else if (ch == 'B') processed_expr += get_bv(sig_b);
			else if (ch == 'P') processed_expr += get_bv(cell->getPort("\\B"));
			else if (ch == 'L') processed_expr += is_signed ? "a" : "l";
			else if (ch == 'U') processed_expr += is_signed ? "s" : "u";
			else processed_expr += ch;
		}

		if (width != GetSize(sig_y) && type != 'b')
			processed_expr = stringf("((_ extract %d 0) %s)", GetSize(sig_y)-1, processed_expr.c_str());

		if (verbose)
			log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "", log_id(cell));

		if (type == 'b') {
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
					get_id(module), idcounter, get_id(module), processed_expr.c_str(), log_signal(sig_y)));
			register_boolvec(sig_y, idcounter++);
		} else {
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
					get_id(module), idcounter, get_id(module), GetSize(sig_y), processed_expr.c_str(), log_signal(sig_y)));
			register_bv(sig_y, idcounter++);
		}

		recursive_cells.erase(cell);
	}

	void export_reduce(RTLIL::Cell *cell, std::string expr, bool identity_val)
	{
		RTLIL::SigSpec sig_y = sigmap(cell->getPort("\\Y"));
		std::string processed_expr;

		for (char ch : expr)
			if (ch == 'A' || ch == 'B') {
				RTLIL::SigSpec sig = sigmap(cell->getPort(stringf("\\%c", ch)));
				for (auto bit : sig)
					processed_expr += " " + get_bool(bit);
				if (GetSize(sig) == 1)
					processed_expr += identity_val ? " true" : " false";
			} else
				processed_expr += ch;

		if (verbose)
			log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "", log_id(cell));

		decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
				get_id(module), idcounter, get_id(module), processed_expr.c_str(), log_signal(sig_y)));
		register_boolvec(sig_y, idcounter++);
		recursive_cells.erase(cell);
	}

	void export_cell(RTLIL::Cell *cell)
	{
		if (verbose)
			log("%*s=> export_cell %s (%s) [%s]\n", 2+2*GetSize(recursive_cells), "",
					log_id(cell), log_id(cell->type), exported_cells.count(cell) ? "old" : "new");

		if (recursive_cells.count(cell))
			log_error("Found logic loop in module %s! See cell %s.\n", get_id(module), get_id(cell));

		if (exported_cells.count(cell))
			return;

		exported_cells.insert(cell);
		recursive_cells.insert(cell);

		if (cell->type == "$initstate")
		{
			SigBit bit = sigmap(cell->getPort("\\Y").as_bit());
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool (|%s_is| state)) ; %s\n",
					get_id(module), idcounter, get_id(module), get_id(module), log_signal(bit)));
			register_bool(bit, idcounter++);
			recursive_cells.erase(cell);
			return;
		}

		if (cell->type.in("$_FF_", "$_DFF_P_", "$_DFF_N_"))
		{
			registers.insert(cell);
			makebits(stringf("%s#%d", get_id(module), idcounter), 0, log_signal(cell->getPort("\\Q")));
			register_bool(cell->getPort("\\Q"), idcounter++);
			recursive_cells.erase(cell);
			return;
		}

		if (cell->type == "$_BUF_") return export_gate(cell, "A");
		if (cell->type == "$_NOT_") return export_gate(cell, "(not A)");
		if (cell->type == "$_AND_") return export_gate(cell, "(and A B)");
		if (cell->type == "$_NAND_") return export_gate(cell, "(not (and A B))");
		if (cell->type == "$_OR_") return export_gate(cell, "(or A B)");
		if (cell->type == "$_NOR_") return export_gate(cell, "(not (or A B))");
		if (cell->type == "$_XOR_") return export_gate(cell, "(xor A B)");
		if (cell->type == "$_XNOR_") return export_gate(cell, "(not (xor A B))");
		if (cell->type == "$_ANDNOT_") return export_gate(cell, "(and A (not B))");
		if (cell->type == "$_ORNOT_") return export_gate(cell, "(or A (not B))");
		if (cell->type == "$_MUX_") return export_gate(cell, "(ite S B A)");
		if (cell->type == "$_NMUX_") return export_gate(cell, "(not (ite S B A))");
		if (cell->type == "$_AOI3_") return export_gate(cell, "(not (or (and A B) C))");
		if (cell->type == "$_OAI3_") return export_gate(cell, "(not (and (or A B) C))");
		if (cell->type == "$_AOI4_") return export_gate(cell, "(not (or (and A B) (and C D)))");
		if (cell->type == "$_OAI4_") return export_gate(cell, "(not (and (or A B) (or C D)))");

		// FIXME: $lut

		if (bvmode)
		{
			if (cell->type.in("$ff", "$dff"))
			{
				registers.insert(cell);
				makebits(stringf("%s#%d", get_id(module), idcounter), GetSize(cell->getPort("\\Q")), log_signal(cell->getPort("\\Q")));
				register_bv(cell->getPort("\\Q"), idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			if (cell->type.in("$anyconst", "$anyseq", "$allconst", "$allseq"))
			{
				registers.insert(cell);
				string infostr = cell->attributes.count("\\src") ? cell->attributes.at("\\src").decode_string().c_str() : get_id(cell);
				if (cell->attributes.count("\\reg"))
					infostr += " " + cell->attributes.at("\\reg").decode_string();
				decls.push_back(stringf("; yosys-smt2-%s %s#%d %d %s\n", cell->type.c_str() + 1, get_id(module), idcounter, GetSize(cell->getPort("\\Y")), infostr.c_str()));
				makebits(stringf("%s#%d", get_id(module), idcounter), GetSize(cell->getPort("\\Y")), log_signal(cell->getPort("\\Y")));
				if (cell->type == "$anyseq")
					ex_input_eq.push_back(stringf("  (= (|%s#%d| state) (|%s#%d| other_state))", get_id(module), idcounter, get_id(module), idcounter));
				register_bv(cell->getPort("\\Y"), idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			if (cell->type == "$and") return export_bvop(cell, "(bvand A B)");
			if (cell->type == "$or") return export_bvop(cell, "(bvor A B)");
			if (cell->type == "$xor") return export_bvop(cell, "(bvxor A B)");
			if (cell->type == "$xnor") return export_bvop(cell, "(bvxnor A B)");

			if (cell->type == "$shl") return export_bvop(cell, "(bvshl A B)", 's');
			if (cell->type == "$shr") return export_bvop(cell, "(bvlshr A B)", 's');
			if (cell->type == "$sshl") return export_bvop(cell, "(bvshl A B)", 's');
			if (cell->type == "$sshr") return export_bvop(cell, "(bvLshr A B)", 's');

			if (cell->type.in("$shift", "$shiftx")) {
				if (cell->getParam("\\B_SIGNED").as_bool()) {
					return export_bvop(cell, stringf("(ite (bvsge P #b%0*d) "
							"(bvlshr A B) (bvlshr A (bvneg B)))",
							GetSize(cell->getPort("\\B")), 0), 's');
				} else {
					return export_bvop(cell, "(bvlshr A B)", 's');
				}
			}

			if (cell->type == "$lt") return export_bvop(cell, "(bvUlt A B)", 'b');
			if (cell->type == "$le") return export_bvop(cell, "(bvUle A B)", 'b');
			if (cell->type == "$ge") return export_bvop(cell, "(bvUge A B)", 'b');
			if (cell->type == "$gt") return export_bvop(cell, "(bvUgt A B)", 'b');

			if (cell->type == "$ne") return export_bvop(cell, "(distinct A B)", 'b');
			if (cell->type == "$nex") return export_bvop(cell, "(distinct A B)", 'b');
			if (cell->type == "$eq") return export_bvop(cell, "(= A B)", 'b');
			if (cell->type == "$eqx") return export_bvop(cell, "(= A B)", 'b');

			if (cell->type == "$not") return export_bvop(cell, "(bvnot A)");
			if (cell->type == "$pos") return export_bvop(cell, "A");
			if (cell->type == "$neg") return export_bvop(cell, "(bvneg A)");

			if (cell->type == "$add") return export_bvop(cell, "(bvadd A B)");
			if (cell->type == "$sub") return export_bvop(cell, "(bvsub A B)");
			if (cell->type == "$mul") return export_bvop(cell, "(bvmul A B)");
			if (cell->type == "$div") return export_bvop(cell, "(bvUdiv A B)", 'd');
			if (cell->type == "$mod") return export_bvop(cell, "(bvUrem A B)", 'd');

			if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_bool") &&
					2*GetSize(cell->getPort("\\A").chunks()) < GetSize(cell->getPort("\\A"))) {
				bool is_and = cell->type == "$reduce_and";
				string bits(GetSize(cell->getPort("\\A")), is_and ? '1' : '0');
				return export_bvop(cell, stringf("(%s A #b%s)", is_and ? "=" : "distinct", bits.c_str()), 'b');
			}

			if (cell->type == "$reduce_and") return export_reduce(cell, "(and A)", true);
			if (cell->type == "$reduce_or") return export_reduce(cell, "(or A)", false);
			if (cell->type == "$reduce_xor") return export_reduce(cell, "(xor A)", false);
			if (cell->type == "$reduce_xnor") return export_reduce(cell, "(not (xor A))", false);
			if (cell->type == "$reduce_bool") return export_reduce(cell, "(or A)", false);

			if (cell->type == "$logic_not") return export_reduce(cell, "(not (or A))", false);
			if (cell->type == "$logic_and") return export_reduce(cell, "(and (or A) (or B))", false);
			if (cell->type == "$logic_or") return export_reduce(cell, "(or A B)", false);

			if (cell->type.in("$mux", "$pmux"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				std::string processed_expr = get_bv(cell->getPort("\\A"));

				RTLIL::SigSpec sig_b = cell->getPort("\\B");
				RTLIL::SigSpec sig_s = cell->getPort("\\S");
				get_bv(sig_b);
				get_bv(sig_s);

				for (int i = 0; i < GetSize(sig_s); i++)
					processed_expr = stringf("(ite %s %s %s)", get_bool(sig_s[i]).c_str(),
							get_bv(sig_b.extract(i*width, width)).c_str(), processed_expr.c_str());

				if (verbose)
					log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "", log_id(cell));

				RTLIL::SigSpec sig = sigmap(cell->getPort("\\Y"));
				decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
						get_id(module), idcounter, get_id(module), width, processed_expr.c_str(), log_signal(sig)));
				register_bv(sig, idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			// FIXME: $slice $concat
		}

		if (memmode && cell->type == "$mem")
		{
			int arrayid = idcounter++;
			memarrays[cell] = arrayid;

			int abits = cell->getParam("\\ABITS").as_int();
			int width = cell->getParam("\\WIDTH").as_int();
			int rd_ports = cell->getParam("\\RD_PORTS").as_int();
			int wr_ports = cell->getParam("\\WR_PORTS").as_int();

			bool async_read = false;
			if (!cell->getParam("\\WR_CLK_ENABLE").is_fully_ones()) {
				if (!cell->getParam("\\WR_CLK_ENABLE").is_fully_zero())
					log_error("Memory %s.%s has mixed clocked/nonclocked write ports. This is not supported by \"write_smt2\".\n", log_id(cell), log_id(module));
				async_read = true;
			}

			decls.push_back(stringf("; yosys-smt2-memory %s %d %d %d %d %s\n", get_id(cell), abits, width, rd_ports, wr_ports, async_read ? "async" : "sync"));

			string memstate;
			if (async_read) {
				memstate = stringf("%s#%d#final", get_id(module), arrayid);
			} else {
				memstate = stringf("%s#%d#0", get_id(module), arrayid);
			}

			if (statebv)
			{
				int mem_size = cell->getParam("\\SIZE").as_int();
				int mem_offset = cell->getParam("\\OFFSET").as_int();

				makebits(memstate, width*mem_size, get_id(cell));
				decls.push_back(stringf("(define-fun |%s_m %s| ((state |%s_s|)) (_ BitVec %d) (|%s| state))\n",
						get_id(module), get_id(cell), get_id(module), width*mem_size, memstate.c_str()));

				for (int i = 0; i < rd_ports; i++)
				{
					SigSpec addr_sig = cell->getPort("\\RD_ADDR").extract(abits*i, abits);
					SigSpec data_sig = cell->getPort("\\RD_DATA").extract(width*i, width);
					std::string addr = get_bv(addr_sig);

					if (cell->getParam("\\RD_CLK_ENABLE").extract(i).as_bool())
						log_error("Read port %d (%s) of memory %s.%s is clocked. This is not supported by \"write_smt2\"! "
								"Call \"memory\" with -nordff to avoid this error.\n", i, log_signal(data_sig), log_id(cell), log_id(module));

					decls.push_back(stringf("(define-fun |%s_m:R%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
							get_id(module), i, get_id(cell), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));

					std::string read_expr = "#b";
					for (int k = 0; k < width; k++)
						read_expr += "0";

					for (int k = 0; k < mem_size; k++)
						read_expr = stringf("(ite (= (|%s_m:R%dA %s| state) #b%s) ((_ extract %d %d) (|%s| state))\n  %s)",
								get_id(module), i, get_id(cell), Const(k+mem_offset, abits).as_string().c_str(),
								width*(k+1)-1, width*k, memstate.c_str(), read_expr.c_str());

					decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d)\n  %s) ; %s\n",
							get_id(module), idcounter, get_id(module), width, read_expr.c_str(), log_signal(data_sig)));

					decls.push_back(stringf("(define-fun |%s_m:R%dD %s| ((state |%s_s|)) (_ BitVec %d) (|%s#%d| state))\n",
							get_id(module), i, get_id(cell), get_id(module), width, get_id(module), idcounter));

					register_bv(data_sig, idcounter++);
				}
			}
			else
			{
				if (statedt)
					dtmembers.push_back(stringf("  (|%s| (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
							memstate.c_str(), abits, width, get_id(cell)));
				else
					decls.push_back(stringf("(declare-fun |%s| (|%s_s|) (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
							memstate.c_str(), get_id(module), abits, width, get_id(cell)));

				decls.push_back(stringf("(define-fun |%s_m %s| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) (|%s| state))\n",
						get_id(module), get_id(cell), get_id(module), abits, width, memstate.c_str()));

				for (int i = 0; i < rd_ports; i++)
				{
					SigSpec addr_sig = cell->getPort("\\RD_ADDR").extract(abits*i, abits);
					SigSpec data_sig = cell->getPort("\\RD_DATA").extract(width*i, width);
					std::string addr = get_bv(addr_sig);

					if (cell->getParam("\\RD_CLK_ENABLE").extract(i).as_bool())
						log_error("Read port %d (%s) of memory %s.%s is clocked. This is not supported by \"write_smt2\"! "
								"Call \"memory\" with -nordff to avoid this error.\n", i, log_signal(data_sig), log_id(cell), log_id(module));

					decls.push_back(stringf("(define-fun |%s_m:R%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
							get_id(module), i, get_id(cell), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));

					decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) (select (|%s| state) (|%s_m:R%dA %s| state))) ; %s\n",
							get_id(module), idcounter, get_id(module), width, memstate.c_str(), get_id(module), i, get_id(cell), log_signal(data_sig)));

					decls.push_back(stringf("(define-fun |%s_m:R%dD %s| ((state |%s_s|)) (_ BitVec %d) (|%s#%d| state))\n",
							get_id(module), i, get_id(cell), get_id(module), width, get_id(module), idcounter));

					register_bv(data_sig, idcounter++);
				}
			}

			registers.insert(cell);
			recursive_cells.erase(cell);
			return;
		}

		Module *m = module->design->module(cell->type);

		if (m != nullptr)
		{
			decls.push_back(stringf("; yosys-smt2-cell %s %s\n", get_id(cell->type), get_id(cell->name)));
			string cell_state = stringf("(|%s_h %s| state)", get_id(module), get_id(cell->name));

			for (auto &conn : cell->connections())
			{
				if (GetSize(conn.second) == 0)
					continue;

				Wire *w = m->wire(conn.first);
				SigSpec sig = sigmap(conn.second);

				if (w->port_output && !w->port_input) {
					if (GetSize(w) > 1) {
						if (bvmode) {
							makebits(stringf("%s#%d", get_id(module), idcounter), GetSize(w), log_signal(sig));
							register_bv(sig, idcounter++);
						} else {
							for (int i = 0; i < GetSize(w); i++) {
								makebits(stringf("%s#%d", get_id(module), idcounter), 0, log_signal(sig[i]));
								register_bool(sig[i], idcounter++);
							}
						}
					} else {
						makebits(stringf("%s#%d", get_id(module), idcounter), 0, log_signal(sig));
						register_bool(sig, idcounter++);
					}
				}
			}

			if (statebv)
				makebits(stringf("%s_h %s", get_id(module), get_id(cell->name)), mod_stbv_width.at(cell->type));
			else if (statedt)
				dtmembers.push_back(stringf("  (|%s_h %s| |%s_s|)\n",
						get_id(module), get_id(cell->name), get_id(cell->type)));
			else
				decls.push_back(stringf("(declare-fun |%s_h %s| (|%s_s|) |%s_s|)\n",
						get_id(module), get_id(cell->name), get_id(module), get_id(cell->type)));

			hiercells.insert(cell);
			hiercells_queue.insert(cell);
			recursive_cells.erase(cell);
			return;
		}

		log_error("Unsupported cell type %s for cell %s.%s.\n",
				log_id(cell->type), log_id(module), log_id(cell));
	}

	void run()
	{
		if (verbose) log("=> export logic driving outputs\n");

		pool<SigBit> reg_bits;
		for (auto cell : module->cells())
			if (cell->type.in("$ff", "$dff", "$_FF_", "$_DFF_P_", "$_DFF_N_")) {
				// not using sigmap -- we want the net directly at the dff output
				for (auto bit : cell->getPort("\\Q"))
					reg_bits.insert(bit);
			}

		for (auto wire : module->wires()) {
			bool is_register = false;
			for (auto bit : SigSpec(wire))
				if (reg_bits.count(bit))
					is_register = true;
			if (wire->port_id || is_register || wire->get_bool_attribute("\\keep") || (wiresmode && wire->name[0] == '\\')) {
				RTLIL::SigSpec sig = sigmap(wire);
				if (wire->port_input)
					decls.push_back(stringf("; yosys-smt2-input %s %d\n", get_id(wire), wire->width));
				if (wire->port_output)
					decls.push_back(stringf("; yosys-smt2-output %s %d\n", get_id(wire), wire->width));
				if (is_register)
					decls.push_back(stringf("; yosys-smt2-register %s %d\n", get_id(wire), wire->width));
				if (wire->get_bool_attribute("\\keep") || (wiresmode && wire->name[0] == '\\'))
					decls.push_back(stringf("; yosys-smt2-wire %s %d\n", get_id(wire), wire->width));
				if (GetSize(wire) == 1 && (clock_posedge.count(sig) || clock_negedge.count(sig)))
					decls.push_back(stringf("; yosys-smt2-clock %s%s%s\n", get_id(wire),
							clock_posedge.count(sig) ? " posedge" : "", clock_negedge.count(sig) ? " negedge" : ""));
				if (bvmode && GetSize(sig) > 1) {
					decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) (_ BitVec %d) %s)\n",
							get_id(module), get_id(wire), get_id(module), GetSize(sig), get_bv(sig).c_str()));
					if (wire->port_input)
						ex_input_eq.push_back(stringf("  (= (|%s_n %s| state) (|%s_n %s| other_state))",
								get_id(module), get_id(wire), get_id(module), get_id(wire)));
				} else {
					for (int i = 0; i < GetSize(sig); i++)
						if (GetSize(sig) > 1) {
							decls.push_back(stringf("(define-fun |%s_n %s %d| ((state |%s_s|)) Bool %s)\n",
									get_id(module), get_id(wire), i, get_id(module), get_bool(sig[i]).c_str()));
							if (wire->port_input)
								ex_input_eq.push_back(stringf("  (= (|%s_n %s %d| state) (|%s_n %s %d| other_state))",
										get_id(module), get_id(wire), i, get_id(module), get_id(wire), i));
						} else {
							decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) Bool %s)\n",
									get_id(module), get_id(wire), get_id(module), get_bool(sig[i]).c_str()));
							if (wire->port_input)
								ex_input_eq.push_back(stringf("  (= (|%s_n %s| state) (|%s_n %s| other_state))",
										get_id(module), get_id(wire), get_id(module), get_id(wire)));
						}
				}
			}
		}

		if (verbose) log("=> export logic associated with the initial state\n");

		vector<string> init_list;
		for (auto wire : module->wires())
			if (wire->attributes.count("\\init")) {
				RTLIL::SigSpec sig = sigmap(wire);
				Const val = wire->attributes.at("\\init");
				val.bits.resize(GetSize(sig), State::Sx);
				if (bvmode && GetSize(sig) > 1) {
					Const mask(State::S1, GetSize(sig));
					bool use_mask = false;
					for (int i = 0; i < GetSize(sig); i++)
						if (val[i] != State::S0 && val[i] != State::S1) {
							val[i] = State::S0;
							mask[i] = State::S0;
							use_mask = true;
						}
					if (use_mask)
						init_list.push_back(stringf("(= (bvand %s #b%s) #b%s) ; %s", get_bv(sig).c_str(), mask.as_string().c_str(), val.as_string().c_str(), get_id(wire)));
					else
						init_list.push_back(stringf("(= %s #b%s) ; %s", get_bv(sig).c_str(), val.as_string().c_str(), get_id(wire)));
				} else {
					for (int i = 0; i < GetSize(sig); i++)
						if (val[i] == State::S0 || val[i] == State::S1)
							init_list.push_back(stringf("(= %s %s) ; %s", get_bool(sig[i]).c_str(), val[i] == State::S1 ? "true" : "false", get_id(wire)));
				}
			}

		if (verbose) log("=> export logic driving asserts\n");

		int assert_id = 0, assume_id = 0, cover_id = 0;
		vector<string> assert_list, assume_list, cover_list;

		for (auto cell : module->cells())
		{
			if (cell->type.in("$assert", "$assume", "$cover"))
			{
				int &id = cell->type == "$assert" ? assert_id :
						cell->type == "$assume" ? assume_id :
						cell->type == "$cover" ? cover_id : *(int*)nullptr;

				char postfix = cell->type == "$assert" ? 'a' :
						cell->type == "$assume" ? 'u' :
						cell->type == "$cover" ? 'c' : 0;

				string name_a = get_bool(cell->getPort("\\A"));
				string name_en = get_bool(cell->getPort("\\EN"));
				string infostr = (cell->name[0] == '$' && cell->attributes.count("\\src")) ? cell->attributes.at("\\src").decode_string() : get_id(cell);
				decls.push_back(stringf("; yosys-smt2-%s %d %s\n", cell->type.c_str() + 1, id, infostr.c_str()));

				if (cell->type == "$cover")
					decls.push_back(stringf("(define-fun |%s_%c %d| ((state |%s_s|)) Bool (and %s %s)) ; %s\n",
							get_id(module), postfix, id, get_id(module), name_a.c_str(), name_en.c_str(), get_id(cell)));
				else
					decls.push_back(stringf("(define-fun |%s_%c %d| ((state |%s_s|)) Bool (or %s (not %s))) ; %s\n",
							get_id(module), postfix, id, get_id(module), name_a.c_str(), name_en.c_str(), get_id(cell)));

				if (cell->type == "$assert")
					assert_list.push_back(stringf("(|%s_a %d| state)", get_id(module), id));
				else if (cell->type == "$assume")
					assume_list.push_back(stringf("(|%s_u %d| state)", get_id(module), id));

				id++;
			}
		}

		if (verbose) log("=> export logic driving hierarchical cells\n");

		for (auto cell : module->cells())
			if (module->design->module(cell->type) != nullptr)
				export_cell(cell);

		while (!hiercells_queue.empty())
		{
			std::set<RTLIL::Cell*> queue;
			queue.swap(hiercells_queue);

			for (auto cell : queue)
			{
				string cell_state = stringf("(|%s_h %s| state)", get_id(module), get_id(cell->name));
				Module *m = module->design->module(cell->type);
				log_assert(m != nullptr);

				hier.push_back(stringf("  (= (|%s_is| state) (|%s_is| %s))\n",
						get_id(module), get_id(cell->type), cell_state.c_str()));

				for (auto &conn : cell->connections())
				{
					if (GetSize(conn.second) == 0)
						continue;

					Wire *w = m->wire(conn.first);
					SigSpec sig = sigmap(conn.second);

					if (bvmode || GetSize(w) == 1) {
						hier.push_back(stringf("  (= %s (|%s_n %s| %s)) ; %s.%s\n", (GetSize(w) > 1 ? get_bv(sig) : get_bool(sig)).c_str(),
								get_id(cell->type), get_id(w), cell_state.c_str(), get_id(cell->type), get_id(w)));
					} else {
						for (int i = 0; i < GetSize(w); i++)
							hier.push_back(stringf("  (= %s (|%s_n %s %d| %s)) ; %s.%s[%d]\n", get_bool(sig[i]).c_str(),
									get_id(cell->type), get_id(w), i, cell_state.c_str(), get_id(cell->type), get_id(w), i));
					}
				}
			}
		}

		for (int iter = 1; !registers.empty(); iter++)
		{
			pool<Cell*> this_regs;
			this_regs.swap(registers);

			if (verbose) log("=> export logic driving registers [iteration %d]\n", iter);

			for (auto cell : this_regs)
			{
				if (cell->type.in("$_FF_", "$_DFF_P_", "$_DFF_N_"))
				{
					std::string expr_d = get_bool(cell->getPort("\\D"));
					std::string expr_q = get_bool(cell->getPort("\\Q"), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort("\\Q"))));
					ex_state_eq.push_back(stringf("(= %s %s)", get_bool(cell->getPort("\\Q")).c_str(), get_bool(cell->getPort("\\Q"), "other_state").c_str()));
				}

				if (cell->type.in("$ff", "$dff"))
				{
					std::string expr_d = get_bv(cell->getPort("\\D"));
					std::string expr_q = get_bv(cell->getPort("\\Q"), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort("\\Q"))));
					ex_state_eq.push_back(stringf("(= %s %s)", get_bv(cell->getPort("\\Q")).c_str(), get_bv(cell->getPort("\\Q"), "other_state").c_str()));
				}

				if (cell->type.in("$anyconst", "$allconst"))
				{
					std::string expr_d = get_bv(cell->getPort("\\Y"));
					std::string expr_q = get_bv(cell->getPort("\\Y"), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort("\\Y"))));
					if (cell->type == "$anyconst")
						ex_state_eq.push_back(stringf("(= %s %s)", get_bv(cell->getPort("\\Y")).c_str(), get_bv(cell->getPort("\\Y"), "other_state").c_str()));
				}

				if (cell->type == "$mem")
				{
					int arrayid = memarrays.at(cell);

					int abits = cell->getParam("\\ABITS").as_int();
					int width = cell->getParam("\\WIDTH").as_int();
					int wr_ports = cell->getParam("\\WR_PORTS").as_int();

					bool async_read = false;
					string initial_memstate, final_memstate;

					if (!cell->getParam("\\WR_CLK_ENABLE").is_fully_ones()) {
						log_assert(cell->getParam("\\WR_CLK_ENABLE").is_fully_zero());
						async_read = true;
						initial_memstate = stringf("%s#%d#0", get_id(module), arrayid);
						final_memstate = stringf("%s#%d#final", get_id(module), arrayid);
					}

					if (statebv)
					{
						int mem_size = cell->getParam("\\SIZE").as_int();
						int mem_offset = cell->getParam("\\OFFSET").as_int();

						if (async_read) {
							makebits(final_memstate, width*mem_size, get_id(cell));
						}

						for (int i = 0; i < wr_ports; i++)
						{
							SigSpec addr_sig = cell->getPort("\\WR_ADDR").extract(abits*i, abits);
							SigSpec data_sig = cell->getPort("\\WR_DATA").extract(width*i, width);
							SigSpec mask_sig = cell->getPort("\\WR_EN").extract(width*i, width);

							std::string addr = get_bv(addr_sig);
							std::string data = get_bv(data_sig);
							std::string mask = get_bv(mask_sig);

							decls.push_back(stringf("(define-fun |%s_m:W%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));
							addr = stringf("(|%s_m:W%dA %s| state)", get_id(module), i, get_id(cell));

							decls.push_back(stringf("(define-fun |%s_m:W%dD %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), width, data.c_str(), log_signal(data_sig)));
							data = stringf("(|%s_m:W%dD %s| state)", get_id(module), i, get_id(cell));

							decls.push_back(stringf("(define-fun |%s_m:W%dM %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), width, mask.c_str(), log_signal(mask_sig)));
							mask = stringf("(|%s_m:W%dM %s| state)", get_id(module), i, get_id(cell));

							std::string data_expr;

							for (int k = mem_size-1; k >= 0; k--) {
								std::string new_data = stringf("(bvor (bvand %s %s) (bvand ((_ extract %d %d) (|%s#%d#%d| state)) (bvnot %s)))",
										data.c_str(), mask.c_str(), width*(k+1)-1, width*k, get_id(module), arrayid, i, mask.c_str());
								data_expr += stringf("\n  (ite (= %s #b%s) %s ((_ extract %d %d) (|%s#%d#%d| state)))",
										addr.c_str(), Const(k+mem_offset, abits).as_string().c_str(), new_data.c_str(),
										width*(k+1)-1, width*k, get_id(module), arrayid, i);
							}

							decls.push_back(stringf("(define-fun |%s#%d#%d| ((state |%s_s|)) (_ BitVec %d) (concat%s)) ; %s\n",
									get_id(module), arrayid, i+1, get_id(module), width*mem_size, data_expr.c_str(), get_id(cell)));
						}
					}
					else
					{
						if (async_read) {
							if (statedt)
								dtmembers.push_back(stringf("  (|%s| (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
										initial_memstate.c_str(), abits, width, get_id(cell)));
							else
								decls.push_back(stringf("(declare-fun |%s| (|%s_s|) (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
										initial_memstate.c_str(), get_id(module), abits, width, get_id(cell)));
						}

						for (int i = 0; i < wr_ports; i++)
						{
							SigSpec addr_sig = cell->getPort("\\WR_ADDR").extract(abits*i, abits);
							SigSpec data_sig = cell->getPort("\\WR_DATA").extract(width*i, width);
							SigSpec mask_sig = cell->getPort("\\WR_EN").extract(width*i, width);

							std::string addr = get_bv(addr_sig);
							std::string data = get_bv(data_sig);
							std::string mask = get_bv(mask_sig);

							decls.push_back(stringf("(define-fun |%s_m:W%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));
							addr = stringf("(|%s_m:W%dA %s| state)", get_id(module), i, get_id(cell));

							decls.push_back(stringf("(define-fun |%s_m:W%dD %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), width, data.c_str(), log_signal(data_sig)));
							data = stringf("(|%s_m:W%dD %s| state)", get_id(module), i, get_id(cell));

							decls.push_back(stringf("(define-fun |%s_m:W%dM %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
									get_id(module), i, get_id(cell), get_id(module), width, mask.c_str(), log_signal(mask_sig)));
							mask = stringf("(|%s_m:W%dM %s| state)", get_id(module), i, get_id(cell));

							data = stringf("(bvor (bvand %s %s) (bvand (select (|%s#%d#%d| state) %s) (bvnot %s)))",
									data.c_str(), mask.c_str(), get_id(module), arrayid, i, addr.c_str(), mask.c_str());

							decls.push_back(stringf("(define-fun |%s#%d#%d| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) "
									"(store (|%s#%d#%d| state) %s %s)) ; %s\n",
									get_id(module), arrayid, i+1, get_id(module), abits, width,
									get_id(module), arrayid, i, addr.c_str(), data.c_str(), get_id(cell)));
						}
					}

					std::string expr_d = stringf("(|%s#%d#%d| state)", get_id(module), arrayid, wr_ports);
					std::string expr_q = stringf("(|%s#%d#0| next_state)", get_id(module), arrayid);
					trans.push_back(stringf("  (= %s %s) ; %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell)));
					ex_state_eq.push_back(stringf("(= (|%s#%d#0| state) (|%s#%d#0| other_state))", get_id(module), arrayid, get_id(module), arrayid));

					if (async_read)
						hier.push_back(stringf("  (= %s (|%s| state)) ; %s\n", expr_d.c_str(), final_memstate.c_str(), get_id(cell)));

					Const init_data = cell->getParam("\\INIT");
					int memsize = cell->getParam("\\SIZE").as_int();

					for (int i = 0; i < memsize; i++)
					{
						if (i*width >= GetSize(init_data))
							break;

						Const initword = init_data.extract(i*width, width, State::Sx);
						Const initmask = initword;
						bool gen_init_constr = false;

						for (int k = 0; k < GetSize(initword); k++) {
							if (initword[k] == State::S0 || initword[k] == State::S1) {
								gen_init_constr = true;
								initmask[k] = State::S1;
							} else {
								initmask[k] = State::S0;
								initword[k] = State::S0;
							}
						}

						if (gen_init_constr)
						{
							if (statebv)
								/* FIXME */;
							else
								init_list.push_back(stringf("(= (bvand (select (|%s#%d#0| state) #b%s) #b%s) #b%s) ; %s[%d]",
										get_id(module), arrayid, Const(i, abits).as_string().c_str(),
										initmask.as_string().c_str(), initword.as_string().c_str(), get_id(cell), i));
						}
					}
				}
			}
		}

		if (verbose) log("=> finalizing SMT2 representation of %s.\n", log_id(module));

		for (auto c : hiercells) {
			assert_list.push_back(stringf("(|%s_a| (|%s_h %s| state))", get_id(c->type), get_id(module), get_id(c->name)));
			assume_list.push_back(stringf("(|%s_u| (|%s_h %s| state))", get_id(c->type), get_id(module), get_id(c->name)));
			init_list.push_back(stringf("(|%s_i| (|%s_h %s| state))", get_id(c->type), get_id(module), get_id(c->name)));
			hier.push_back(stringf("  (|%s_h| (|%s_h %s| state))\n", get_id(c->type), get_id(module), get_id(c->name)));
			trans.push_back(stringf("  (|%s_t| (|%s_h %s| state) (|%s_h %s| next_state))\n",
					get_id(c->type), get_id(module), get_id(c->name), get_id(module), get_id(c->name)));
			ex_state_eq.push_back(stringf("(|%s_ex_state_eq| (|%s_h %s| state) (|%s_h %s| other_state))\n",
					get_id(c->type), get_id(module), get_id(c->name), get_id(module), get_id(c->name)));
		}

		if (forallmode)
		{
			string expr = ex_state_eq.empty() ? "true" : "(and";
			if (!ex_state_eq.empty()) {
				if (GetSize(ex_state_eq) == 1) {
					expr = "\n  " + ex_state_eq.front() + "\n";
				} else {
					for (auto &str : ex_state_eq)
						expr += stringf("\n  %s", str.c_str());
					expr += "\n)";
				}
			}
			decls.push_back(stringf("(define-fun |%s_ex_state_eq| ((state |%s_s|) (other_state |%s_s|)) Bool %s)\n",
				get_id(module), get_id(module), get_id(module), expr.c_str()));

			expr = ex_input_eq.empty() ? "true" : "(and";
			if (!ex_input_eq.empty()) {
				if (GetSize(ex_input_eq) == 1) {
					expr = "\n  " + ex_input_eq.front() + "\n";
				} else {
					for (auto &str : ex_input_eq)
						expr += stringf("\n  %s", str.c_str());
					expr += "\n)";
				}
			}
			decls.push_back(stringf("(define-fun |%s_ex_input_eq| ((state |%s_s|) (other_state |%s_s|)) Bool %s)\n",
				get_id(module), get_id(module), get_id(module), expr.c_str()));
		}

		string assert_expr = assert_list.empty() ? "true" : "(and";
		if (!assert_list.empty()) {
			if (GetSize(assert_list) == 1) {
				assert_expr = "\n  " + assert_list.front() + "\n";
			} else {
				for (auto &str : assert_list)
					assert_expr += stringf("\n  %s", str.c_str());
				assert_expr += "\n)";
			}
		}
		decls.push_back(stringf("(define-fun |%s_a| ((state |%s_s|)) Bool %s)\n",
				get_id(module), get_id(module), assert_expr.c_str()));

		string assume_expr = assume_list.empty() ? "true" : "(and";
		if (!assume_list.empty()) {
			if (GetSize(assume_list) == 1) {
				assume_expr = "\n  " + assume_list.front() + "\n";
			} else {
				for (auto &str : assume_list)
					assume_expr += stringf("\n  %s", str.c_str());
				assume_expr += "\n)";
			}
		}
		decls.push_back(stringf("(define-fun |%s_u| ((state |%s_s|)) Bool %s)\n",
				get_id(module), get_id(module), assume_expr.c_str()));

		string init_expr = init_list.empty() ? "true" : "(and";
		if (!init_list.empty()) {
			if (GetSize(init_list) == 1) {
				init_expr = "\n  " + init_list.front() + "\n";
			} else {
				for (auto &str : init_list)
					init_expr += stringf("\n  %s", str.c_str());
				init_expr += "\n)";
			}
		}
		decls.push_back(stringf("(define-fun |%s_i| ((state |%s_s|)) Bool %s)\n",
				get_id(module), get_id(module), init_expr.c_str()));
	}

	void write(std::ostream &f)
	{
		f << stringf("; yosys-smt2-module %s\n", get_id(module));

		if (statebv) {
			f << stringf("(define-sort |%s_s| () (_ BitVec %d))\n", get_id(module), statebv_width);
			mod_stbv_width[module->name] = statebv_width;
		} else
		if (statedt) {
			f << stringf("(declare-datatype |%s_s| ((|%s_mk|\n", get_id(module), get_id(module));
			for (auto it : dtmembers)
				f << it;
			f << stringf(")))\n");
		} else
			f << stringf("(declare-sort |%s_s| 0)\n", get_id(module));

		for (auto it : decls)
			f << it;

		f << stringf("(define-fun |%s_h| ((state |%s_s|)) Bool ", get_id(module), get_id(module));
		if (GetSize(hier) > 1) {
			f << "(and\n";
			for (auto it : hier)
				f << it;
			f << "))\n";
		} else
		if (GetSize(hier) == 1)
			f << "\n" + hier.front() + ")\n";
		else
			f << "true)\n";

		f << stringf("(define-fun |%s_t| ((state |%s_s|) (next_state |%s_s|)) Bool ", get_id(module), get_id(module), get_id(module));
		if (GetSize(trans) > 1) {
			f << "(and\n";
			for (auto it : trans)
				f << it;
			f << "))";
		} else
		if (GetSize(trans) == 1)
			f << "\n" + trans.front() + ")";
		else
			f << "true)";
		f << stringf(" ; end of module %s\n", get_id(module));
	}
};

struct Smt2Backend : public Backend {
	Smt2Backend() : Backend("smt2", "write design to SMT-LIBv2 file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smt2 [options] [filename]\n");
		log("\n");
		log("Write a SMT-LIBv2 [1] description of the current design. For a module with name\n");
		log("'<mod>' this will declare the sort '<mod>_s' (state of the module) and will\n");
		log("define and declare functions operating on that state.\n");
		log("\n");
		log("The following SMT2 functions are generated for a module with name '<mod>'.\n");
		log("Some declarations/definitions are printed with a special comment. A prover\n");
		log("using the SMT2 files can use those comments to collect all relevant metadata\n");
		log("about the design.\n");
		log("\n");
		log("    ; yosys-smt2-module <mod>\n");
		log("    (declare-sort |<mod>_s| 0)\n");
		log("        The sort representing a state of module <mod>.\n");
		log("\n");
		log("    (define-fun |<mod>_h| ((state |<mod>_s|)) Bool (...))\n");
		log("        This function must be asserted for each state to establish the\n");
		log("        design hierarchy.\n");
		log("\n");
		log("    ; yosys-smt2-input <wirename> <width>\n");
		log("    ; yosys-smt2-output <wirename> <width>\n");
		log("    ; yosys-smt2-register <wirename> <width>\n");
		log("    ; yosys-smt2-wire <wirename> <width>\n");
		log("    (define-fun |<mod>_n <wirename>| (|<mod>_s|) (_ BitVec <width>))\n");
		log("    (define-fun |<mod>_n <wirename>| (|<mod>_s|) Bool)\n");
		log("        For each port, register, and wire with the 'keep' attribute set an\n");
		log("        accessor function is generated. Single-bit wires are returned as Bool,\n");
		log("        multi-bit wires as BitVec.\n");
		log("\n");
		log("    ; yosys-smt2-cell <submod> <instancename>\n");
		log("    (declare-fun |<mod>_h <instancename>| (|<mod>_s|) |<submod>_s|)\n");
		log("        There is a function like that for each hierarchical instance. It\n");
		log("        returns the sort that represents the state of the sub-module that\n");
		log("        implements the instance.\n");
		log("\n");
		log("    (declare-fun |<mod>_is| (|<mod>_s|) Bool)\n");
		log("        This function must be asserted 'true' for initial states, and 'false'\n");
		log("        otherwise.\n");
		log("\n");
		log("    (define-fun |<mod>_i| ((state |<mod>_s|)) Bool (...))\n");
		log("        This function must be asserted 'true' for initial states. For\n");
		log("        non-initial states it must be left unconstrained.\n");
		log("\n");
		log("    (define-fun |<mod>_t| ((state |<mod>_s|) (next_state |<mod>_s|)) Bool (...))\n");
		log("        This function evaluates to 'true' if the states 'state' and\n");
		log("        'next_state' form a valid state transition.\n");
		log("\n");
		log("    (define-fun |<mod>_a| ((state |<mod>_s|)) Bool (...))\n");
		log("        This function evaluates to 'true' if all assertions hold in the state.\n");
		log("\n");
		log("    (define-fun |<mod>_u| ((state |<mod>_s|)) Bool (...))\n");
		log("        This function evaluates to 'true' if all assumptions hold in the state.\n");
		log("\n");
		log("    ; yosys-smt2-assert <id> <filename:linenum>\n");
		log("    (define-fun |<mod>_a <id>| ((state |<mod>_s|)) Bool (...))\n");
		log("        Each $assert cell is converted into one of this functions. The function\n");
		log("        evaluates to 'true' if the assert statement holds in the state.\n");
		log("\n");
		log("    ; yosys-smt2-assume <id> <filename:linenum>\n");
		log("    (define-fun |<mod>_u <id>| ((state |<mod>_s|)) Bool (...))\n");
		log("        Each $assume cell is converted into one of this functions. The function\n");
		log("        evaluates to 'true' if the assume statement holds in the state.\n");
		log("\n");
		log("    ; yosys-smt2-cover <id> <filename:linenum>\n");
		log("    (define-fun |<mod>_c <id>| ((state |<mod>_s|)) Bool (...))\n");
		log("        Each $cover cell is converted into one of this functions. The function\n");
		log("        evaluates to 'true' if the cover statement is activated in the state.\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("    -verbose\n");
		log("        this will print the recursive walk used to export the modules.\n");
		log("\n");
		log("    -stbv\n");
		log("        Use a BitVec sort to represent a state instead of an uninterpreted\n");
		log("        sort. As a side-effect this will prevent use of arrays to model\n");
		log("        memories.\n");
		log("\n");
		log("    -stdt\n");
		log("        Use SMT-LIB 2.6 style datatypes to represent a state instead of an\n");
		log("        uninterpreted sort.\n");
		log("\n");
		log("    -nobv\n");
		log("        disable support for BitVec (FixedSizeBitVectors theory). without this\n");
		log("        option multi-bit wires are represented using the BitVec sort and\n");
		log("        support for coarse grain cells (incl. arithmetic) is enabled.\n");
		log("\n");
		log("    -nomem\n");
		log("        disable support for memories (via ArraysEx theory). this option is\n");
		log("        implied by -nobv. only $mem cells without merged registers in\n");
		log("        read ports are supported. call \"memory\" with -nordff to make sure\n");
		log("        that no registers are merged into $mem read ports. '<mod>_m' functions\n");
		log("        will be generated for accessing the arrays that are used to represent\n");
		log("        memories.\n");
		log("\n");
		log("    -wires\n");
		log("        create '<mod>_n' functions for all public wires. by default only ports,\n");
		log("        registers, and wires with the 'keep' attribute are exported.\n");
		log("\n");
		log("    -tpl <template_file>\n");
		log("        use the given template file. the line containing only the token '%%%%'\n");
		log("        is replaced with the regular output of this command.\n");
		log("\n");
		log("[1] For more information on SMT-LIBv2 visit http://smt-lib.org/ or read David\n");
		log("R. Cok's tutorial: http://www.grammatech.com/resources/smt/SMTLIBTutorial.pdf\n");
		log("\n");
		log("---------------------------------------------------------------------------\n");
		log("\n");
		log("Example:\n");
		log("\n");
		log("Consider the following module (test.v). We want to prove that the output can\n");
		log("never transition from a non-zero value to a zero value.\n");
		log("\n");
		log("        module test(input clk, output reg [3:0] y);\n");
		log("          always @(posedge clk)\n");
		log("            y <= (y << 1) | ^y;\n");
		log("        endmodule\n");
		log("\n");
		log("For this proof we create the following template (test.tpl).\n");
		log("\n");
		log("        ; we need QF_UFBV for this poof\n");
		log("        (set-logic QF_UFBV)\n");
		log("\n");
		log("        ; insert the auto-generated code here\n");
		log("        %%%%\n");
		log("\n");
		log("        ; declare two state variables s1 and s2\n");
		log("        (declare-fun s1 () test_s)\n");
		log("        (declare-fun s2 () test_s)\n");
		log("\n");
		log("        ; state s2 is the successor of state s1\n");
		log("        (assert (test_t s1 s2))\n");
		log("\n");
		log("        ; we are looking for a model with y non-zero in s1\n");
		log("        (assert (distinct (|test_n y| s1) #b0000))\n");
		log("\n");
		log("        ; we are looking for a model with y zero in s2\n");
		log("        (assert (= (|test_n y| s2) #b0000))\n");
		log("\n");
		log("        ; is there such a model?\n");
		log("        (check-sat)\n");
		log("\n");
		log("The following yosys script will create a 'test.smt2' file for our proof:\n");
		log("\n");
		log("        read_verilog test.v\n");
		log("        hierarchy -check; proc; opt; check -assert\n");
		log("        write_smt2 -bv -tpl test.tpl test.smt2\n");
		log("\n");
		log("Running 'cvc4 test.smt2' will print 'unsat' because y can never transition\n");
		log("from non-zero to zero in the test design.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::ifstream template_f;
		bool bvmode = true, memmode = true, wiresmode = false, verbose = false, statebv = false, statedt = false;
		bool forallmode = false;

		log_header(design, "Executing SMT2 backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tpl" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-bv" || args[argidx] == "-mem") {
				log_warning("Options -bv and -mem are now the default. Support for -bv and -mem will be removed in the future.\n");
				continue;
			}
			if (args[argidx] == "-stbv") {
				statebv = true;
				statedt = false;
				continue;
			}
			if (args[argidx] == "-stdt") {
				statebv = false;
				statedt = true;
				continue;
			}
			if (args[argidx] == "-nobv") {
				bvmode = false;
				memmode = false;
				continue;
			}
			if (args[argidx] == "-nomem") {
				memmode = false;
				continue;
			}
			if (args[argidx] == "-wires") {
				wiresmode = true;
				continue;
			}
			if (args[argidx] == "-verbose") {
				verbose = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line)) {
				int indent = 0;
				while (indent < GetSize(line) && (line[indent] == ' ' || line[indent] == '\t'))
					indent++;
				if (line.compare(indent, 2, "%%") == 0)
					break;
				*f << line << std::endl;
			}
		}

		*f << stringf("; SMT-LIBv2 description generated by %s\n", yosys_version_str);

		if (!bvmode)
			*f << stringf("; yosys-smt2-nobv\n");

		if (!memmode)
			*f << stringf("; yosys-smt2-nomem\n");

		if (statebv)
			*f << stringf("; yosys-smt2-stbv\n");

		if (statedt)
			*f << stringf("; yosys-smt2-stdt\n");

		std::vector<RTLIL::Module*> sorted_modules;

		// extract module dependencies
		std::map<RTLIL::Module*, std::set<RTLIL::Module*>> module_deps;
		for (auto &mod_it : design->modules_) {
			module_deps[mod_it.second] = std::set<RTLIL::Module*>();
			for (auto &cell_it : mod_it.second->cells_)
				if (design->modules_.count(cell_it.second->type) > 0)
					module_deps[mod_it.second].insert(design->modules_.at(cell_it.second->type));
		}

		// simple good-enough topological sort
		// (O(n*m) on n elements and depth m)
		while (module_deps.size() > 0) {
			size_t sorted_modules_idx = sorted_modules.size();
			for (auto &it : module_deps) {
				for (auto &dep : it.second)
					if (module_deps.count(dep) > 0)
						goto not_ready_yet;
				// log("Next in topological sort: %s\n", RTLIL::id2cstr(it.first->name));
				sorted_modules.push_back(it.first);
			not_ready_yet:;
			}
			if (sorted_modules_idx == sorted_modules.size())
				log_error("Cyclic dependency between modules found! Cycle includes module %s.\n", RTLIL::id2cstr(module_deps.begin()->first->name));
			while (sorted_modules_idx < sorted_modules.size())
				module_deps.erase(sorted_modules.at(sorted_modules_idx++));
		}

		dict<IdString, int> mod_stbv_width;
		dict<IdString, dict<IdString, pair<bool, bool>>> mod_clk_cache;
		Module *topmod = design->top_module();
		std::string topmod_id;

		for (auto module : sorted_modules)
			for (auto cell : module->cells())
				if (cell->type.in("$allconst", "$allseq"))
					goto found_forall;
		if (0) {
	found_forall:
			forallmode = true;
			*f << stringf("; yosys-smt2-forall\n");
			if (!statebv && !statedt)
				log_error("Forall-exists problems are only supported in -stbv or -stdt mode.\n");
		}

		for (auto module : sorted_modules)
		{
			if (module->get_blackbox_attribute() || module->has_memories_warn() || module->has_processes_warn())
				continue;

			log("Creating SMT-LIBv2 representation of module %s.\n", log_id(module));

			Smt2Worker worker(module, bvmode, memmode, wiresmode, verbose, statebv, statedt, forallmode, mod_stbv_width, mod_clk_cache);
			worker.run();
			worker.write(*f);

			if (module == topmod)
				topmod_id = worker.get_id(module);
		}

		if (topmod)
			*f << stringf("; yosys-smt2-topmod %s\n", topmod_id.c_str());

		*f << stringf("; end of yosys output\n");

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line))
				*f << line << std::endl;
		}
	}
} Smt2Backend;

PRIVATE_NAMESPACE_END
