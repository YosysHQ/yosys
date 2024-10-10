/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/mem.h"
#include "libs/json11/json11.hpp"
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
	std::vector<Mem> memories;
	dict<Cell*, Mem*> mem_cells;
	std::set<Mem*> memory_queue;

	pool<SigBit> clock_posedge, clock_negedge;
	vector<string> ex_state_eq, ex_input_eq;

	std::map<RTLIL::SigBit, std::pair<int, int>> fcache;
	std::map<Mem*, int> memarrays;
	std::map<int, int> bvsizes;
	dict<IdString, char*> ids;

	bool is_smtlib2_module;

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
		   dict<IdString, int> &mod_stbv_width, dict<IdString, dict<IdString, pair<bool, bool>>> &mod_clk_cache)
	    : ct(module->design), sigmap(module), module(module), bvmode(bvmode), memmode(memmode), wiresmode(wiresmode), verbose(verbose),
	      statebv(statebv), statedt(statedt), forallmode(forallmode), mod_stbv_width(mod_stbv_width),
	      is_smtlib2_module(module->has_attribute(ID::smtlib2_module))
	{
		pool<SigBit> noclock;

		makebits(stringf("%s_is", get_id(module)));

		dict<IdString, Mem*> mem_dict;
		memories = Mem::get_all_memories(module);
		for (auto &mem : memories)
		{
			if (is_smtlib2_module)
				log_error("Memory %s.%s not allowed in module with smtlib2_module attribute", get_id(module), mem.memid.c_str());

			mem.narrow();
			mem_dict[mem.memid] = &mem;
			for (auto &port : mem.wr_ports)
			{
				if (port.clk_enable) {
					SigSpec clk = sigmap(port.clk);
					for (int i = 0; i < GetSize(clk); i++)
					{
						if (clk[i].wire == nullptr)
							continue;
						if (port.clk_polarity)
							clock_posedge.insert(clk[i]);
						else
							clock_negedge.insert(clk[i]);
					}
				}
				for (auto bit : sigmap(port.en))
					noclock.insert(bit);
				for (auto bit : sigmap(port.addr))
					noclock.insert(bit);
				for (auto bit : sigmap(port.data))
					noclock.insert(bit);
			}
			for (auto &port : mem.rd_ports)
			{
				if (port.clk_enable) {
					SigSpec clk = sigmap(port.clk);
					for (int i = 0; i < GetSize(clk); i++)
					{
						if (clk[i].wire == nullptr)
							continue;
						if (port.clk_polarity)
							clock_posedge.insert(clk[i]);
						else
							clock_negedge.insert(clk[i]);
					}
				}
				for (auto bit : sigmap(port.en))
					noclock.insert(bit);
				for (auto bit : sigmap(port.addr))
					noclock.insert(bit);
				for (auto bit : sigmap(port.data))
					noclock.insert(bit);
				Cell *driver = port.cell ? port.cell : mem.cell;
				for (auto bit : sigmap(port.data)) {
					if (bit_driver.count(bit))
						log_error("Found multiple drivers for %s.\n", log_signal(bit));
					bit_driver[bit] = driver;
				}
			}
		}

		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
		{
			if (GetSize(conn.second) == 0)
				continue;

			// Handled above.
			if (cell->is_mem_cell()) {
				mem_cells[cell] = mem_dict[cell->parameters.at(ID::MEMID).decode_string()];
				continue;
			}

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

			if (cell->type.in(ID($dff), ID($_DFF_P_), ID($_DFF_N_)) && conn.first.in(ID::CLK, ID::C))
			{
				bool posedge = (cell->type == ID($_DFF_N_)) || (cell->type == ID($dff) && cell->getParam(ID::CLK_POLARITY).as_bool());
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
			auto gclk_attr = wire->attributes.find(ID::replaced_by_gclk);
			if (gclk_attr != wire->attributes.end()) {
				if (gclk_attr->second == State::S1)
					clock_posedge.insert(sigmap(wire));
				else if (gclk_attr->second == State::S0)
					clock_negedge.insert(sigmap(wire));
			}
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
		RTLIL::SigBit bit = sigmap(cell->getPort(ID::Y).as_bit());
		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bool(cell->getPort(ID::A));
			else if (ch == 'B') processed_expr += get_bool(cell->getPort(ID::B));
			else if (ch == 'C') processed_expr += get_bool(cell->getPort(ID::C));
			else if (ch == 'D') processed_expr += get_bool(cell->getPort(ID::D));
			else if (ch == 'S') processed_expr += get_bool(cell->getPort(ID::S));
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
		RTLIL::SigSpec sig_y = sigmap(cell->getPort(ID::Y));
		bool is_signed = type == 'U' ? false : cell->getParam(ID::A_SIGNED).as_bool();
		int width = GetSize(sig_y);

		if (type == 's' || type == 'S' || type == 'd' || type == 'b') {
			if (type == 'b')
				width = GetSize(cell->getPort(ID::A));
			else
				width = max(width, GetSize(cell->getPort(ID::A)));
			if (cell->hasPort(ID::B))
				width = max(width, GetSize(cell->getPort(ID::B)));
		}

		if (cell->hasPort(ID::A)) {
			sig_a = cell->getPort(ID::A);
			sig_a.extend_u0(width, is_signed);
		}

		if (cell->hasPort(ID::B)) {
			sig_b = cell->getPort(ID::B);
			sig_b.extend_u0(width, (type == 'S') || (is_signed && !(type == 's')));
		}

		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bv(sig_a);
			else if (ch == 'B') processed_expr += get_bv(sig_b);
			else if (ch == 'P') processed_expr += get_bv(cell->getPort(ID::B));
			else if (ch == 'S') processed_expr += get_bv(cell->getPort(ID::S));
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
		RTLIL::SigSpec sig_y = sigmap(cell->getPort(ID::Y));
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

		if (cell->type == ID($initstate))
		{
			SigBit bit = sigmap(cell->getPort(ID::Y).as_bit());
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool (|%s_is| state)) ; %s\n",
					get_id(module), idcounter, get_id(module), get_id(module), log_signal(bit)));
			register_bool(bit, idcounter++);
			recursive_cells.erase(cell);
			return;
		}

		if (cell->type.in(ID($_FF_), ID($_DFF_P_), ID($_DFF_N_)))
		{
			registers.insert(cell);
			SigBit q_bit = cell->getPort(ID::Q);
			if (q_bit.is_wire())
				decls.push_back(witness_signal("reg", 1, 0, "", idcounter, q_bit.wire));
			makebits(stringf("%s#%d", get_id(module), idcounter), 0, log_signal(cell->getPort(ID::Q)));
			register_bool(cell->getPort(ID::Q), idcounter++);
			recursive_cells.erase(cell);
			return;
		}

		if (cell->type == ID($_BUF_)) return export_gate(cell, "A");
		if (cell->type == ID($_NOT_)) return export_gate(cell, "(not A)");
		if (cell->type == ID($_AND_)) return export_gate(cell, "(and A B)");
		if (cell->type == ID($_NAND_)) return export_gate(cell, "(not (and A B))");
		if (cell->type == ID($_OR_)) return export_gate(cell, "(or A B)");
		if (cell->type == ID($_NOR_)) return export_gate(cell, "(not (or A B))");
		if (cell->type == ID($_XOR_)) return export_gate(cell, "(xor A B)");
		if (cell->type == ID($_XNOR_)) return export_gate(cell, "(not (xor A B))");
		if (cell->type == ID($_ANDNOT_)) return export_gate(cell, "(and A (not B))");
		if (cell->type == ID($_ORNOT_)) return export_gate(cell, "(or A (not B))");
		if (cell->type == ID($_MUX_)) return export_gate(cell, "(ite S B A)");
		if (cell->type == ID($_NMUX_)) return export_gate(cell, "(not (ite S B A))");
		if (cell->type == ID($_AOI3_)) return export_gate(cell, "(not (or (and A B) C))");
		if (cell->type == ID($_OAI3_)) return export_gate(cell, "(not (and (or A B) C))");
		if (cell->type == ID($_AOI4_)) return export_gate(cell, "(not (or (and A B) (and C D)))");
		if (cell->type == ID($_OAI4_)) return export_gate(cell, "(not (and (or A B) (or C D)))");

		// FIXME: $lut

		if (bvmode)
		{
			if (cell->type.in(ID($ff), ID($dff)))
			{
				registers.insert(cell);
				int smtoffset = 0;
				for (auto chunk : cell->getPort(ID::Q).chunks()) {
					if (chunk.is_wire())
						decls.push_back(witness_signal("reg", chunk.width, chunk.offset, "", idcounter, chunk.wire, smtoffset));
					smtoffset += chunk.width;
				}
				makebits(stringf("%s#%d", get_id(module), idcounter), GetSize(cell->getPort(ID::Q)), log_signal(cell->getPort(ID::Q)));
				register_bv(cell->getPort(ID::Q), idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			if (cell->type.in(ID($anyconst), ID($anyseq), ID($anyinit), ID($allconst), ID($allseq)))
			{
				auto QY = cell->type == ID($anyinit) ? ID::Q : ID::Y;
				registers.insert(cell);
				string infostr = cell->attributes.count(ID::src) ? cell->attributes.at(ID::src).decode_string().c_str() : get_id(cell);
				if (cell->attributes.count(ID::reg))
					infostr += " " + cell->attributes.at(ID::reg).decode_string();
				decls.push_back(stringf("; yosys-smt2-%s %s#%d %d %s\n", cell->type.c_str() + 1, get_id(module), idcounter, GetSize(cell->getPort(QY)), infostr.c_str()));
				if (cell->getPort(QY).is_wire() && cell->getPort(QY).as_wire()->get_bool_attribute(ID::maximize)){
					decls.push_back(stringf("; yosys-smt2-maximize %s#%d\n", get_id(module), idcounter));
					log("Wire %s is maximized\n", cell->getPort(QY).as_wire()->name.str().c_str());
				}
				else if (cell->getPort(QY).is_wire() && cell->getPort(QY).as_wire()->get_bool_attribute(ID::minimize)){
					decls.push_back(stringf("; yosys-smt2-minimize %s#%d\n", get_id(module), idcounter));
					log("Wire %s is minimized\n", cell->getPort(QY).as_wire()->name.str().c_str());
				}

				bool init_only = cell->type.in(ID($anyconst), ID($anyinit), ID($allconst));
				bool clk2fflogic = cell->type == ID($anyinit) && cell->get_bool_attribute(ID(clk2fflogic));
				int smtoffset = 0;
				for (auto chunk : cell->getPort(clk2fflogic ? ID::D : QY).chunks()) {
					if (chunk.is_wire())
						decls.push_back(witness_signal(init_only ? "init" : "seq", chunk.width, chunk.offset, "", idcounter, chunk.wire, smtoffset));
					smtoffset += chunk.width;
				}

				makebits(stringf("%s#%d", get_id(module), idcounter), GetSize(cell->getPort(QY)), log_signal(cell->getPort(QY)));
				if (cell->type == ID($anyseq))
					ex_input_eq.push_back(stringf("  (= (|%s#%d| state) (|%s#%d| other_state))", get_id(module), idcounter, get_id(module), idcounter));
				register_bv(cell->getPort(QY), idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			if (cell->type == ID($and)) return export_bvop(cell, "(bvand A B)");
			if (cell->type == ID($or)) return export_bvop(cell, "(bvor A B)");
			if (cell->type == ID($xor)) return export_bvop(cell, "(bvxor A B)");
			if (cell->type == ID($xnor)) return export_bvop(cell, "(bvxnor A B)");

			if (cell->type == ID($bweqx)) return export_bvop(cell, "(bvxnor A B)", 'U');
			if (cell->type == ID($bwmux)) return export_bvop(cell, "(bvor (bvand A (bvnot S)) (bvand B S))", 'U');

			if (cell->type == ID($shl)) return export_bvop(cell, "(bvshl A B)", 's');
			if (cell->type == ID($shr)) return export_bvop(cell, "(bvlshr A B)", 's');
			if (cell->type == ID($sshl)) return export_bvop(cell, "(bvshl A B)", 's');
			if (cell->type == ID($sshr)) return export_bvop(cell, "(bvLshr A B)", 's');

			if (cell->type.in(ID($shift), ID($shiftx))) {
				if (cell->getParam(ID::B_SIGNED).as_bool()) {
					return export_bvop(cell, stringf("(ite (bvsge P #b%0*d) "
							"(bvlshr A B) (bvshl A (bvneg B)))",
							GetSize(cell->getPort(ID::B)), 0), 'S'); // type 'S' sign extends B
				} else {
					return export_bvop(cell, "(bvlshr A B)", 's');
				}
			}

			if (cell->type == ID($lt)) return export_bvop(cell, "(bvUlt A B)", 'b');
			if (cell->type == ID($le)) return export_bvop(cell, "(bvUle A B)", 'b');
			if (cell->type == ID($ge)) return export_bvop(cell, "(bvUge A B)", 'b');
			if (cell->type == ID($gt)) return export_bvop(cell, "(bvUgt A B)", 'b');

			if (cell->type == ID($ne)) return export_bvop(cell, "(distinct A B)", 'b');
			if (cell->type == ID($nex)) return export_bvop(cell, "(distinct A B)", 'b');
			if (cell->type == ID($eq)) return export_bvop(cell, "(= A B)", 'b');
			if (cell->type == ID($eqx)) return export_bvop(cell, "(= A B)", 'b');

			if (cell->type == ID($not)) return export_bvop(cell, "(bvnot A)");
			if (cell->type == ID($pos)) return export_bvop(cell, "A");
			if (cell->type == ID($neg)) return export_bvop(cell, "(bvneg A)");

			if (cell->type == ID($add)) return export_bvop(cell, "(bvadd A B)");
			if (cell->type == ID($sub)) return export_bvop(cell, "(bvsub A B)");
			if (cell->type == ID($mul)) return export_bvop(cell, "(bvmul A B)");
			if (cell->type == ID($div)) return export_bvop(cell, "(bvUdiv A B)", 'd');
			// "rem" = truncating modulo
			if (cell->type == ID($mod)) return export_bvop(cell, "(bvUrem A B)", 'd');
			// "mod" = flooring modulo
			if (cell->type == ID($modfloor)) {
				// bvumod doesn't exist because it's the same as bvurem
				if (cell->getParam(ID::A_SIGNED).as_bool()) {
					return export_bvop(cell, "(bvsmod A B)", 'd');
				} else {
					return export_bvop(cell, "(bvurem A B)", 'd');
				}
			}
			// "div" = flooring division
			if (cell->type == ID($divfloor)) {
				if (cell->getParam(ID::A_SIGNED).as_bool()) {
					// bvsdiv is truncating division, so we can't use it here.
					int width = max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
					width = max(width, GetSize(cell->getPort(ID::Y)));
					auto expr = stringf("(let ("
							    "(a_neg (bvslt A #b%0*d)) "
							    "(b_neg (bvslt B #b%0*d))) "
							    "(let ((abs_a (ite a_neg (bvneg A) A)) "
							    "(abs_b (ite b_neg (bvneg B) B))) "
							    "(let ((u (bvudiv abs_a abs_b)) "
							    "(adj (ite (= #b%0*d (bvurem abs_a abs_b)) #b%0*d #b%0*d))) "
							    "(ite (= a_neg b_neg) u "
							    "(bvneg (bvadd u adj))))))",
							    width, 0, width, 0, width, 0, width, 0, width, 1);
					return export_bvop(cell, expr, 'd');
				} else {
					return export_bvop(cell, "(bvudiv A B)", 'd');
				}
			}

			if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool)) &&
					2*GetSize(cell->getPort(ID::A).chunks()) < GetSize(cell->getPort(ID::A))) {
				bool is_and = cell->type == ID($reduce_and);
				string bits(GetSize(cell->getPort(ID::A)), is_and ? '1' : '0');
				return export_bvop(cell, stringf("(%s A #b%s)", is_and ? "=" : "distinct", bits.c_str()), 'b');
			}

			if (cell->type == ID($reduce_and)) return export_reduce(cell, "(and A)", true);
			if (cell->type == ID($reduce_or)) return export_reduce(cell, "(or A)", false);
			if (cell->type == ID($reduce_xor)) return export_reduce(cell, "(xor A)", false);
			if (cell->type == ID($reduce_xnor)) return export_reduce(cell, "(not (xor A))", false);
			if (cell->type == ID($reduce_bool)) return export_reduce(cell, "(or A)", false);

			if (cell->type == ID($logic_not)) return export_reduce(cell, "(not (or A))", false);
			if (cell->type == ID($logic_and)) return export_reduce(cell, "(and (or A) (or B))", false);
			if (cell->type == ID($logic_or)) return export_reduce(cell, "(or A B)", false);

			if (cell->type.in(ID($mux), ID($pmux)))
			{
				int width = GetSize(cell->getPort(ID::Y));
				std::string processed_expr = get_bv(cell->getPort(ID::A));

				RTLIL::SigSpec sig_b = cell->getPort(ID::B);
				RTLIL::SigSpec sig_s = cell->getPort(ID::S);
				get_bv(sig_b);
				get_bv(sig_s);

				for (int i = 0; i < GetSize(sig_s); i++)
					processed_expr = stringf("(ite %s %s %s)", get_bool(sig_s[i]).c_str(),
							get_bv(sig_b.extract(i*width, width)).c_str(), processed_expr.c_str());

				if (verbose)
					log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "", log_id(cell));

				RTLIL::SigSpec sig = sigmap(cell->getPort(ID::Y));
				decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
						get_id(module), idcounter, get_id(module), width, processed_expr.c_str(), log_signal(sig)));
				register_bv(sig, idcounter++);
				recursive_cells.erase(cell);
				return;
			}

			// FIXME: $slice $concat
		}

		if (memmode && cell->is_mem_cell())
		{
			Mem *mem = mem_cells[cell];

			if (memarrays.count(mem)) {
				recursive_cells.erase(cell);
				return;
			}

			int arrayid = idcounter++;
			memarrays[mem] = arrayid;

			int abits = max(1, ceil_log2(mem->size));

			bool has_sync_wr = false;
			bool has_async_wr = false;
			for (auto &port : mem->wr_ports) {
				if (port.clk_enable)
					has_sync_wr = true;
				else
					has_async_wr = true;
			}
			if (has_async_wr && has_sync_wr)
				log_error("Memory %s.%s has mixed clocked/nonclocked write ports. This is not supported by \"write_smt2\".\n", log_id(cell), log_id(module));

			decls.push_back(stringf("; yosys-smt2-memory %s %d %d %d %d %s\n", get_id(mem->memid), abits, mem->width, GetSize(mem->rd_ports), GetSize(mem->wr_ports), has_async_wr ? "async" : "sync"));
			decls.push_back(witness_memory(get_id(mem->memid), cell, mem));

			string memstate;
			if (has_async_wr) {
				memstate = stringf("%s#%d#final", get_id(module), arrayid);
			} else {
				memstate = stringf("%s#%d#0", get_id(module), arrayid);
			}

			if (statebv)
			{
				makebits(memstate, mem->width*mem->size, get_id(mem->memid));
				decls.push_back(stringf("(define-fun |%s_m %s| ((state |%s_s|)) (_ BitVec %d) (|%s| state))\n",
						get_id(module), get_id(mem->memid), get_id(module), mem->width*mem->size, memstate.c_str()));

				for (int i = 0; i < GetSize(mem->rd_ports); i++)
				{
					auto &port = mem->rd_ports[i];
					SigSpec addr_sig = port.addr;
					addr_sig.extend_u0(abits);
					std::string addr = get_bv(addr_sig);

					if (port.clk_enable)
						log_error("Read port %d (%s) of memory %s.%s is clocked. This is not supported by \"write_smt2\"! "
								"Call \"memory\" with -nordff to avoid this error.\n", i, log_signal(port.data), log_id(mem->memid), log_id(module));

					decls.push_back(stringf("(define-fun |%s_m:R%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
							get_id(module), i, get_id(mem->memid), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));

					std::string read_expr = "#b";
					for (int k = 0; k < mem->width; k++)
						read_expr += "0";

					for (int k = 0; k < mem->size; k++)
						read_expr = stringf("(ite (= (|%s_m:R%dA %s| state) #b%s) ((_ extract %d %d) (|%s| state))\n  %s)",
								get_id(module), i, get_id(mem->memid), Const(k+mem->start_offset, abits).as_string().c_str(),
								mem->width*(k+1)-1, mem->width*k, memstate.c_str(), read_expr.c_str());

					decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d)\n  %s) ; %s\n",
							get_id(module), idcounter, get_id(module), mem->width, read_expr.c_str(), log_signal(port.data)));

					decls.push_back(stringf("(define-fun |%s_m:R%dD %s| ((state |%s_s|)) (_ BitVec %d) (|%s#%d| state))\n",
							get_id(module), i, get_id(mem->memid), get_id(module), mem->width, get_id(module), idcounter));

					register_bv(port.data, idcounter++);
				}
			}
			else
			{
				if (statedt)
					dtmembers.push_back(stringf("  (|%s| (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
							memstate.c_str(), abits, mem->width, get_id(mem->memid)));
				else
					decls.push_back(stringf("(declare-fun |%s| (|%s_s|) (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
							memstate.c_str(), get_id(module), abits, mem->width, get_id(mem->memid)));

				decls.push_back(stringf("(define-fun |%s_m %s| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) (|%s| state))\n",
						get_id(module), get_id(mem->memid), get_id(module), abits, mem->width, memstate.c_str()));

				for (int i = 0; i < GetSize(mem->rd_ports); i++)
				{
					auto &port = mem->rd_ports[i];
					SigSpec addr_sig = port.addr;
					addr_sig.extend_u0(abits);
					std::string addr = get_bv(addr_sig);

					if (port.clk_enable)
						log_error("Read port %d (%s) of memory %s.%s is clocked. This is not supported by \"write_smt2\"! "
								"Call \"memory\" with -nordff to avoid this error.\n", i, log_signal(port.data), log_id(mem->memid), log_id(module));

					decls.push_back(stringf("(define-fun |%s_m:R%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
							get_id(module), i, get_id(mem->memid), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));

					decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) (select (|%s| state) (|%s_m:R%dA %s| state))) ; %s\n",
							get_id(module), idcounter, get_id(module), mem->width, memstate.c_str(), get_id(module), i, get_id(mem->memid), log_signal(port.data)));

					decls.push_back(stringf("(define-fun |%s_m:R%dD %s| ((state |%s_s|)) (_ BitVec %d) (|%s#%d| state))\n",
							get_id(module), i, get_id(mem->memid), get_id(module), mem->width, get_id(module), idcounter));

					register_bv(port.data, idcounter++);
				}
			}

			memory_queue.insert(mem);
			recursive_cells.erase(cell);
			return;
		}

		Module *m = module->design->module(cell->type);

		if (m != nullptr)
		{
			decls.push_back(stringf("; yosys-smt2-cell %s %s\n", get_id(cell->type), get_id(cell->name)));
			decls.push_back(witness_cell(get_id(cell->name), cell));
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

		if (cell->type.in(ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)) || cell->type.str().substr(0, 6) == "$_SDFF" || (cell->type.str().substr(0, 6) == "$_DFFE" && cell->type.str().size() == 10)) {
			log_error("Unsupported cell type %s for cell %s.%s -- please run `dffunmap` before `write_smt2`.\n",
					log_id(cell->type), log_id(module), log_id(cell));
		}
		if (cell->type.in(ID($adff), ID($adffe), ID($aldff), ID($aldffe), ID($dffsr), ID($dffsre)) || cell->type.str().substr(0, 5) == "$_DFF" || cell->type.str().substr(0, 7) == "$_ALDFF") {
			log_error("Unsupported cell type %s for cell %s.%s -- please run `async2sync; dffunmap` or `clk2fflogic` before `write_smt2`.\n",
					log_id(cell->type), log_id(module), log_id(cell));
		}
		if (cell->type.in(ID($sr), ID($dlatch), ID($adlatch), ID($dlatchsr)) || cell->type.str().substr(0, 8) == "$_DLATCH" || cell->type.str().substr(0, 5) == "$_SR_") {
			log_error("Unsupported cell type %s for cell %s.%s -- please run `clk2fflogic` before `write_smt2`.\n",
					log_id(cell->type), log_id(module), log_id(cell));
		}
		log_error("Unsupported cell type %s for cell %s.%s.\n",
				log_id(cell->type), log_id(module), log_id(cell));
	}

	void verify_smtlib2_module()
	{
		if (!module->get_blackbox_attribute())
			log_error("Module %s with smtlib2_module attribute must also have blackbox attribute.\n", log_id(module));
		if (module->cells().size() > 0)
			log_error("Module %s with smtlib2_module attribute must not have any cells inside it.\n", log_id(module));
		for (auto wire : module->wires())
			if (!wire->port_id)
				log_error("Wire %s.%s must be input or output since module has smtlib2_module attribute.\n", log_id(module),
					  log_id(wire));
	}

	void run()
	{
		if (verbose) log("=> export logic driving outputs\n");

		if (is_smtlib2_module)
			verify_smtlib2_module();

		pool<SigBit> reg_bits;
		for (auto cell : module->cells())
			if (cell->type.in(ID($ff), ID($dff), ID($_FF_), ID($_DFF_P_), ID($_DFF_N_), ID($anyinit))) {
				// not using sigmap -- we want the net directly at the dff output
				for (auto bit : cell->getPort(ID::Q))
					reg_bits.insert(bit);
			}

		std::string smtlib2_inputs;
		std::vector<std::string> smtlib2_decls;
		if (is_smtlib2_module) {
			for (auto wire : module->wires()) {
				if (!wire->port_input)
					continue;
				smtlib2_inputs += stringf("(|%s| (|%s_n %s| state))\n", get_id(wire), get_id(module), get_id(wire));
			}
		}

		for (auto wire : module->wires()) {
			bool is_register = false;
			bool contains_clock = false;
			for (auto bit : SigSpec(wire)) {
				if (reg_bits.count(bit))
					is_register = true;
				auto sig_bit = sigmap(bit);
				if (clock_posedge.count(sig_bit) || clock_negedge.count(sig_bit))
					contains_clock = true;
			}
			bool is_smtlib2_comb_expr = wire->has_attribute(ID::smtlib2_comb_expr);
			if (is_smtlib2_comb_expr && !is_smtlib2_module)
				log_error("smtlib2_comb_expr is only valid in a module with the smtlib2_module attribute: wire %s.%s", log_id(module),
					  log_id(wire));
			if (wire->port_id || is_register || contains_clock || wire->get_bool_attribute(ID::keep) || (wiresmode && wire->name.isPublic())) {
				RTLIL::SigSpec sig = sigmap(wire);
				std::vector<std::string> comments;
				if (wire->port_input)
					comments.push_back(stringf("; yosys-smt2-input %s %d\n", get_id(wire), wire->width));
				if (wire->port_output)
					comments.push_back(stringf("; yosys-smt2-output %s %d\n", get_id(wire), wire->width));
				if (is_register)
					comments.push_back(stringf("; yosys-smt2-register %s %d\n", get_id(wire), wire->width));
				if (wire->get_bool_attribute(ID::keep) || (wiresmode && wire->name.isPublic()))
					comments.push_back(stringf("; yosys-smt2-wire %s %d\n", get_id(wire), wire->width));
				if (contains_clock && GetSize(wire) == 1 && (clock_posedge.count(sig) || clock_negedge.count(sig)))
					comments.push_back(stringf("; yosys-smt2-clock %s%s%s\n", get_id(wire),
							clock_posedge.count(sig) ? " posedge" : "", clock_negedge.count(sig) ? " negedge" : ""));
				if (wire->port_input && contains_clock) {
					for (int i = 0; i < GetSize(sig); i++) {
						bool is_posedge = clock_posedge.count(sig[i]);
						bool is_negedge = clock_negedge.count(sig[i]);
						if (is_posedge != is_negedge)
							comments.push_back(witness_signal(
									is_posedge ? "posedge" : "negedge", 1, i, get_id(wire), -1, wire));
					}
				}
				if (wire->port_input)
					comments.push_back(witness_signal("input", wire->width, 0, get_id(wire), -1, wire));
				std::string smtlib2_comb_expr;
				if (is_smtlib2_comb_expr) {
					smtlib2_comb_expr =
					  "(let (\n" + smtlib2_inputs + ")\n" + wire->get_string_attribute(ID::smtlib2_comb_expr) + "\n)";
					if (wire->port_input || !wire->port_output)
						log_error("smtlib2_comb_expr is only valid on output: wire %s.%s", log_id(module), log_id(wire));
					if (!bvmode && GetSize(sig) > 1)
						log_error("smtlib2_comb_expr is unsupported on multi-bit wires when -nobv is specified: wire %s.%s",
							  log_id(module), log_id(wire));

					comments.push_back(witness_signal("blackbox", wire->width, 0, get_id(wire), -1, wire));
				}
				auto &out_decls = is_smtlib2_comb_expr ? smtlib2_decls : decls;
				if (bvmode && GetSize(sig) > 1) {
					std::string sig_bv = is_smtlib2_comb_expr ? smtlib2_comb_expr : get_bv(sig);
					if (!comments.empty())
						out_decls.insert(out_decls.end(), comments.begin(), comments.end());
					out_decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) (_ BitVec %d) %s)\n",
							get_id(module), get_id(wire), get_id(module), GetSize(sig), sig_bv.c_str()));
					if (wire->port_input)
						ex_input_eq.push_back(stringf("  (= (|%s_n %s| state) (|%s_n %s| other_state))",
								get_id(module), get_id(wire), get_id(module), get_id(wire)));
				} else {
					std::vector<std::string> sig_bool;
					for (int i = 0; i < GetSize(sig); i++) {
						sig_bool.push_back(is_smtlib2_comb_expr ? smtlib2_comb_expr : get_bool(sig[i]));
					}
					if (!comments.empty())
						out_decls.insert(out_decls.end(), comments.begin(), comments.end());
					for (int i = 0; i < GetSize(sig); i++) {
						if (GetSize(sig) > 1) {
							out_decls.push_back(stringf("(define-fun |%s_n %s %d| ((state |%s_s|)) Bool %s)\n",
									get_id(module), get_id(wire), i, get_id(module), sig_bool[i].c_str()));
							if (wire->port_input)
								ex_input_eq.push_back(stringf("  (= (|%s_n %s %d| state) (|%s_n %s %d| other_state))",
										get_id(module), get_id(wire), i, get_id(module), get_id(wire), i));
						} else {
							out_decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) Bool %s)\n",
									get_id(module), get_id(wire), get_id(module), sig_bool[i].c_str()));
							if (wire->port_input)
								ex_input_eq.push_back(stringf("  (= (|%s_n %s| state) (|%s_n %s| other_state))",
										get_id(module), get_id(wire), get_id(module), get_id(wire)));
						}
					}
				}
			}
		}

		decls.insert(decls.end(), smtlib2_decls.begin(), smtlib2_decls.end());

		if (verbose) log("=> export logic associated with the initial state\n");

		vector<string> init_list;
		for (auto wire : module->wires())
			if (wire->attributes.count(ID::init)) {
				if (is_smtlib2_module)
					log_error("init attribute not allowed on wires in module with smtlib2_module attribute: wire %s.%s",
						  log_id(module), log_id(wire));

				RTLIL::SigSpec sig = sigmap(wire);
				Const val = wire->attributes.at(ID::init);
				val.bits().resize(GetSize(sig), State::Sx);
				if (bvmode && GetSize(sig) > 1) {
					Const mask(State::S1, GetSize(sig));
					bool use_mask = false;
					for (int i = 0; i < GetSize(sig); i++)
						if (val[i] != State::S0 && val[i] != State::S1) {
							val.bits()[i] = State::S0;
							mask.bits()[i] = State::S0;
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
			if (cell->type.in(ID($assert), ID($assume), ID($cover)))
			{
				int &id = cell->type == ID($assert) ? assert_id :
						cell->type == ID($assume) ? assume_id :
						cell->type == ID($cover) ? cover_id : *(int*)nullptr;

				char postfix = cell->type == ID($assert) ? 'a' :
						cell->type == ID($assume) ? 'u' :
						cell->type == ID($cover) ? 'c' : 0;

				string name_a = get_bool(cell->getPort(ID::A));
				string name_en = get_bool(cell->getPort(ID::EN));
				bool private_name = cell->name[0] == '$';

				if (!private_name && cell->has_attribute(ID::hdlname)) {
					for (auto const &part : cell->get_hdlname_attribute()) {
						if (part == "_witness_") {
							private_name = true;
							break;
						}
					}
				}

				if (private_name && cell->attributes.count(ID::src))
					decls.push_back(stringf("; yosys-smt2-%s %d %s %s\n", cell->type.c_str() + 1, id, get_id(cell), cell->attributes.at(ID::src).decode_string().c_str()));
				else
					decls.push_back(stringf("; yosys-smt2-%s %d %s\n", cell->type.c_str() + 1, id, get_id(cell)));

				if (cell->type == ID($cover))
					decls.push_back(stringf("(define-fun |%s_%c %d| ((state |%s_s|)) Bool (and %s %s)) ; %s\n",
							get_id(module), postfix, id, get_id(module), name_a.c_str(), name_en.c_str(), get_id(cell)));
				else
					decls.push_back(stringf("(define-fun |%s_%c %d| ((state |%s_s|)) Bool (or %s (not %s))) ; %s\n",
							get_id(module), postfix, id, get_id(module), name_a.c_str(), name_en.c_str(), get_id(cell)));

				if (cell->type == ID($assert))
					assert_list.push_back(stringf("(|%s_a %d| state)", get_id(module), id));
				else if (cell->type == ID($assume))
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

		for (int iter = 1; !registers.empty() || !memory_queue.empty(); iter++)
		{
			pool<Cell*> this_regs;
			this_regs.swap(registers);

			if (verbose) log("=> export logic driving registers [iteration %d]\n", iter);

			for (auto cell : this_regs)
			{
				if (cell->type.in(ID($_FF_), ID($_DFF_P_), ID($_DFF_N_)))
				{
					std::string expr_d = get_bool(cell->getPort(ID::D));
					std::string expr_q = get_bool(cell->getPort(ID::Q), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort(ID::Q))));
					ex_state_eq.push_back(stringf("(= %s %s)", get_bool(cell->getPort(ID::Q)).c_str(), get_bool(cell->getPort(ID::Q), "other_state").c_str()));
				}

				if (cell->type.in(ID($ff), ID($dff), ID($anyinit)))
				{
					std::string expr_d = get_bv(cell->getPort(ID::D));
					std::string expr_q = get_bv(cell->getPort(ID::Q), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort(ID::Q))));
					ex_state_eq.push_back(stringf("(= %s %s)", get_bv(cell->getPort(ID::Q)).c_str(), get_bv(cell->getPort(ID::Q), "other_state").c_str()));
				}

				if (cell->type.in(ID($anyconst), ID($allconst)))
				{
					std::string expr_d = get_bv(cell->getPort(ID::Y));
					std::string expr_q = get_bv(cell->getPort(ID::Y), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), get_id(cell), log_signal(cell->getPort(ID::Y))));
					if (cell->type == ID($anyconst))
						ex_state_eq.push_back(stringf("(= %s %s)", get_bv(cell->getPort(ID::Y)).c_str(), get_bv(cell->getPort(ID::Y), "other_state").c_str()));
				}
			}

			std::set<Mem*> this_mems;
			this_mems.swap(memory_queue);

			for (auto mem : this_mems)
			{
				int arrayid = memarrays.at(mem);

				int abits = max(1, ceil_log2(mem->size));

				bool has_sync_wr = false;
				bool has_async_wr = false;
				for (auto &port : mem->wr_ports) {
					if (port.clk_enable)
						has_sync_wr = true;
					else
						has_async_wr = true;
				}

				string initial_memstate, final_memstate;

				if (has_async_wr) {
					log_assert(!has_sync_wr);
					initial_memstate = stringf("%s#%d#0", get_id(module), arrayid);
					final_memstate = stringf("%s#%d#final", get_id(module), arrayid);
				}

				if (statebv)
				{
					if (has_async_wr) {
						makebits(final_memstate, mem->width*mem->size, get_id(mem->memid));
					}

					for (int i = 0; i < GetSize(mem->wr_ports); i++)
					{
						auto &port = mem->wr_ports[i];
						SigSpec addr_sig = port.addr;
						addr_sig.extend_u0(abits);

						std::string addr = get_bv(addr_sig);
						std::string data = get_bv(port.data);
						std::string mask = get_bv(port.en);

						decls.push_back(stringf("(define-fun |%s_m:W%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));
						addr = stringf("(|%s_m:W%dA %s| state)", get_id(module), i, get_id(mem->memid));

						decls.push_back(stringf("(define-fun |%s_m:W%dD %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), mem->width, data.c_str(), log_signal(port.data)));
						data = stringf("(|%s_m:W%dD %s| state)", get_id(module), i, get_id(mem->memid));

						decls.push_back(stringf("(define-fun |%s_m:W%dM %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), mem->width, mask.c_str(), log_signal(port.en)));
						mask = stringf("(|%s_m:W%dM %s| state)", get_id(module), i, get_id(mem->memid));

						std::string data_expr;

						for (int k = mem->size-1; k >= 0; k--) {
							std::string new_data = stringf("(bvor (bvand %s %s) (bvand ((_ extract %d %d) (|%s#%d#%d| state)) (bvnot %s)))",
									data.c_str(), mask.c_str(), mem->width*(k+1)-1, mem->width*k, get_id(module), arrayid, i, mask.c_str());
							data_expr += stringf("\n  (ite (= %s #b%s) %s ((_ extract %d %d) (|%s#%d#%d| state)))",
									addr.c_str(), Const(k+mem->start_offset, abits).as_string().c_str(), new_data.c_str(),
									mem->width*(k+1)-1, mem->width*k, get_id(module), arrayid, i);
						}

						decls.push_back(stringf("(define-fun |%s#%d#%d| ((state |%s_s|)) (_ BitVec %d) (concat%s)) ; %s\n",
								get_id(module), arrayid, i+1, get_id(module), mem->width*mem->size, data_expr.c_str(), get_id(mem->memid)));
					}
				}
				else
				{
					if (has_async_wr) {
						if (statedt)
							dtmembers.push_back(stringf("  (|%s| (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
									initial_memstate.c_str(), abits, mem->width, get_id(mem->memid)));
						else
							decls.push_back(stringf("(declare-fun |%s| (|%s_s|) (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
									initial_memstate.c_str(), get_id(module), abits, mem->width, get_id(mem->memid)));
					}

					for (int i = 0; i < GetSize(mem->wr_ports); i++)
					{
						auto &port = mem->wr_ports[i];
						SigSpec addr_sig = port.addr;
						addr_sig.extend_u0(abits);

						std::string addr = get_bv(addr_sig);
						std::string data = get_bv(port.data);
						std::string mask = get_bv(port.en);

						decls.push_back(stringf("(define-fun |%s_m:W%dA %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), abits, addr.c_str(), log_signal(addr_sig)));
						addr = stringf("(|%s_m:W%dA %s| state)", get_id(module), i, get_id(mem->memid));

						decls.push_back(stringf("(define-fun |%s_m:W%dD %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), mem->width, data.c_str(), log_signal(port.data)));
						data = stringf("(|%s_m:W%dD %s| state)", get_id(module), i, get_id(mem->memid));

						decls.push_back(stringf("(define-fun |%s_m:W%dM %s| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
								get_id(module), i, get_id(mem->memid), get_id(module), mem->width, mask.c_str(), log_signal(port.en)));
						mask = stringf("(|%s_m:W%dM %s| state)", get_id(module), i, get_id(mem->memid));

						data = stringf("(bvor (bvand %s %s) (bvand (select (|%s#%d#%d| state) %s) (bvnot %s)))",
								data.c_str(), mask.c_str(), get_id(module), arrayid, i, addr.c_str(), mask.c_str());

						string empty_mask(mem->width, '0');

						decls.push_back(stringf("(define-fun |%s#%d#%d| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) "
								"(ite (= %s #b%s) (|%s#%d#%d| state) (store (|%s#%d#%d| state) %s %s))) ; %s\n",
								get_id(module), arrayid, i+1, get_id(module), abits, mem->width,
								mask.c_str(), empty_mask.c_str(), get_id(module), arrayid, i, get_id(module), arrayid, i, addr.c_str(), data.c_str(), get_id(mem->memid)));
					}
				}

				std::string expr_d = stringf("(|%s#%d#%d| state)", get_id(module), arrayid, GetSize(mem->wr_ports));
				std::string expr_q = stringf("(|%s#%d#0| next_state)", get_id(module), arrayid);
				trans.push_back(stringf("  (= %s %s) ; %s\n", expr_d.c_str(), expr_q.c_str(), get_id(mem->memid)));
				ex_state_eq.push_back(stringf("(= (|%s#%d#0| state) (|%s#%d#0| other_state))", get_id(module), arrayid, get_id(module), arrayid));

				if (has_async_wr)
					hier.push_back(stringf("  (= %s (|%s| state)) ; %s\n", expr_d.c_str(), final_memstate.c_str(), get_id(mem->memid)));

				Const init_data = mem->get_init_data();

				for (int i = 0; i < mem->size; i++)
				{
					if (i*mem->width >= GetSize(init_data))
						break;

					Const initword = init_data.extract(i*mem->width, mem->width, State::Sx);
					Const initmask = initword;
					bool gen_init_constr = false;

					for (int k = 0; k < GetSize(initword); k++) {
						if (initword[k] == State::S0 || initword[k] == State::S1) {
							gen_init_constr = true;
							initmask.bits()[k] = State::S1;
						} else {
							initmask.bits()[k] = State::S0;
							initword.bits()[k] = State::S0;
						}
					}

					if (gen_init_constr)
					{
						if (statebv)
							/* FIXME */;
						else
							init_list.push_back(stringf("(= (bvand (select (|%s#%d#0| state) #b%s) #b%s) #b%s) ; %s[%d]",
									get_id(module), arrayid, Const(i, abits).as_string().c_str(),
									initmask.as_string().c_str(), initword.as_string().c_str(), get_id(mem->memid), i));
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

	template<class T> static std::vector<std::string> witness_path(T *obj) {
		std::vector<std::string> path;
		if (obj->name.isPublic()) {
			auto hdlname = obj->get_string_attribute(ID::hdlname);
			for (auto token : split_tokens(hdlname))
				path.push_back("\\" + token);
		}
		if (path.empty())
			path.push_back(obj->name.str());
		return path;
	}

	std::string witness_signal(const char *type, int width, int offset, const std::string &smtname, int smtid, RTLIL::Wire *wire, int smtoffset = 0)
	{
		std::vector<std::string> hiername;
		const char *wire_name = wire->name.c_str();
		if (wire_name[0] == '\\') {
			auto hdlname = wire->get_string_attribute(ID::hdlname);
			for (auto token : split_tokens(hdlname))
				hiername.push_back("\\" + token);
		}
		if (hiername.empty())
			hiername.push_back(wire->name.str());

		std::string line = "; yosys-smt2-witness ";
		(json11::Json { json11::Json::object {
			{ "type", type },
			{ "offset", offset },
			{ "width", width },
			{ "smtname", smtname.empty() ? json11::Json(smtid) : json11::Json(smtname) },
			{ "smtoffset", smtoffset },
			{ "path", witness_path(wire) },
		}}).dump(line);
		line += "\n";
		return line;
	}

	std::string witness_cell(const char *smtname, RTLIL::Cell *cell)
	{
		std::string line = "; yosys-smt2-witness ";
		(json11::Json {json11::Json::object {
			{ "type", "cell" },
			{ "smtname", smtname },
			{ "path", witness_path(cell) },
		}}).dump(line);
		line += "\n";
		return line;
	}

	std::string witness_memory(const char *smtname, RTLIL::Cell *cell, Mem *mem)
	{
		json11::Json::array uninitialized;
		auto init_data = mem->get_init_data();

		int cursor = 0;

		while (cursor < init_data.size()) {
			while (cursor < init_data.size() && init_data[cursor] != State::Sx)
				cursor++;
			int offset = cursor;
			while (cursor < init_data.size() && init_data[cursor] == State::Sx)
				cursor++;
			int width = cursor - offset;
			if (width)
				uninitialized.push_back(json11::Json::object {
					{"width", width},
					{"offset", offset},
				});
		}

		std::string line = "; yosys-smt2-witness ";
		(json11::Json { json11::Json::object {
			{ "type", "mem" },
			{ "width", mem->width },
			{ "size", mem->size },
			{ "rom", mem->wr_ports.empty() },
			{ "statebv", statebv },
			{ "smtname", smtname },
			{ "uninitialized", uninitialized },
			{ "path", witness_path(cell) },
		}}).dump(line);
		line += "\n";
		return line;
	}
};

struct Smt2Backend : public Backend {
	Smt2Backend() : Backend("smt2", "write design to SMT-LIBv2 file") { }
	void help() override
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
		log("    -solver-option <option> <value>\n");
		log("        emit a `; yosys-smt2-solver-option` directive for yosys-smtbmc to write\n");
		log("        the given option as a `(set-option ...)` command in the SMT-LIBv2.\n");
		log("\n");
		log("[1] For more information on SMT-LIBv2 visit http://smt-lib.org/ or read David\n");
		log("R. Cok's tutorial: https://smtlib.github.io/jSMTLIB/SMTLIBTutorial.pdf\n");
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
		log("        ; we need QF_UFBV for this proof\n");
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
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::ifstream template_f;
		bool bvmode = true, memmode = true, wiresmode = false, verbose = false, statebv = false, statedt = false;
		bool forallmode = false;
		dict<std::string, std::string> solver_options;

		log_header(design, "Executing SMT2 backend.\n");

		log_push();
		Pass::call(design, "bmuxmap");
		Pass::call(design, "demuxmap");
		log_pop();

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
			if (args[argidx] == "-solver-option" && argidx+2 < args.size()) {
				solver_options.emplace(args[argidx+1], args[argidx+2]);
				argidx += 2;
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

		for (auto &it : solver_options)
			*f << stringf("; yosys-smt2-solver-option %s %s\n", it.first.c_str(), it.second.c_str());

		std::vector<RTLIL::Module*> sorted_modules;

		// extract module dependencies
		std::map<RTLIL::Module*, std::set<RTLIL::Module*>> module_deps;
		for (auto mod : design->modules()) {
			module_deps[mod] = std::set<RTLIL::Module*>();
			for (auto cell : mod->cells())
				if (design->has(cell->type))
					module_deps[mod].insert(design->module(cell->type));
		}

		// simple good-enough topological sort
		// (O(n*m) on n elements and depth m)
		while (module_deps.size() > 0) {
			size_t sorted_modules_idx = sorted_modules.size();
			for (auto &it : module_deps) {
				for (auto &dep : it.second)
					if (module_deps.count(dep) > 0)
						goto not_ready_yet;
				// log("Next in topological sort: %s\n", log_id(it.first->name));
				sorted_modules.push_back(it.first);
			not_ready_yet:;
			}
			if (sorted_modules_idx == sorted_modules.size())
				log_error("Cyclic dependency between modules found! Cycle includes module %s.\n", log_id(module_deps.begin()->first->name));
			while (sorted_modules_idx < sorted_modules.size())
				module_deps.erase(sorted_modules.at(sorted_modules_idx++));
		}

		dict<IdString, int> mod_stbv_width;
		dict<IdString, dict<IdString, pair<bool, bool>>> mod_clk_cache;
		Module *topmod = design->top_module();
		std::string topmod_id;

		for (auto module : sorted_modules)
			for (auto cell : module->cells())
				if (cell->type.in(ID($allconst), ID($allseq)))
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
			if (module->get_blackbox_attribute() && !module->has_attribute(ID::smtlib2_module))
				continue;

			if (module->has_processes_warn())
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
