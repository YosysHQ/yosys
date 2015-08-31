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
	bool bvmode, memmode, regsmode, verbose;
	int idcounter;

	std::vector<std::string> decls, trans;
	std::map<RTLIL::SigBit, RTLIL::Cell*> bit_driver;
	std::set<RTLIL::Cell*> exported_cells;
	pool<Cell*> recursive_cells, registers;

	std::map<RTLIL::SigBit, std::pair<int, int>> fcache;
	std::map<Cell*, int> memarrays;
	std::map<int, int> bvsizes;

	Smt2Worker(RTLIL::Module *module, bool bvmode, bool memmode, bool regsmode, bool verbose) :
			ct(module->design), sigmap(module), module(module), bvmode(bvmode), memmode(memmode), regsmode(regsmode), verbose(verbose), idcounter(0)
	{
		decls.push_back(stringf("(declare-sort |%s_s| 0)\n", log_id(module)));

		for (auto cell : module->cells())
		for (auto &conn : cell->connections()) {
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
		}
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
			decls.push_back(stringf("(declare-fun |%s#%d| (|%s_s|) Bool) ; %s\n",
					log_id(module), idcounter, log_id(module), log_signal(bit)));
			register_bool(bit, idcounter++);
		}

		auto f = fcache.at(bit);
		if (f.second >= 0)
			return stringf("(= ((_ extract %d %d) (|%s#%d| %s)) #b1)", f.second, f.second, log_id(module), f.first, state_name);
		return stringf("(|%s#%d| %s)", log_id(module), f.first, state_name);
	}

	std::string get_bool(RTLIL::SigSpec sig, const char *state_name = "state")
	{
		return get_bool(sig.to_single_sigbit(), state_name);
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
					subexpr.push_back(stringf("(|%s#%d| %s)", log_id(module), t1.first, state_name));
				else
					subexpr.push_back(stringf("((_ extract %d %d) (|%s#%d| %s))",
							t1.second + j - 1, t1.second, log_id(module), t1.first, state_name));
				continue;
			}

			std::set<RTLIL::SigBit> seen_bits = { sig[i] };
			while (i+j < GetSize(sig) && sig[i+j].wire && !fcache.count(sig[i+j]) && !seen_bits.count(sig[i+j]))
				seen_bits.insert(sig[i+j]), j++;

			if (verbose) log("%*s-> external bv: %s\n", 2+2*GetSize(recursive_cells), "",
					log_signal(sig.extract(i, j)));
			for (auto bit : sig.extract(i, j))
				log_assert(bit_driver.count(bit) == 0);
			decls.push_back(stringf("(declare-fun |%s#%d| (|%s_s|) (_ BitVec %d)) ; %s\n",
					log_id(module), idcounter, log_id(module), j, log_signal(sig.extract(i, j))));
			subexpr.push_back(stringf("(|%s#%d| %s)", log_id(module), idcounter, state_name));
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
		RTLIL::SigBit bit = sigmap(cell->getPort("\\Y").to_single_sigbit());
		std::string processed_expr;

		for (char ch : expr) {
			if (ch == 'A') processed_expr += get_bool(cell->getPort("\\A"));
			else if (ch == 'B') processed_expr += get_bool(cell->getPort("\\B"));
			else if (ch == 'C') processed_expr += get_bool(cell->getPort("\\C"));
			else if (ch == 'D') processed_expr += get_bool(cell->getPort("\\D"));
			else if (ch == 'S') processed_expr += get_bool(cell->getPort("\\S"));
			else processed_expr += ch;
		}

		if (verbose) log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "",
				log_id(cell));
		decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
				log_id(module), idcounter, log_id(module), processed_expr.c_str(), log_signal(bit)));
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
			width = std::max(width, GetSize(cell->getPort("\\A")));
			width = std::max(width, GetSize(cell->getPort("\\B")));
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
			else if (ch == 'L') processed_expr += is_signed ? "a" : "l";
			else if (ch == 'U') processed_expr += is_signed ? "s" : "u";
			else processed_expr += ch;
		}

		if (width != GetSize(sig_y) && type != 'b')
			processed_expr = stringf("((_ extract %d 0) %s)", GetSize(sig_y)-1, processed_expr.c_str());

		if (verbose) log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "",
				log_id(cell));

		if (type == 'b') {
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
					log_id(module), idcounter, log_id(module), processed_expr.c_str(), log_signal(sig_y)));
			register_boolvec(sig_y, idcounter++);
		} else {
			decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
					log_id(module), idcounter, log_id(module), GetSize(sig_y), processed_expr.c_str(), log_signal(sig_y)));
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

		if (verbose) log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "",
				log_id(cell));
		decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool %s) ; %s\n",
				log_id(module), idcounter, log_id(module), processed_expr.c_str(), log_signal(sig_y)));
		register_boolvec(sig_y, idcounter++);
		recursive_cells.erase(cell);
	}

	void export_cell(RTLIL::Cell *cell)
	{
		if (verbose) log("%*s=> export_cell %s (%s) [%s]\n", 2+2*GetSize(recursive_cells), "",
				log_id(cell), log_id(cell->type), exported_cells.count(cell) ? "old" : "new");

		if (recursive_cells.count(cell))
			log_error("Found logic loop in module %s! See cell %s.\n", log_id(module), log_id(cell));

		if (exported_cells.count(cell))
			return;

		exported_cells.insert(cell);
		recursive_cells.insert(cell);

		if (cell->type == "$_DFF_P_" || cell->type == "$_DFF_N_")
		{
			registers.insert(cell);
			decls.push_back(stringf("(declare-fun |%s#%d| (|%s_s|) Bool) ; %s\n",
					log_id(module), idcounter, log_id(module), log_signal(cell->getPort("\\Q"))));
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
		if (cell->type == "$_MUX_") return export_gate(cell, "(ite S B A)");
		if (cell->type == "$_AOI3_") return export_gate(cell, "(not (or (and A B) C))");
		if (cell->type == "$_OAI3_") return export_gate(cell, "(not (and (or A B) C))");
		if (cell->type == "$_AOI4_") return export_gate(cell, "(not (or (and A B) (and C D)))");
		if (cell->type == "$_OAI4_") return export_gate(cell, "(not (and (or A B) (or C D)))");

		// FIXME: $lut

		if (bvmode)
		{
			if (cell->type == "$dff")
			{
				registers.insert(cell);
				decls.push_back(stringf("(declare-fun |%s#%d| (|%s_s|) (_ BitVec %d)) ; %s\n",
						log_id(module), idcounter, log_id(module), GetSize(cell->getPort("\\Q")), log_signal(cell->getPort("\\Q"))));
				register_bv(cell->getPort("\\Q"), idcounter++);
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

			// FIXME: $shift $shiftx

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

			if (cell->type == "$reduce_and") return export_reduce(cell, "(and A)", true);
			if (cell->type == "$reduce_or") return export_reduce(cell, "(or A)", false);
			if (cell->type == "$reduce_xor") return export_reduce(cell, "(xor A)", false);
			if (cell->type == "$reduce_xnor") return export_reduce(cell, "(not (xor A))", false);
			if (cell->type == "$reduce_bool") return export_reduce(cell, "(or A)", false);

			if (cell->type == "$logic_not") return export_reduce(cell, "(not (or A))", false);
			if (cell->type == "$logic_and") return export_reduce(cell, "(and (or A) (or B))", false);
			if (cell->type == "$logic_or") return export_reduce(cell, "(or A B)", false);

			if (cell->type == "$mux" || cell->type == "$pmux")
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

				if (verbose) log("%*s-> import cell: %s\n", 2+2*GetSize(recursive_cells), "",
						log_id(cell));
				RTLIL::SigSpec sig = sigmap(cell->getPort("\\Y"));
				decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) %s) ; %s\n",
						log_id(module), idcounter, log_id(module), width, processed_expr.c_str(), log_signal(sig)));
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

			decls.push_back(stringf("(declare-fun |%s#%d#0| (|%s_s|) (Array (_ BitVec %d) (_ BitVec %d))) ; %s\n",
					log_id(module), arrayid, log_id(module), abits, width, log_id(cell)));

			decls.push_back(stringf("(define-fun |%s_m %s| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) (|%s#%d#0| state))\n",
					log_id(module), log_id(cell), log_id(module), abits, width, log_id(module), arrayid));

			for (int i = 0; i < rd_ports; i++)
			{
				std::string addr = get_bv(cell->getPort("\\RD_ADDR").extract(abits*i, abits));
				SigSpec data_sig = cell->getPort("\\RD_DATA").extract(width*i, width);

				if (cell->getParam("\\RD_CLK_ENABLE").extract(i).as_bool())
					log_error("Read port %d (%s) of memory %s.%s is clocked. This is not supported by \"write_smt2\"! "
							"Call \"memory\" with -nordff to avoid this error.\n", i, log_signal(data_sig), log_id(cell), log_id(module));

				decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) (_ BitVec %d) (select (|%s#%d#0| state) %s)) ; %s\n",
						log_id(module), idcounter, log_id(module), width, log_id(module), arrayid, addr.c_str(), log_signal(data_sig)));
				register_bv(data_sig, idcounter++);
			}

			registers.insert(cell);
			recursive_cells.erase(cell);
			return;
		}

		log_error("Unsupported cell type %s for cell %s.%s. (Maybe this cell type would be supported in -bv or -mem mode?)\n",
				log_id(cell->type), log_id(module), log_id(cell));
	}

	void run()
	{
		if (verbose) log("=> export logic driving outputs\n");

		pool<SigBit> reg_bits;
		if (regsmode) {
			for (auto cell : module->cells())
				if (cell->type.in("$_DFF_P_", "$_DFF_N_", "$dff")) {
					// not using sigmap -- we want the net directly at the dff output
					for (auto bit : cell->getPort("\\Q"))
						reg_bits.insert(bit);
				}
		}

		for (auto wire : module->wires()) {
			bool is_register = false;
			if (regsmode)
				for (auto bit : SigSpec(wire))
					if (reg_bits.count(bit))
						is_register = true;
			if (wire->port_id || is_register || wire->get_bool_attribute("\\keep")) {
				RTLIL::SigSpec sig = sigmap(wire);
				if (wire->port_input)
					decls.push_back(stringf("; yosys-smt2-input %s %d\n", log_id(wire), wire->width));
				if (wire->port_output)
					decls.push_back(stringf("; yosys-smt2-output %s %d\n", log_id(wire), wire->width));
				if (is_register)
					decls.push_back(stringf("; yosys-smt2-register %s %d\n", log_id(wire), wire->width));
				if (wire->get_bool_attribute("\\keep"))
					decls.push_back(stringf("; yosys-smt2-wire %s %d\n", log_id(wire), wire->width));
				if (bvmode && GetSize(sig) > 1) {
					decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) (_ BitVec %d) %s)\n",
							log_id(module), log_id(wire), log_id(module), GetSize(sig), get_bv(sig).c_str()));
				} else {
					for (int i = 0; i < GetSize(sig); i++)
						if (GetSize(sig) > 1)
							decls.push_back(stringf("(define-fun |%s_n %s %d| ((state |%s_s|)) Bool %s)\n",
									log_id(module), log_id(wire), i, log_id(module), get_bool(sig[i]).c_str()));
						else
							decls.push_back(stringf("(define-fun |%s_n %s| ((state |%s_s|)) Bool %s)\n",
									log_id(module), log_id(wire), log_id(module), get_bool(sig[i]).c_str()));
				}
			}
		}

		if (verbose) log("=> export logic associated with the initial state\n");

		vector<string> init_list;
		for (auto wire : module->wires())
			if (wire->attributes.count("\\init")) {
				RTLIL::SigSpec sig = sigmap(wire);
				Const val = wire->attributes.at("\\init");
				val.bits.resize(GetSize(sig));
				if (bvmode && GetSize(sig) > 1) {
					init_list.push_back(stringf("(= %s #b%s) ; %s", get_bv(sig).c_str(), val.as_string().c_str(), log_id(wire)));
				} else {
					for (int i = 0; i < GetSize(sig); i++)
						init_list.push_back(stringf("(= %s %s) ; %s", get_bool(sig[i]).c_str(), val.bits[i] == State::S1 ? "true" : "false", log_id(wire)));
				}
			}

		if (verbose) log("=> export logic driving asserts\n");

		vector<int> assert_list, assume_list;
		for (auto cell : module->cells())
			if (cell->type.in("$assert", "$assume")) {
				string name_a = get_bool(cell->getPort("\\A"));
				string name_en = get_bool(cell->getPort("\\EN"));
				decls.push_back(stringf("(define-fun |%s#%d| ((state |%s_s|)) Bool (or %s (not %s))) ; %s\n",
					log_id(module), idcounter, log_id(module), name_a.c_str(), name_en.c_str(), log_id(cell)));
				if (cell->type == "$assert")
					assert_list.push_back(idcounter++);
				else
					assume_list.push_back(idcounter++);
			}

		for (int iter = 1; !registers.empty(); iter++)
		{
			pool<Cell*> this_regs;
			this_regs.swap(registers);

			if (verbose) log("=> export logic driving registers [iteration %d]\n", iter);

			for (auto cell : this_regs)
			{
				if (cell->type == "$_DFF_P_" || cell->type == "$_DFF_N_")
				{
					std::string expr_d = get_bool(cell->getPort("\\D"));
					std::string expr_q = get_bool(cell->getPort("\\Q"), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), log_id(cell), log_signal(cell->getPort("\\Q"))));
				}

				if (cell->type == "$dff")
				{
					std::string expr_d = get_bv(cell->getPort("\\D"));
					std::string expr_q = get_bv(cell->getPort("\\Q"), "next_state");
					trans.push_back(stringf("  (= %s %s) ; %s %s\n", expr_d.c_str(), expr_q.c_str(), log_id(cell), log_signal(cell->getPort("\\Q"))));
				}

				if (cell->type == "$mem")
				{
					int arrayid = memarrays.at(cell);

					int abits = cell->getParam("\\ABITS").as_int();
					int width = cell->getParam("\\WIDTH").as_int();
					int wr_ports = cell->getParam("\\WR_PORTS").as_int();

					for (int i = 0; i < wr_ports; i++)
					{
						std::string addr = get_bv(cell->getPort("\\WR_ADDR").extract(abits*i, abits));
						std::string data = get_bv(cell->getPort("\\WR_DATA").extract(width*i, width));
						std::string mask = get_bv(cell->getPort("\\WR_EN").extract(width*i, width));

						data = stringf("(bvor (bvand %s %s) (bvand (select (|%s#%d#%d| state) %s) (bvnot %s)))",
								data.c_str(), mask.c_str(), log_id(module), arrayid, i, addr.c_str(), mask.c_str());

						decls.push_back(stringf("(define-fun |%s#%d#%d| ((state |%s_s|)) (Array (_ BitVec %d) (_ BitVec %d)) "
								"(store (|%s#%d#%d| state) %s %s)) ; %s\n",
								log_id(module), arrayid, i+1, log_id(module), abits, width,
								log_id(module), arrayid, i, addr.c_str(), data.c_str(), log_id(cell)));
					}

					std::string expr_d = stringf("(|%s#%d#%d| state)", log_id(module), arrayid, wr_ports);
					std::string expr_q = stringf("(|%s#%d#0| next_state)", log_id(module), arrayid);
					trans.push_back(stringf("  (= %s %s) ; %s\n", expr_d.c_str(), expr_q.c_str(), log_id(cell)));
				}
			}
		}

		string assert_expr = assert_list.empty() ? "true" : "(and";
		if (!assert_list.empty()) {
			for (int i : assert_list)
				assert_expr += stringf(" (|%s#%d| state)", log_id(module), i);
			assert_expr += ")";
		}
		decls.push_back(stringf("(define-fun |%s_a| ((state |%s_s|)) Bool %s)\n",
				log_id(module), log_id(module), assert_expr.c_str()));

		string assume_expr = assume_list.empty() ? "true" : "(and";
		if (!assume_list.empty()) {
			for (int i : assume_list)
				assume_expr += stringf(" (|%s#%d| state)", log_id(module), i);
			assume_expr += ")";
		}
		decls.push_back(stringf("(define-fun |%s_u| ((state |%s_s|)) Bool %s)\n",
				log_id(module), log_id(module), assume_expr.c_str()));

		string init_expr = init_list.empty() ? "true" : "(and";
		if (!init_list.empty()) {
			for (auto &str : init_list)
				init_expr += stringf("\n\t%s", str.c_str());
			init_expr += "\n)";
		}
		decls.push_back(stringf("(define-fun |%s_i| ((state |%s_s|)) Bool %s)\n",
				log_id(module), log_id(module), init_expr.c_str()));
	}

	void write(std::ostream &f)
	{
		for (auto it : decls)
			f << it;

		f << stringf("(define-fun |%s_t| ((state |%s_s|) (next_state |%s_s|)) Bool ", log_id(module), log_id(module), log_id(module));
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
		f << stringf(" ; end of module %s\n", log_id(module));
	}
};

struct Smt2Backend : public Backend {
	Smt2Backend() : Backend("smt2", "write design to SMT-LIBv2 file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smt2 [options] [filename]\n");
		log("\n");
		log("Write a SMT-LIBv2 [1] description of the current design. For a module with name\n");
		log("'<mod>' this will declare the sort '<mod>_s' (state of the module) and the\n");
		log("functions operating on that state.\n");
		log("\n");
		log("The '<mod>_s' sort represents a module state. Additional '<mod>_n' functions\n");
		log("are provided that can be used to access the values of the signals in the module.\n");
		log("Only ports, and signals with the 'keep' attribute set are made available via\n");
		log("such functions. Without the -bv option, multi-bit wires are exported as\n");
		log("separate functions of type Bool for the individual bits. With the -bv option\n");
		log("multi-bit wires are exported as single functions of type BitVec.\n");
		log("\n");
		log("The '<mod>_t' function evaluates to 'true' when the given pair of states\n");
		log("describes a valid state transition.\n");
		log("\n");
		log("The '<mod>_a' function evaluates to 'true' when the given state satisfies\n");
		log("the asserts in the module.\n");
		log("\n");
		log("The '<mod>_u' function evaluates to 'true' when the given state satisfies\n");
		log("the assumptions in the module.\n");
		log("\n");
		log("The '<mod>_i' function evaluates to 'true' when the given state conforms\n");
		log("to the initial state.\n");
		log("\n");
		log("    -verbose\n");
		log("        this will print the recursive walk used to export the modules.\n");
		log("\n");
		log("    -bv\n");
		log("        enable support for BitVec (FixedSizeBitVectors theory). with this\n");
		log("        option set multi-bit wires are represented using the BitVec sort and\n");
		log("        support for coarse grain cells (incl. arithmetic) is enabled.\n");
		log("\n");
		log("    -mem\n");
		log("        enable support for memories (via ArraysEx theory). this option\n");
		log("        also implies -bv. only $mem cells without merged registers in\n");
		log("        read ports are supported. call \"memory\" with -nordff to make sure\n");
		log("        that no registers are merged into $mem read ports. '<mod>_m' functions\n");
		log("        will be generated for accessing the arrays that are used to represent\n");
		log("        memories.\n");
		log("\n");
		log("    -regs\n");
		log("        also create '<mod>_n' functions for all registers.\n");
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
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::ifstream template_f;
		bool bvmode = false, memmode = false, regsmode = false, verbose = false;

		log_header("Executing SMT2 backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tpl" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-bv") {
				bvmode = true;
				continue;
			}
			if (args[argidx] == "-mem") {
				bvmode = true;
				memmode = true;
				continue;
			}
			if (args[argidx] == "-regs") {
				regsmode = true;
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
				if (line.substr(indent, 2) == "%%")
					break;
				*f << line << std::endl;
			}
		}

		*f << stringf("; SMT-LIBv2 description generated by %s\n", yosys_version_str);

		for (auto module : design->modules())
		{
			if (module->get_bool_attribute("\\blackbox") || module->has_memories_warn() || module->has_processes_warn())
				continue;

			log("Creating SMT-LIBv2 representation of module %s.\n", log_id(module));

			Smt2Worker worker(module, bvmode, memmode, regsmode, verbose);
			worker.run();
			worker.write(*f);
		}

		*f << stringf("; end of yosys output\n");

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line))
				*f << line << std::endl;
		}
	}
} Smt2Backend;

PRIVATE_NAMESPACE_END
