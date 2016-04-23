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

struct SmvWorker
{
	CellTypes ct;
	SigMap sigmap;
	RTLIL::Module *module;
	std::ostream &f;
	bool verbose;

	int idcounter;
	dict<IdString, shared_str> idcache;
	pool<shared_str> used_names;
	vector<shared_str> strbuf;

	pool<Wire*> partial_assignment_wires;
	dict<SigBit, std::pair<const char*, int>> partial_assignment_bits;
	vector<string> assignments, invarspecs;

	const char *cid()
	{
		while (true) {
			shared_str s(stringf("_%d", idcounter++));
			if (!used_names.count(s)) {
				used_names.insert(s);
				return s.c_str();
			}
		}
	}

	const char *cid(IdString id, bool precache = false)
	{
		if (!idcache.count(id))
		{
			string name = stringf("_%s", id.c_str());

			if (name.substr(0, 2) == "_\\")
				name = "_" + name.substr(2);

			for (auto &c : name) {
				if (c == '|' || c == '$' || c == '_') continue;
				if (c >= 'a' && c <='z') continue;
				if (c >= 'A' && c <='Z') continue;
				if (c >= '0' && c <='9') continue;
				if (precache) return nullptr;
				c = '#';
			}

			if (name == "_main")
				name = "main";

			while (used_names.count(name))
				name += "_";

			shared_str s(name);
			used_names.insert(s);
			idcache[id] = s;
		}

		return idcache.at(id).c_str();
	}

	SmvWorker(RTLIL::Module *module, bool verbose, std::ostream &f) :
			ct(module->design), sigmap(module), module(module), f(f), verbose(verbose), idcounter(0)
	{
		for (auto mod : module->design->modules())
			cid(mod->name, true);

		for (auto wire : module->wires())
			cid(wire->name, true);

		for (auto cell : module->cells()) {
			cid(cell->name, true);
			cid(cell->type, true);
			for (auto &conn : cell->connections())
				cid(conn.first, true);
		}
	}

	const char *rvalue(SigSpec sig, int width = -1, bool is_signed = false)
	{
		string s;
		int count_chunks = 0;
		sigmap.apply(sig);

		for (int i = 0; i < GetSize(sig); i++)
			if (partial_assignment_bits.count(sig[i]))
			{
				int width = 1;
				const auto &bit_a = partial_assignment_bits.at(sig[i]);

				while (i+width < GetSize(sig))
				{
					if (!partial_assignment_bits.count(sig[i+width]))
						break;

					const auto &bit_b = partial_assignment_bits.at(sig[i+width]);
					if (strcmp(bit_a.first, bit_b.first))
						break;
					if (bit_a.second+width != bit_b.second)
						break;

					width++;
				}

				if (i+width < GetSize(sig))
					s = stringf("%s :: ", rvalue(sig.extract(i+width, GetSize(sig)-(width+i))));

				s += stringf("%s[%d:%d]", bit_a.first, bit_a.second+width-1, bit_a.second);

				if (i > 0)
					s += stringf(" :: %s", rvalue(sig.extract(0, i)));

				count_chunks = 3;
				goto continue_with_resize;
			}

		for (auto &c : sig.chunks()) {
			count_chunks++;
			if (!s.empty())
				s = " :: " + s;
			if (c.wire) {
				if (c.offset != 0 || c.width != c.wire->width)
					s = stringf("%s[%d:%d]", cid(c.wire->name), c.offset+c.width-1, c.offset) + s;
				else
					s = cid(c.wire->name) + s;
			} else {
				string v = stringf("0ub%d_", c.width);
				for (int i = c.width-1; i >= 0; i--)
					v += c.data.at(i) == State::S1 ? '1' : '0';
				s = v + s;
			}
		}

	continue_with_resize:;
		if (width >= 0) {
			if (is_signed) {
				if (GetSize(sig) > width)
					s = stringf("signed(resize(%s, %d))", s.c_str(), width);
				else
					s = stringf("resize(signed(%s), %d)", s.c_str(), width);
			} else
				s = stringf("resize(%s, %d)", s.c_str(), width);
		} else if (is_signed)
			s = stringf("signed(%s)", s.c_str());
		else if (count_chunks > 1)
			s = stringf("(%s)", s.c_str());

		strbuf.push_back(s);
		return strbuf.back().c_str();
	}

	const char *rvalue_u(SigSpec sig, int width = -1)
	{
		return rvalue(sig, width, false);
	}

	const char *rvalue_s(SigSpec sig, int width = -1, bool is_signed = true)
	{
		return rvalue(sig, width, is_signed);
	}

	const char *lvalue(SigSpec sig)
	{
		sigmap.apply(sig);

		if (sig.is_wire())
			return rvalue(sig);

		const char *temp_id = cid();
		f << stringf("    %s : unsigned word[%d]; -- %s\n", temp_id, GetSize(sig), log_signal(sig));

		int offset = 0;
		for (auto bit : sig) {
			log_assert(bit.wire != nullptr);
			partial_assignment_wires.insert(bit.wire);
			partial_assignment_bits[bit] = std::pair<const char*, int>(temp_id, offset++);
		}

		return temp_id;
	}

	void run()
	{
		f << stringf("MODULE %s\n", cid(module->name));
		f << stringf("  VAR\n");

		for (auto wire : module->wires())
		{
			if (SigSpec(wire) != sigmap(wire))
				partial_assignment_wires.insert(wire);

			f << stringf("    %s : unsigned word[%d]; -- %s\n", cid(wire->name), wire->width, log_id(wire));

			if (wire->attributes.count("\\init"))
				assignments.push_back(stringf("init(%s) := %s;", lvalue(wire), rvalue(wire->attributes.at("\\init"))));
		}

		for (auto cell : module->cells())
		{
			// FIXME: $slice, $concat, $mem

			if (cell->type.in("$assert"))
			{
				SigSpec sig_a = cell->getPort("\\A");
				SigSpec sig_en = cell->getPort("\\EN");

				invarspecs.push_back(stringf("!bool(%s) | bool(%s);", rvalue(sig_en), rvalue(sig_a)));

				continue;
			}

			if (cell->type.in("$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx"))
			{
				SigSpec sig_a = cell->getPort("\\A");
				SigSpec sig_b = cell->getPort("\\B");

				int width_y = GetSize(cell->getPort("\\Y"));
				int shift_b_width = GetSize(sig_b);
				int width_ay = max(GetSize(sig_a), width_y);
				int width = width_ay;

				for (int i = 1, j = 0;; i <<= 1, j++)
					if (width_ay < i) {
						width = i-1;
						shift_b_width = min(shift_b_width, j);
						break;
					}

				bool signed_a = cell->getParam("\\A_SIGNED").as_bool();
				bool signed_b = cell->getParam("\\B_SIGNED").as_bool();
				string op = cell->type.in("$shl", "$sshl") ? "<<" : ">>";
				string expr, expr_a;

				if (cell->type == "$sshr" && signed_a)
				{
					expr_a = rvalue_s(sig_a, width);
					expr = stringf("resize(unsigned(%s %s %s), %d)", expr_a.c_str(), op.c_str(), rvalue(sig_b.extract(0, shift_b_width)), width_y);
					if (shift_b_width < GetSize(sig_b))
						expr = stringf("%s != 0ud%d_0 ? (bool(%s) ? !0ud%d_0 : 0ud%d_0) : %s",
								rvalue(sig_b.extract(shift_b_width, GetSize(sig_b) - shift_b_width)), GetSize(sig_b) - shift_b_width,
								rvalue(sig_a[GetSize(sig_a)-1]), width_y, width_y, expr.c_str());
				}
				else if (cell->type.in("$shift", "$shiftx") && signed_b)
				{
					expr_a = rvalue_u(sig_a, width);

					const char *b_shr = rvalue_u(sig_b);
					const char *b_shl = cid();

					f << stringf("    %s : unsigned word[%d]; -- neg(%s)\n", b_shl, GetSize(sig_b), log_signal(sig_b));
					assignments.push_back(stringf("%s := unsigned(-%s);", b_shl, rvalue_s(sig_b)));

					string expr_shl = stringf("resize(%s << %s[%d:0], %d)", expr_a.c_str(), b_shl, shift_b_width-1, width_y);
					string expr_shr = stringf("resize(%s >> %s[%d:0], %d)", expr_a.c_str(), b_shr, shift_b_width-1, width_y);

					if (shift_b_width < GetSize(sig_b)) {
						expr_shl = stringf("%s[%d:%d] != 0ud%d_0 ? 0ud%d_0 : %s", b_shl, GetSize(sig_b)-1, shift_b_width,
								GetSize(sig_b)-shift_b_width, width_y, expr_shl.c_str());
						expr_shr = stringf("%s[%d:%d] != 0ud%d_0 ? 0ud%d_0 : %s", b_shr, GetSize(sig_b)-1, shift_b_width,
								GetSize(sig_b)-shift_b_width, width_y, expr_shr.c_str());
					}

					expr = stringf("bool(%s) ? %s : %s", rvalue(sig_b[GetSize(sig_b)-1]), expr_shl.c_str(), expr_shr.c_str());
				}
				else
				{
					if (cell->type.in("$shift", "$shiftx") || !signed_a)
						expr_a = rvalue_u(sig_a, width);
					else
						expr_a = stringf("resize(unsigned(%s), %d)", rvalue_s(sig_a, width_ay), width);

					expr = stringf("resize(%s %s %s[%d:0], %d)", expr_a.c_str(), op.c_str(), rvalue_u(sig_b), shift_b_width-1, width_y);
					if (shift_b_width < GetSize(sig_b))
						expr = stringf("%s[%d:%d] != 0ud%d_0 ? 0ud%d_0 : %s", rvalue_u(sig_b), GetSize(sig_b)-1, shift_b_width,
								GetSize(sig_b)-shift_b_width, width_y, expr.c_str());
				}

				assignments.push_back(stringf("%s := %s;", lvalue(cell->getPort("\\Y")), expr.c_str()));

				continue;
			}

			if (cell->type.in("$not", "$pos", "$neg"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				string expr_a, op;

				if (cell->type == "$not")  op = "!";
				if (cell->type == "$pos")  op = "";
				if (cell->type == "$neg")  op = "-";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					assignments.push_back(stringf("%s := unsigned(%s%s);", lvalue(cell->getPort("\\Y")),
							op.c_str(), rvalue_s(cell->getPort("\\A"), width)));
				}
				else
				{
					assignments.push_back(stringf("%s := %s%s;", lvalue(cell->getPort("\\Y")),
							op.c_str(), rvalue_u(cell->getPort("\\A"), width)));
				}

				continue;
			}

			if (cell->type.in("$add", "$sub", "$mul", "$and", "$or", "$xor", "$xnor"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				string expr_a, expr_b, op;

				if (cell->type == "$add")  op = "+";
				if (cell->type == "$sub")  op = "-";
				if (cell->type == "$mul")  op = "*";
				if (cell->type == "$and")  op = "&";
				if (cell->type == "$or")   op = "|";
				if (cell->type == "$xor")  op = "xor";
				if (cell->type == "$xnor") op = "xnor";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					assignments.push_back(stringf("%s := unsigned(%s %s %s);", lvalue(cell->getPort("\\Y")),
							rvalue_s(cell->getPort("\\A"), width), op.c_str(), rvalue_s(cell->getPort("\\B"), width)));
				}
				else
				{
					assignments.push_back(stringf("%s := %s %s %s;", lvalue(cell->getPort("\\Y")),
							rvalue_u(cell->getPort("\\A"), width), op.c_str(), rvalue_u(cell->getPort("\\B"), width)));
				}

				continue;
			}

			if (cell->type.in("$div", "$mod"))
			{
				int width_y = GetSize(cell->getPort("\\Y"));
				int width = max(width_y, GetSize(cell->getPort("\\A")));
				width = max(width, GetSize(cell->getPort("\\B")));
				string expr_a, expr_b, op;

				if (cell->type == "$div")  op = "/";
				if (cell->type == "$mod")  op = "mod";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					assignments.push_back(stringf("%s := resize(unsigned(%s %s %s), %d);", lvalue(cell->getPort("\\Y")),
							rvalue_s(cell->getPort("\\A"), width), op.c_str(), rvalue_s(cell->getPort("\\B"), width), width_y));
				}
				else
				{
					assignments.push_back(stringf("%s := resize(%s %s %s, %d);", lvalue(cell->getPort("\\Y")),
							rvalue_u(cell->getPort("\\A"), width), op.c_str(), rvalue_u(cell->getPort("\\B"), width), width_y));
				}

				continue;
			}

			if (cell->type.in("$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$ge", "$gt"))
			{
				int width = max(GetSize(cell->getPort("\\A")), GetSize(cell->getPort("\\B")));
				string expr_a, expr_b, op;

				if (cell->type == "$eq")  op = "=";
				if (cell->type == "$ne")  op = "!=";
				if (cell->type == "$eqx") op = "=";
				if (cell->type == "$nex") op = "!=";
				if (cell->type == "$lt")  op = "<";
				if (cell->type == "$le")  op = "<=";
				if (cell->type == "$ge")  op = ">=";
				if (cell->type == "$gt")  op = ">";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					expr_a = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\B")), width);
				}
				else
				{
					expr_a = stringf("resize(%s, %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(%s, %d)", rvalue(cell->getPort("\\B")), width);
				}

				assignments.push_back(stringf("%s := resize(word1(%s %s %s), %d);", lvalue(cell->getPort("\\Y")),
						expr_a.c_str(), op.c_str(), expr_b.c_str(), GetSize(cell->getPort("\\Y"))));

				continue;
			}

			if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_bool"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_y = GetSize(cell->getPort("\\Y"));
				const char *expr_a = rvalue(cell->getPort("\\A"));
				const char *expr_y = lvalue(cell->getPort("\\Y"));
				string expr;

				if (cell->type == "$reduce_and")  expr = stringf("%s = !0ub%d_0", expr_a, width_a);
				if (cell->type == "$reduce_or")   expr = stringf("%s != 0ub%d_0", expr_a, width_a);
				if (cell->type == "$reduce_bool") expr = stringf("%s != 0ub%d_0", expr_a, width_a);

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$reduce_xor", "$reduce_xnor"))
			{
				int width_y = GetSize(cell->getPort("\\Y"));
				const char *expr_y = lvalue(cell->getPort("\\Y"));
				string expr;

				for (auto bit : cell->getPort("\\A")) {
					if (!expr.empty())
						expr += " xor ";
					expr += rvalue(bit);
				}

				if (cell->type == "$reduce_xnor")
					expr = "!(" + expr + ")";

				assignments.push_back(stringf("%s := resize(%s, %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$logic_and", "$logic_or"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_b = GetSize(cell->getPort("\\B"));
				int width_y = GetSize(cell->getPort("\\Y"));

				string expr_a = stringf("(%s != 0ub%d_0)", rvalue(cell->getPort("\\A")), width_a);
				string expr_b = stringf("(%s != 0ub%d_0)", rvalue(cell->getPort("\\B")), width_b);
				const char *expr_y = lvalue(cell->getPort("\\Y"));

				string expr;
				if (cell->type == "$logic_and") expr = expr_a + " & " + expr_b;
				if (cell->type == "$logic_or")  expr = expr_a + " | " + expr_b;

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$logic_not"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_y = GetSize(cell->getPort("\\Y"));

				string expr_a = stringf("(%s = 0ub%d_0)", rvalue(cell->getPort("\\A")), width_a);
				const char *expr_y = lvalue(cell->getPort("\\Y"));

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr_a.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$mux", "$pmux"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				SigSpec sig_a = cell->getPort("\\A");
				SigSpec sig_b = cell->getPort("\\B");
				SigSpec sig_s = cell->getPort("\\S");

				string expr;
				for (int i = 0; i < GetSize(sig_s); i++)
					expr += stringf("bool(%s) ? %s : ", rvalue(sig_s[i]), rvalue(sig_b.extract(i*width, width)));
				expr += rvalue(sig_a);

				assignments.push_back(stringf("%s := %s;", lvalue(cell->getPort("\\Y")), expr.c_str()));
				continue;
			}

			if (cell->type == "$dff")
			{
				assignments.push_back(stringf("next(%s) := %s;", lvalue(cell->getPort("\\Q")), rvalue(cell->getPort("\\D"))));
				continue;
			}

			if (cell->type.in("$_BUF_", "$_NOT_"))
			{
				string op = cell->type == "$_NOT_" ? "!" : "";
				assignments.push_back(stringf("%s := %s%s;", lvalue(cell->getPort("\\Y")), op.c_str(), rvalue(cell->getPort("\\A"))));
				continue;
			}

			if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_"))
			{
				string op;

				if (cell->type.in("$_AND_", "$_NAND_")) op = "&";
				if (cell->type.in("$_OR_", "$_NOR_")) op = "|";
				if (cell->type.in("$_XOR_"))  op = "xor";
				if (cell->type.in("$_XNOR_"))  op = "xnor";

				if (cell->type.in("$_NAND_", "$_NOR_"))
					assignments.push_back(stringf("%s := !(%s %s %s);", lvalue(cell->getPort("\\Y")),
							rvalue(cell->getPort("\\A")), op.c_str(), rvalue(cell->getPort("\\B"))));
				else
					assignments.push_back(stringf("%s := %s %s %s;", lvalue(cell->getPort("\\Y")),
							rvalue(cell->getPort("\\A")), op.c_str(), rvalue(cell->getPort("\\B"))));
				continue;
			}

			if (cell->type == "$_MUX_")
			{
				assignments.push_back(stringf("%s := bool(%s) ? %s : %s;", lvalue(cell->getPort("\\Y")),
						rvalue(cell->getPort("\\S")), rvalue(cell->getPort("\\B")), rvalue(cell->getPort("\\A"))));
				continue;
			}

			if (cell->type == "$_AOI3_")
			{
				assignments.push_back(stringf("%s := !((%s & %s) | %s);", lvalue(cell->getPort("\\Y")),
						rvalue(cell->getPort("\\A")), rvalue(cell->getPort("\\B")), rvalue(cell->getPort("\\C"))));
				continue;
			}

			if (cell->type == "$_OAI3_")
			{
				assignments.push_back(stringf("%s := !((%s | %s) & %s);", lvalue(cell->getPort("\\Y")),
						rvalue(cell->getPort("\\A")), rvalue(cell->getPort("\\B")), rvalue(cell->getPort("\\C"))));
				continue;
			}

			if (cell->type == "$_AOI4_")
			{
				assignments.push_back(stringf("%s := !((%s & %s) | (%s & %s));", lvalue(cell->getPort("\\Y")),
						rvalue(cell->getPort("\\A")), rvalue(cell->getPort("\\B")), rvalue(cell->getPort("\\C")), rvalue(cell->getPort("\\D"))));
				continue;
			}

			if (cell->type == "$_OAI4_")
			{
				assignments.push_back(stringf("%s := !((%s | %s) & (%s | %s));", lvalue(cell->getPort("\\Y")),
						rvalue(cell->getPort("\\A")), rvalue(cell->getPort("\\B")), rvalue(cell->getPort("\\C")), rvalue(cell->getPort("\\D"))));
				continue;
			}

			if (cell->type[0] == '$')
				log_error("Found currently unsupported cell type %s (%s.%s).\n", log_id(cell->type), log_id(module), log_id(cell));

			f << stringf("    %s : %s;\n", cid(cell->name), cid(cell->type));

			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					assignments.push_back(stringf("%s := %s.%s;", lvalue(conn.second), cid(cell->name), cid(conn.first)));
				else
					assignments.push_back(stringf("%s.%s := %s;", cid(cell->name), cid(conn.first), rvalue(conn.second)));
		}

		for (Wire *wire : partial_assignment_wires)
		{
			string expr;

			for (int i = 0; i < wire->width; i++)
			{
				if (!expr.empty())
					expr = " :: " + expr;

				if (partial_assignment_bits.count(sigmap(SigBit(wire, i))))
				{
					int width = 1;
					const auto &bit_a = partial_assignment_bits.at(sigmap(SigBit(wire, i)));

					while (i+1 < wire->width)
					{
						SigBit next_bit = sigmap(SigBit(wire, i+1));

						if (!partial_assignment_bits.count(next_bit))
							break;

						const auto &bit_b = partial_assignment_bits.at(next_bit);
						if (strcmp(bit_a.first, bit_b.first))
							break;
						if (bit_a.second+width != bit_b.second)
							break;

						width++, i++;
					}

					expr = stringf("%s[%d:%d]", bit_a.first, bit_a.second+width-1, bit_a.second) + expr;
				}
				else if (sigmap(SigBit(wire, i)).wire == nullptr)
				{
					string bits;
					SigSpec sig = sigmap(SigSpec(wire, i));

					while (i+1 < wire->width) {
						SigBit next_bit = sigmap(SigBit(wire, i+1));
						if (next_bit.wire != nullptr)
							break;
						sig.append(next_bit);
						i++;
					}

					for (int k = GetSize(sig)-1; k >= 0; k--)
						bits += sig[k] == State::S1 ? '1' : '0';

					expr = stringf("0ub%d_%s", GetSize(bits), bits.c_str()) + expr;
				}
				else if (sigmap(SigBit(wire, i)) == SigBit(wire, i))
				{
					int length = 1;

					while (i+1 < wire->width) {
						if (partial_assignment_bits.count(sigmap(SigBit(wire, i+1))))
							break;
						if (sigmap(SigBit(wire, i+1)) != SigBit(wire, i+1))
							break;
						i++, length++;
					}

					expr = stringf("0ub%d_0", length) + expr;
				}
				else
				{
					string bits;
					SigSpec sig = sigmap(SigSpec(wire, i));

					while (i+1 < wire->width) {
						SigBit next_bit = sigmap(SigBit(wire, i+1));
						if (next_bit.wire == nullptr || partial_assignment_bits.count(next_bit))
							break;
						sig.append(next_bit);
						i++;
					}

					expr = rvalue(sig) + expr;
				}
			}

			assignments.push_back(stringf("%s := %s;", cid(wire->name), expr.c_str()));
		}

		if (!assignments.empty()) {
			f << stringf("  ASSIGN\n");
			for (const string &line : assignments)
				f << stringf("    %s\n", line.c_str());
		}

		if (!invarspecs.empty()) {
			for (const string &line : invarspecs)
				f << stringf("  INVARSPEC %s\n", line.c_str());
		}
	}
};

struct SmvBackend : public Backend {
	SmvBackend() : Backend("smv", "write design to SMV file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smv [options] [filename]\n");
		log("\n");
		log("Write an SMV description of the current design.\n");
		log("\n");
		log("    -verbose\n");
		log("        this will print the recursive walk used to export the modules.\n");
		log("\n");
		log("    -tpl <template_file>\n");
		log("        use the given template file. the line containing only the token '%%%%'\n");
		log("        is replaced with the regular output of this command.\n");
		log("\n");
		log("THIS COMMAND IS UNDER CONSTRUCTION\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::ifstream template_f;
		bool verbose = false;

		log_header(design, "Executing SMV backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tpl" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-verbose") {
				verbose = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		pool<Module*> modules;

		for (auto module : design->modules())
			if (!module->get_bool_attribute("\\blackbox") && !module->has_memories_warn() && !module->has_processes_warn())
				modules.insert(module);

		if (template_f.is_open())
		{
			std::string line;
			while (std::getline(template_f, line))
			{
				int indent = 0;
				while (indent < GetSize(line) && (line[indent] == ' ' || line[indent] == '\t'))
					indent++;

				if (line[indent] == '%')
				{
					vector<string> stmt = split_tokens(line);

					if (GetSize(stmt) == 1 && stmt[0] == "%%")
						break;

					if (GetSize(stmt) == 2 && stmt[0] == "%module")
					{
						Module *module = design->module(RTLIL::escape_id(stmt[1]));
						modules.erase(module);

						if (module == nullptr)
							log_error("Module '%s' not found.\n", stmt[1].c_str());

						*f << stringf("-- SMV description generated by %s\n", yosys_version_str);

						log("Creating SMV representation of module %s.\n", log_id(module));
						SmvWorker worker(module, verbose, *f);
						worker.run();

						*f << stringf("-- end of yosys output\n");
						continue;
					}

					log_error("Unknown template statement: '%s'", line.c_str() + indent);
				}

				*f << line << std::endl;
			}
		}

		if (!modules.empty())
		{
			*f << stringf("-- SMV description generated by %s\n", yosys_version_str);

			for (auto module : modules) {
				log("Creating SMV representation of module %s.\n", log_id(module));
				SmvWorker worker(module, verbose, *f);
				worker.run();
			}

			*f << stringf("-- end of yosys output\n");
		}

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line))
				*f << line << std::endl;
		}
	}
} SmvBackend;

PRIVATE_NAMESPACE_END
