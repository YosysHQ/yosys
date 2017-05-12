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
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct HierDirtyFlags;

struct HierDirtyFlags
{
	int dirty;
	Module *module;
	IdString hiername;
	HierDirtyFlags *parent;
	pool<SigBit> dirty_bits;
	pool<Cell*> dirty_cells;
	dict<IdString, HierDirtyFlags*> children;

	HierDirtyFlags(Module *module, IdString hiername, HierDirtyFlags *parent) : dirty(0), module(module), hiername(hiername), parent(parent)
	{
		for (Cell *cell : module->cells()) {
			Module *mod = module->design->module(cell->type);
			if (mod) children[cell->name] = new HierDirtyFlags(mod, cell->name, this);
		}
	}

	~HierDirtyFlags()
	{
		for (auto &child : children)
			delete child.second;
	}

	void set_dirty(SigBit bit)
	{
		if (dirty_bits.count(bit))
			return;

		dirty_bits.insert(bit);

		HierDirtyFlags *p = this;
		while (p != nullptr) {
			p->dirty++;
			p = p->parent;
		}
	}

	void unset_dirty(SigBit bit)
	{
		if (dirty_bits.count(bit) == 0)
			return;

		dirty_bits.erase(bit);

		HierDirtyFlags *p = this;
		while (p != nullptr) {
			p->dirty--;
			log_assert(p->dirty >= 0);
			p = p->parent;
		}
	}

	void set_dirty(Cell *cell)
	{
		if (dirty_cells.count(cell))
			return;

		dirty_cells.insert(cell);

		HierDirtyFlags *p = this;
		while (p != nullptr) {
			p->dirty++;
			p = p->parent;
		}
	}

	void unset_dirty(Cell *cell)
	{
		if (dirty_cells.count(cell) == 0)
			return;

		dirty_cells.erase(cell);

		HierDirtyFlags *p = this;
		while (p != nullptr) {
			p->dirty--;
			log_assert(p->dirty >= 0);
			p = p->parent;
		}
	}
};

struct SimplecWorker
{
	bool verbose = false;
	int max_uintsize = 32;

	Design *design;
	dict<Module*, SigMap> sigmaps;
	HierDirtyFlags *dirty_flags = nullptr;

	vector<string> signal_declarations;
	pool<int> generated_sigtypes;

	vector<string> util_declarations;
	pool<string> generated_utils;

	vector<string> struct_declarations;
	pool<IdString> generated_structs;

	vector<string> funct_declarations;

	pool<string> reserved_cids;
	dict<IdString, string> id2cid;

	dict<Module*, dict<SigBit, pool<tuple<Cell*, IdString, int>>>> bit2cell;
	dict<Module*, dict<SigBit, pool<SigBit>>> bit2output;

	dict<Cell*, int> topoidx;

	SimplecWorker(Design *design) : design(design)
	{
	}

	string sigtype(int n)
	{
		string struct_name = stringf("signal%d_t", n);

		if (generated_sigtypes.count(n) == 0)
		{
			signal_declarations.push_back("");
			signal_declarations.push_back(stringf("#ifndef YOSYS_SIMPLEC_SIGNAL%d_T", n));
			signal_declarations.push_back(stringf("#define YOSYS_SIMPLEC_SIGNAL%d_T", n));
			signal_declarations.push_back(stringf("typedef struct {"));

			for (int k = 8; k <= max_uintsize; k = 2*k)
				if (n <= k && k <= max_uintsize) {
					signal_declarations.push_back(stringf("  uint%d_t value_%d_0 : %d;", k, n-1, n));
					goto end_struct;
				}

			for (int k = 0; k < n; k += max_uintsize) {
				int bits = std::min(max_uintsize, n-k);
				signal_declarations.push_back(stringf("  uint%d_t value_%d_%d : %d;", max_uintsize, k+bits-1, k, bits));
			}

		end_struct:
			signal_declarations.push_back(stringf("} signal%d_t;", n));
			signal_declarations.push_back(stringf("#endif"));
			generated_sigtypes.insert(n);
		}

		return struct_name;
	}

	void util_ifdef_guard(string s)
	{
		for (int i = 0; i < GetSize(s); i++)
			if ('a' <= s[i] && s[i] <= 'z')
				s[i] -= 'a' - 'A';

		util_declarations.push_back(stringf("#ifndef %s", s.c_str()));
		util_declarations.push_back(stringf("#define %s", s.c_str()));
	}

	string util_get_bit(int n, int idx)
	{
		string util_name = stringf("yosys_simplec_get_bit_%d_of_%d", idx, n);

		if (generated_utils.count(util_name) == 0)
		{
			util_ifdef_guard(util_name);
			util_declarations.push_back(stringf("bool %s(const %s *sig)", util_name.c_str(), sigtype(n).c_str()));
			util_declarations.push_back(stringf("{"));

			int word_idx = idx / max_uintsize, word_offset = idx % max_uintsize;
			string value_name = stringf("value_%d_%d", std::min(n-1, (word_idx+1)*max_uintsize-1), word_idx*max_uintsize);

			util_declarations.push_back(stringf("  return (sig->%s >> %d) & 1;", value_name.c_str(), word_offset));

			util_declarations.push_back(stringf("}"));
			util_declarations.push_back(stringf("#endif"));
			generated_utils.insert(util_name);
		}

		return util_name;
	}

	string util_set_bit(int n, int idx)
	{
		string util_name = stringf("yosys_simplec_set_bit_%d_of_%d", idx, n);

		if (generated_utils.count(util_name) == 0)
		{
			util_ifdef_guard(util_name);
			util_declarations.push_back(stringf("void %s(%s *sig, bool value)", util_name.c_str(), sigtype(n).c_str()));
			util_declarations.push_back(stringf("{"));

			int word_idx = idx / max_uintsize, word_offset = idx % max_uintsize;
			string value_name = stringf("value_%d_%d", std::min(n-1, (word_idx+1)*max_uintsize-1), word_idx*max_uintsize);

			util_declarations.push_back(stringf("  if (value)"));
			util_declarations.push_back(stringf("    sig->%s |= 1UL << %d;", value_name.c_str(), word_offset));
			util_declarations.push_back(stringf("  else"));
			util_declarations.push_back(stringf("    sig->%s &= ~(1UL << %d);", value_name.c_str(), word_offset));

			util_declarations.push_back(stringf("}"));
			util_declarations.push_back(stringf("#endif"));
			generated_utils.insert(util_name);
		}

		return util_name;
	}

	string cid(IdString id)
	{
		if (id2cid.count(id) == 0)
		{
			string s = id.str();
			if (GetSize(s) < 2) log_abort();

			if (s[0] == '\\')
				s = s.substr(1);

			if ('0' <= s[0] && s[0] <= '9') {
				s = "_" + s;
			}

			for (int i = 0; i < GetSize(s); i++) {
				if ('0' <= s[i] && s[i] <= '9') continue;
				if ('A' <= s[i] && s[i] <= 'Z') continue;
				if ('a' <= s[i] && s[i] <= 'z') continue;
				s[i] = '_';
			}

			while (reserved_cids.count(s))
				s += "_";

			reserved_cids.insert(s);
			id2cid[id] = s;
		}

		return id2cid.at(id);
	}

	void create_module_struct(Module *mod)
	{
		if (generated_structs.count(mod->name))
			return;

		generated_structs.insert(mod->name);
		sigmaps[mod].set(mod);

		for (Wire *w : mod->wires())
		{
			if (w->port_output)
				for (auto bit : SigSpec(w))
					bit2output[mod][sigmaps.at(mod)(bit)].insert(bit);
		}

		for (Cell *c : mod->cells())
		{
			for (auto &conn : c->connections())
			{
				if (!c->input(conn.first))
					continue;

				int idx = 0;
				for (auto bit : sigmaps.at(mod)(conn.second))
					bit2cell[mod][bit].insert(tuple<Cell*, IdString, int>(c, conn.first, idx++));
			}

			if (design->module(c->type))
				create_module_struct(design->module(c->type));
		}

		TopoSort<IdString> topo;

		for (Cell *c : mod->cells())
		{
			topo.node(c->name);

			for (auto &conn : c->connections())
			{
				if (!c->input(conn.first))
					continue;

				for (auto bit : sigmaps.at(mod)(conn.second))
				for (auto &it : bit2cell[mod][bit])
					topo.edge(c->name, std::get<0>(it)->name);
			}
		}

		topo.analyze_loops = false;
		topo.sort();

		for (int i = 0; i < GetSize(topo.sorted); i++)
			topoidx[mod->cell(topo.sorted[i])] = i;

		struct_declarations.push_back("");
		struct_declarations.push_back(stringf("struct %s_state_t", cid(mod->name).c_str()));
		struct_declarations.push_back("{");

		struct_declarations.push_back("  // Input Ports");
		for (Wire *w : mod->wires())
			if (w->port_input)
				struct_declarations.push_back(stringf("  %s %s; // %s", sigtype(w->width).c_str(), cid(w->name).c_str(), log_id(w)));

		struct_declarations.push_back("");
		struct_declarations.push_back("  // Output Ports");
		for (Wire *w : mod->wires())
			if (!w->port_input && w->port_output)
				struct_declarations.push_back(stringf("  %s %s; // %s", sigtype(w->width).c_str(), cid(w->name).c_str(), log_id(w)));

		struct_declarations.push_back("");
		struct_declarations.push_back("  // Internal Wires");
		for (Wire *w : mod->wires())
			if (!w->port_input && !w->port_output)
				struct_declarations.push_back(stringf("  %s %s; // %s", sigtype(w->width).c_str(), cid(w->name).c_str(), log_id(w)));

		for (Cell *c : mod->cells())
			if (design->module(c->type))
				struct_declarations.push_back(stringf("  struct %s_state_t %s; // %s", cid(c->type).c_str(), cid(c->name).c_str(), log_id(c)));

		struct_declarations.push_back(stringf("};"));
	}

	void eval_cell(HierDirtyFlags *work, const string &prefix, const string &/* log_prefix */, Cell *cell)
	{
		if (cell->type.in("$_BUF_", "$_NOT_"))
		{
			SigBit a = sigmaps.at(work->module)(cell->getPort("\\A"));
			SigBit y = sigmaps.at(work->module)(cell->getPort("\\Y"));

			string a_expr = a.wire ? stringf("%s(&%s)", util_get_bit(a.wire->width, a.offset).c_str(), (prefix + cid(a.wire->name)).c_str()) : a.data ? "1" : "0";
			string expr;

			if (cell->type == "$_BUF_")  expr = a_expr;
			if (cell->type == "$_NOT_")  expr = "!" + a_expr;

			log_assert(y.wire);
			funct_declarations.push_back(stringf("  %s(&%s, %s); // %s (%s)", util_set_bit(y.wire->width, y.offset).c_str(),
					(prefix + cid(y.wire->name)).c_str(), expr.c_str(), log_id(cell), log_id(cell->type)));

			work->set_dirty(y);
			return;
		}

		if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_"))
		{
			SigBit a = sigmaps.at(work->module)(cell->getPort("\\A"));
			SigBit b = sigmaps.at(work->module)(cell->getPort("\\B"));
			SigBit y = sigmaps.at(work->module)(cell->getPort("\\Y"));

			string a_expr = a.wire ? stringf("%s(&%s)", util_get_bit(a.wire->width, a.offset).c_str(), (prefix + cid(a.wire->name)).c_str()) : a.data ? "1" : "0";
			string b_expr = b.wire ? stringf("%s(&%s)", util_get_bit(b.wire->width, b.offset).c_str(), (prefix + cid(b.wire->name)).c_str()) : b.data ? "1" : "0";
			string expr;

			if (cell->type == "$_AND_")  expr = stringf("%s & %s",    a_expr.c_str(), b_expr.c_str());
			if (cell->type == "$_NAND_") expr = stringf("!(%s & %s)", a_expr.c_str(), b_expr.c_str());
			if (cell->type == "$_OR_")   expr = stringf("%s | %s",    a_expr.c_str(), b_expr.c_str());
			if (cell->type == "$_NOR_")  expr = stringf("!(%s | %s)", a_expr.c_str(), b_expr.c_str());
			if (cell->type == "$_XOR_")  expr = stringf("%s ^ %s",    a_expr.c_str(), b_expr.c_str());
			if (cell->type == "$_XNOR_") expr = stringf("!(%s ^ %s)", a_expr.c_str(), b_expr.c_str());

			log_assert(y.wire);
			funct_declarations.push_back(stringf("  %s(&%s, %s); // %s (%s)", util_set_bit(y.wire->width, y.offset).c_str(),
					(prefix + cid(y.wire->name)).c_str(), expr.c_str(), log_id(cell), log_id(cell->type)));

			work->set_dirty(y);
			return;
		}

		if (cell->type.in("$_AOI3_", "$_OAI3_"))
		{
			SigBit a = sigmaps.at(work->module)(cell->getPort("\\A"));
			SigBit b = sigmaps.at(work->module)(cell->getPort("\\B"));
			SigBit c = sigmaps.at(work->module)(cell->getPort("\\C"));
			SigBit y = sigmaps.at(work->module)(cell->getPort("\\Y"));

			string a_expr = a.wire ? stringf("%s(&%s)", util_get_bit(a.wire->width, a.offset).c_str(), (prefix + cid(a.wire->name)).c_str()) : a.data ? "1" : "0";
			string b_expr = b.wire ? stringf("%s(&%s)", util_get_bit(b.wire->width, b.offset).c_str(), (prefix + cid(b.wire->name)).c_str()) : b.data ? "1" : "0";
			string c_expr = c.wire ? stringf("%s(&%s)", util_get_bit(c.wire->width, c.offset).c_str(), (prefix + cid(c.wire->name)).c_str()) : c.data ? "1" : "0";
			string expr;

			if (cell->type == "$_AOI3_") expr = stringf("!((%s & %s) | %s)", a_expr.c_str(), b_expr.c_str(), c_expr.c_str());
			if (cell->type == "$_OAI3_") expr = stringf("!((%s | %s) & %s)", a_expr.c_str(), b_expr.c_str(), c_expr.c_str());

			log_assert(y.wire);
			funct_declarations.push_back(stringf("  %s(&%s, %s); // %s (%s)", util_set_bit(y.wire->width, y.offset).c_str(),
					(prefix + cid(y.wire->name)).c_str(), expr.c_str(), log_id(cell), log_id(cell->type)));

			work->set_dirty(y);
			return;
		}

		if (cell->type.in("$_AOI4_", "$_OAI4_"))
		{
			SigBit a = sigmaps.at(work->module)(cell->getPort("\\A"));
			SigBit b = sigmaps.at(work->module)(cell->getPort("\\B"));
			SigBit c = sigmaps.at(work->module)(cell->getPort("\\C"));
			SigBit d = sigmaps.at(work->module)(cell->getPort("\\D"));
			SigBit y = sigmaps.at(work->module)(cell->getPort("\\Y"));

			string a_expr = a.wire ? stringf("%s(&%s)", util_get_bit(a.wire->width, a.offset).c_str(), (prefix + cid(a.wire->name)).c_str()) : a.data ? "1" : "0";
			string b_expr = b.wire ? stringf("%s(&%s)", util_get_bit(b.wire->width, b.offset).c_str(), (prefix + cid(b.wire->name)).c_str()) : b.data ? "1" : "0";
			string c_expr = c.wire ? stringf("%s(&%s)", util_get_bit(c.wire->width, c.offset).c_str(), (prefix + cid(c.wire->name)).c_str()) : c.data ? "1" : "0";
			string d_expr = d.wire ? stringf("%s(&%s)", util_get_bit(d.wire->width, d.offset).c_str(), (prefix + cid(d.wire->name)).c_str()) : d.data ? "1" : "0";
			string expr;

			if (cell->type == "$_AOI4_") expr = stringf("!((%s & %s) | (%s & %s))", a_expr.c_str(), b_expr.c_str(), c_expr.c_str(), d_expr.c_str());
			if (cell->type == "$_OAI4_") expr = stringf("!((%s | %s) & (%s | %s))", a_expr.c_str(), b_expr.c_str(), c_expr.c_str(), d_expr.c_str());

			log_assert(y.wire);
			funct_declarations.push_back(stringf("  %s(&%s, %s); // %s (%s)", util_set_bit(y.wire->width, y.offset).c_str(),
					(prefix + cid(y.wire->name)).c_str(), expr.c_str(), log_id(cell), log_id(cell->type)));

			work->set_dirty(y);
			return;
		}

		if (cell->type == "$_MUX_")
		{
			SigBit a = sigmaps.at(work->module)(cell->getPort("\\A"));
			SigBit b = sigmaps.at(work->module)(cell->getPort("\\B"));
			SigBit s = sigmaps.at(work->module)(cell->getPort("\\S"));
			SigBit y = sigmaps.at(work->module)(cell->getPort("\\Y"));

			string a_expr = a.wire ? stringf("%s(&%s)", util_get_bit(a.wire->width, a.offset).c_str(), (prefix + cid(a.wire->name)).c_str()) : a.data ? "1" : "0";
			string b_expr = b.wire ? stringf("%s(&%s)", util_get_bit(b.wire->width, b.offset).c_str(), (prefix + cid(b.wire->name)).c_str()) : b.data ? "1" : "0";
			string s_expr = s.wire ? stringf("%s(&%s)", util_get_bit(s.wire->width, s.offset).c_str(), (prefix + cid(s.wire->name)).c_str()) : s.data ? "1" : "0";
			string expr = stringf("%s ? %s : %s", s_expr.c_str(), b_expr.c_str(), a_expr.c_str());

			log_assert(y.wire);
			funct_declarations.push_back(stringf("  %s(&%s, %s); // %s (%s)", util_set_bit(y.wire->width, y.offset).c_str(),
					(prefix + cid(y.wire->name)).c_str(), expr.c_str(), log_id(cell), log_id(cell->type)));

			work->set_dirty(y);
			return;
		}

		log_error("No C model for %s available at the moment (FIXME).\n", log_id(cell->type));
	}

	void eval_dirty(HierDirtyFlags *work, const string &prefix, const string &log_prefix, const string &parent_prefix, const string &parent_log_prefix)
	{
		while (work->dirty)
		{
			if (verbose && (!work->dirty_bits.empty() || !work->dirty_cells.empty()))
				log("In %s:\n", log_prefix.c_str());

			while (!work->dirty_bits.empty() || !work->dirty_cells.empty())
			{
				if (!work->dirty_bits.empty())
				{
					SigSpec dirtysig(work->dirty_bits);
					dirtysig.sort_and_unify();

					for (SigChunk chunk : dirtysig.chunks()) {
						if (verbose)
							log("  Propagating %s.%s[%d:%d].\n", log_prefix.c_str(), log_id(chunk.wire), chunk.offset+chunk.width-1, chunk.offset);
						funct_declarations.push_back(stringf("  // Updated signal in %s: %s", log_prefix.c_str(), log_signal(chunk)));
					}

					for (SigBit bit : dirtysig)
					{
						if (bit2output[work->module].count(bit) && work->parent)
							for (auto outbit : bit2output[work->module][bit])
							{
								Module *parent_mod = work->parent->module;
								Cell *parent_cell = parent_mod->cell(work->hiername);

								IdString port_name = outbit.wire->name;
								int port_offset = outbit.offset;
								SigBit parent_bit = sigmaps.at(parent_mod)(parent_cell->getPort(port_name)[port_offset]);

								log_assert(bit.wire && parent_bit.wire);
								funct_declarations.push_back(stringf("  %s(&%s, %s(&%s));",
										util_set_bit(parent_bit.wire->width, parent_bit.offset).c_str(),
										(parent_prefix + cid(parent_bit.wire->name)).c_str(),
										util_get_bit(bit.wire->width, bit.offset).c_str(),
										(prefix + cid(bit.wire->name)).c_str()));
								work->parent->set_dirty(parent_bit);

								if (verbose)
									log("    Propagating %s.%s[%d] -> %s.%s[%d].\n", log_prefix.c_str(), log_id(bit.wire), bit.offset,
											parent_log_prefix.c_str(), log_id(parent_bit.wire), parent_bit.offset);
							}

						for (auto &port : bit2cell[work->module][bit])
						{
							if (work->children.count(std::get<0>(port)->name))
							{
								HierDirtyFlags *child = work->children.at(std::get<0>(port)->name);
								SigBit child_bit = sigmaps.at(child->module)(SigBit(child->module->wire(std::get<1>(port)), std::get<2>(port)));
								log_assert(bit.wire && child_bit.wire);

								funct_declarations.push_back(stringf("  %s(&%s, %s(&%s));",
										util_set_bit(child_bit.wire->width, child_bit.offset).c_str(),
										(prefix + cid(child->hiername) + "." + cid(child_bit.wire->name)).c_str(),
										util_get_bit(bit.wire->width, bit.offset).c_str(),
										(prefix + cid(bit.wire->name)).c_str()));
								child->set_dirty(child_bit);

								if (verbose)
									log("    Propagating %s.%s[%d] -> %s.%s.%s[%d].\n", log_prefix.c_str(), log_id(bit.wire), bit.offset,
											log_prefix.c_str(), log_id(std::get<0>(port)), log_id(child_bit.wire), child_bit.offset);
							} else {
								if (verbose)
									log("    Marking cell %s.%s (via %s.%s[%d]).\n", log_prefix.c_str(), log_id(std::get<0>(port)),
											log_prefix.c_str(), log_id(bit.wire), bit.offset);
								work->set_dirty(std::get<0>(port));
							}
						}
						work->unset_dirty(bit);
					}
				}

				if (!work->dirty_cells.empty())
				{
					Cell *cell = nullptr;
					for (auto c : work->dirty_cells)
						if (cell == nullptr || topoidx.at(cell) < topoidx.at(c))
							cell = c;

					if (verbose)
						log("  Evaluating %s.%s (%s, best of %d).\n", log_prefix.c_str(), log_id(cell), log_id(cell->type), GetSize(work->dirty_cells));
					eval_cell(work, prefix, log_prefix, cell);
					work->unset_dirty(cell);
				}
			}

			for (auto &child : work->children)
				eval_dirty(child.second, prefix + cid(child.first) + ".", log_prefix + "." + cid(child.first), prefix, log_prefix);
		}
	}

	void run(Module *mod)
	{
		create_module_struct(mod);

		dirty_flags = new HierDirtyFlags(mod, IdString(), nullptr);

		funct_declarations.push_back("");
		funct_declarations.push_back(stringf("void %s_init(struct %s_state_t *state)", cid(mod->name).c_str(), cid(mod->name).c_str()));
		funct_declarations.push_back("{");
		funct_declarations.push_back("}");

		funct_declarations.push_back("");
		funct_declarations.push_back(stringf("void %s_eval(struct %s_state_t *state)", cid(mod->name).c_str(), cid(mod->name).c_str()));
		funct_declarations.push_back("{");

		for (Wire *w : mod->wires()) {
			if (w->port_input)
				for (SigBit bit : sigmaps.at(mod)(w))
					dirty_flags->set_dirty(bit);
		}

		eval_dirty(dirty_flags, "state->", log_id(mod), "", "");

		funct_declarations.push_back("}");

		funct_declarations.push_back("");
		funct_declarations.push_back(stringf("void %s_tick(struct %s_state_t *state)", cid(mod->name).c_str(), cid(mod->name).c_str()));
		funct_declarations.push_back("{");
		funct_declarations.push_back("}");

		delete dirty_flags;
		dirty_flags = nullptr;
	}

	void write(std::ostream &f)
	{
		f << "#include <stdint.h>" << std::endl;
		f << "#include <stdbool.h>" << std::endl;

		for (auto &line : signal_declarations)
			f << line << std::endl;

		for (auto &line : util_declarations)
			f << line << std::endl;

		for (auto &line : struct_declarations)
			f << line << std::endl;

		for (auto &line : funct_declarations)
			f << line << std::endl;
	}
};

struct SimplecBackend : public Backend {
	SimplecBackend() : Backend("simplec", "convert design to simple C code") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_simplec [options] [filename]\n");
		log("\n");
		log("Write simple C code for simulating the design. The C code writen can be used to\n");
		log("simulate the design in a C environment, but the purpose of this command is to\n");
		log("generate code that works well with C-based formal verification.\n");
		log("\n");
		log("    -verbose\n");
		log("        this will print the recursive walk used to export the modules.\n");
		log("\n");
		log("    -i8, -i16, -i32, -i64\n");
		log("        set the maximum integer bit width to use in the generated code.\n");
		log("\n");
		log("THIS COMMAND IS UNDER CONSTRUCTION\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		SimplecWorker worker(design);

		log_header(design, "Executing SIMPLEC backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-verbose") {
				worker.verbose = true;
				continue;
			}
			if (args[argidx] == "-i8") {
				worker.max_uintsize = 8;
				continue;
			}
			if (args[argidx] == "-i16") {
				worker.max_uintsize = 16;
				continue;
			}
			if (args[argidx] == "-i32") {
				worker.max_uintsize = 32;
				continue;
			}
			if (args[argidx] == "-i64") {
				worker.max_uintsize = 64;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		Module *topmod = design->top_module();

		if (topmod == nullptr)
			log_error("Current design has no top module.\n");

		worker.run(topmod);
		worker.write(*f);
	}
} SimplecBackend;

PRIVATE_NAMESPACE_END
