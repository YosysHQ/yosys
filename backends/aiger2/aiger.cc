/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C)  Martin Povišer <povik@cutebit.org>
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

// TODOs:
//  - gracefully handling inout ports (an error message probably)
//  - undriven wires
//  - zero-width operands

#include "kernel/register.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define BITWISE_OPS ID($buf), ID($not), ID($mux), ID($and), ID($or), ID($xor), ID($xnor), ID($fa), \
					ID($bwmux)

#define REDUCE_OPS ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)

#define LOGIC_OPS ID($logic_and), ID($logic_or), ID($logic_not)

#define GATE_OPS ID($_BUF_), ID($_NOT_), ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), \
				 ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_), ID($_MUX_), ID($_NMUX_), \
				 ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_)

#define CMP_OPS ID($eq), ID($ne), ID($lt), ID($le), ID($ge), ID($gt)

// TODO
//#define ARITH_OPS ID($add), ID($sub), ID($neg)

#define KNOWN_OPS BITWISE_OPS, REDUCE_OPS, LOGIC_OPS, GATE_OPS, ID($pos), CMP_OPS, \
				  ID($pmux), ID($bmux) /*, ARITH_OPS*/

template<typename Writer, typename Lit, Lit CFALSE, Lit CTRUE>
struct Index {
	struct HierCursor;
	struct ModuleInfo {
		Module *module;
		int len;
		dict<Wire *, int> windices;
		dict<Cell *, int> suboffsets;
		pool<Cell *> found_blackboxes;

		bool indexing = false;
		bool indexed = false;
	};

	dict<Module *, ModuleInfo> modules;

	int index_wires(ModuleInfo &info, RTLIL::Module *m)
	{
		int sum = 0;
		for (auto w : m->wires()) {
			info.windices[w] = sum;
			sum += w->width;
		}
		return sum;
	}

	bool flatten = false;
	bool inline_whiteboxes = false;
	bool allow_blackboxes = false;

	int index_module(RTLIL::Module *m)
	{
		ModuleInfo &info = modules[m];

		if (info.indexed)
			return info.len;

		if (info.indexing && !info.indexed)
			log_error("Hierarchy error\n");

		info.module = m;
		int pos = index_wires(info, m);

		for (auto cell : m->cells()) {
			if (cell->type.in(KNOWN_OPS) || cell->type.in(ID($scopeinfo), ID($specify2), ID($specify3)))
				continue;

			Module *submodule = m->design->module(cell->type);

			if (submodule && flatten &&
					!submodule->get_bool_attribute(ID::keep_hierarchy) &&
					!submodule->get_blackbox_attribute(inline_whiteboxes)) {
				info.suboffsets[cell] = pos;
				pos += index_module(submodule);
			} else {
				if (allow_blackboxes) {
					info.found_blackboxes.insert(cell);	
				} else {
					if (!submodule || submodule->get_blackbox_attribute())
						log_error("Unsupported cell type: %s (%s in %s)\n",
								  log_id(cell->type), log_id(cell), log_id(m));
				}
			}
		}

		info.len = pos;
		return info.len;
	}

	Design *design;
	Module *top;
	ModuleInfo *top_minfo;
	std::vector<Lit> lits;

	Index()
	{
	}

	void setup(RTLIL::Module *top)
	{
		design = top->design;
		this->top = top;

		modules.reserve(top->design->modules().size());
		int nlits = index_module(top);
		log_debug("allocating for %d literals\n", nlits);
		lits.resize(nlits, Writer::EMPTY_LIT);
		top_minfo = &modules.at(top);
	}

	bool const_folding = true;
	bool strashing = false;
	dict<std::pair<Lit, Lit>, Lit> cache;

	Lit AND(Lit a, Lit b)
	{
		if (const_folding) {
			if (a == CFALSE || b == CFALSE)
				return CFALSE;
			if (a == CTRUE)
				return b;
			if (b == CTRUE)
				return a;
		}

		if (!strashing) {
			return (static_cast<Writer*>(this))->emit_gate(a, b);
		} else {
			if (a < b) std::swap(a, b);
			auto pair = std::make_pair(a, b);

			if (!cache.count(pair)) {
				Lit nl = (static_cast<Writer*>(this))->emit_gate(a, b);
				cache[pair] = nl;
				return nl;
			} else {
				return cache.at(pair);
			}
		}
	}

	Lit NOT(Lit lit)
	{
		return Writer::negate(lit);
	}

	Lit OR(Lit a, Lit b)
	{
		return NOT(AND(NOT(a), NOT(b)));
	}

	Lit MUX(Lit a, Lit b, Lit s)
	{
		if (const_folding) {
			if (a == b)
				return a;
			if (s == CFALSE)
				return a;
			if (s == CTRUE)
				return b;
		}

		return OR(AND(a, NOT(s)), AND(b, s));
	}

	Lit XOR(Lit a, Lit b)
	{
		return OR(AND(a, NOT(b)), AND(NOT(a), b));
	}

	Lit XNOR(Lit a, Lit b)
	{
		return NOT(OR(AND(a, NOT(b)), AND(NOT(a), b)));
	}

	Lit CARRY(Lit a, Lit b, Lit c)
	{
		if (const_folding) {
			if (c == CTRUE) {
				return OR(a, b);
			} else if (c == CFALSE) {
				return AND(a, b);
			}
		}
		return OR(AND(a, b), AND(c, OR(a, b)));
	}

	Lit REDUCE(std::vector<Lit> lits, bool op_xor=false)
	{
		std::vector<Lit> next;
		while (lits.size() > 1) {
			next.clear();
			for (int i = 0; i < (int) lits.size(); i += 2) {
				if (i + 1 >= (int) lits.size()) {
					next.push_back(lits[i]);
				} else {
					Lit a = lits[i], b = lits[i + 1];
					next.push_back(op_xor ? XOR(a, b) : AND(a, b));
				}
			}
			next.swap(lits);
		}

		if (lits.empty())
			return op_xor ? CFALSE : CTRUE;
		else
			return lits.front();
	}

	Lit impl_op(HierCursor &cursor, Cell *cell, IdString oport, int obit)
	{
		if (cell->type.in(REDUCE_OPS, LOGIC_OPS, CMP_OPS) && obit != 0) {
			return CFALSE;
		} else if (cell->type.in(CMP_OPS)) {
			SigSpec aport = cell->getPort(ID::A);
			bool asigned = cell->getParam(ID::A_SIGNED).as_bool();
			SigSpec bport = cell->getPort(ID::B);
			bool bsigned = cell->getParam(ID::B_SIGNED).as_bool();

			int width = std::max(aport.size(), bport.size()) + 1;
			aport.extend_u0(width, asigned);
			bport.extend_u0(width, bsigned);

			if (cell->type.in(ID($eq), ID($ne))) {
				int carry = CTRUE;
				for (int i = 0; i < width; i++) {
					Lit a = visit(cursor, aport[i]);
					Lit b = visit(cursor, bport[i]);
					carry = AND(carry, XNOR(a, b));
				}
				return (cell->type == ID($eq)) ? carry : /* $ne */ NOT(carry);
			} else if (cell->type.in(ID($lt), ID($le), ID($gt), ID($ge))) {
				if (cell->type.in(ID($gt), ID($ge)))
					std::swap(aport, bport);
				int carry = cell->type.in(ID($le), ID($ge)) ? CFALSE : CTRUE; 
				Lit a, b;
				// TODO: this might not be the most economic structure; revisit at a later date
				for (int i = 0; i < width; i++) {
					a = visit(cursor, aport[i]);
					b = visit(cursor, bport[i]);
					if (i != width - 1)
						carry = CARRY(a, NOT(b), carry);
				}
				return XOR(carry, XNOR(a, b));
			} else {
				log_abort();
			}
		} else if (cell->type.in(REDUCE_OPS, ID($logic_not))) {
			SigSpec inport = cell->getPort(ID::A);

			std::vector<Lit> lits;
			for (int i = 0; i < inport.size(); i++) {
				Lit lit = visit(cursor, inport[i]);
				if (cell->type.in(ID($reduce_and), ID($reduce_xor), ID($reduce_xnor))) {
					lits.push_back(lit);
				} else if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($logic_not))) {
					lits.push_back(NOT(lit));
				} else {
					log_abort();
				}
			}

			Lit acc = REDUCE(lits, cell->type.in(ID($reduce_xor), ID($reduce_xnor)));

			if (!cell->type.in(ID($reduce_xnor), ID($reduce_or), ID($reduce_bool)))
				return acc;
			else
				return NOT(acc);
		} else if (cell->type.in(ID($logic_and), ID($logic_or))) {
			SigSpec aport = cell->getPort(ID::A);
			SigSpec bport = cell->getPort(ID::B);

			log_assert(aport.size() > 0 && bport.size() > 0); // TODO

			Lit a = visit(cursor, aport[0]);
			for (int i = 1; i < aport.size(); i++) {
				Lit l = visit(cursor, aport[i]);
				a = OR(a, l);
			}

			Lit b = visit(cursor, bport[0]);
			for (int i = 1; i < bport.size(); i++) {
				Lit l = visit(cursor, bport[i]);
				b = OR(b, l);
			}

			if (cell->type == ID($logic_and))
				return AND(a, b);
			else if (cell->type == ID($logic_or))
				return OR(a, b);
			else
				log_abort();
		} else if (cell->type.in(BITWISE_OPS, GATE_OPS, ID($pos))) {
			SigSpec aport = cell->getPort(ID::A);
			Lit a;
			if (obit < aport.size()) {
				a = visit(cursor, aport[obit]);
			} else {
				if (cell->getParam(ID::A_SIGNED).as_bool())
					a = visit(cursor, aport.msb());
				else
					a = CFALSE;
			}

			if (cell->type.in(ID($buf), ID($pos), ID($_BUF_))) {
				return a;
			} else if (cell->type.in(ID($not), ID($_NOT_))) {
				return NOT(a);
			} else {
				SigSpec bport = cell->getPort(ID::B);
				Lit b;
				if (obit < bport.size()) {
					b = visit(cursor, bport[obit]);
				} else {
					if (cell->getParam(ID::B_SIGNED).as_bool())
						b = visit(cursor, bport.msb());
					else
						b = CFALSE;
				}

				if (cell->type.in(ID($and), ID($_AND_))) {
					return AND(a, b);
				} else if (cell->type.in(ID($_NAND_))) {
					return NOT(AND(a, b));
				} else if (cell->type.in(ID($or), ID($_OR_))) {
					return OR(a, b);
				} else if (cell->type.in(ID($_NOR_))) {
					return NOT(OR(a, b));
				} else if (cell->type.in(ID($xor), ID($_XOR_))) {
					return XOR(a, b);
				} else if (cell->type.in(ID($xnor), ID($_XNOR_))) {
					return NOT(XOR(a, b));
				} else if (cell->type.in(ID($_ANDNOT_))) {
					return AND(a, NOT(b));
				} else if (cell->type.in(ID($_ORNOT_))) {
					return OR(a, NOT(b));
				} else if (cell->type.in(ID($mux), ID($_MUX_))) {
					Lit s = visit(cursor, cell->getPort(ID::S));
					return MUX(a, b, s);
				} else if (cell->type.in(ID($bwmux))) {
					Lit s = visit(cursor, cell->getPort(ID::S)[obit]);
					return MUX(a, b, s);
				} else if (cell->type.in(ID($_NMUX_))) {
					Lit s = visit(cursor, cell->getPort(ID::S)[obit]);
					return NOT(MUX(a, b, s));
				} else if (cell->type.in(ID($fa))) {
					Lit c = visit(cursor, cell->getPort(ID::C)[obit]);
					Lit ab = XOR(a, b);
					if (oport == ID::Y) {
						return XOR(ab, c);
					} else /* oport == ID::X */ {
						return OR(AND(a, b), AND(c, ab));
					}
				} else if (cell->type.in(ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_))) {
					Lit c, d;

					c = visit(cursor, cell->getPort(ID::C)[obit]);
					if (/* 4 input types */ cell->type.in(ID($_AOI4_), ID($_OAI4_)))
						d = visit(cursor, cell->getPort(ID::D)[obit]);
					else
						d = cell->type == ID($_AOI3_) ? 1 : 0;

					if (/* aoi */ cell->type.in(ID($_AOI3_), ID($_AOI4_)))
						return NOT(OR(AND(a, b), AND(c, d)));
					else
						return NOT(AND(OR(a, b), OR(c, d)));
				} else {
					log_abort();
				}
			}
		} else if (cell->type == ID($pmux)) {
			SigSpec aport = cell->getPort(ID::A);
			SigSpec bport = cell->getPort(ID::B);
			SigSpec sport = cell->getPort(ID::S);
			int width = aport.size();

			Lit a = visit(cursor, aport[obit]);

			std::vector<Lit> bar, sels;
			for (int i = 0; i < sport.size(); i++) {
				Lit s = visit(cursor, sport[i]);
				Lit b = visit(cursor, bport[width * i + obit]);
				bar.push_back(NOT(AND(s, b)));
				sels.push_back(NOT(s));
			}

			return OR(AND(REDUCE(sels), a), NOT(REDUCE(bar)));
		} else if (cell->type == ID($bmux)) {
			SigSpec aport = cell->getPort(ID::A);
			SigSpec sport = cell->getPort(ID::S);
			int width = cell->getParam(ID::WIDTH).as_int();

			std::vector<Lit> data;
			for (int i = obit; i < aport.size(); i += width)
				data.push_back(visit(cursor, aport[i]));

			std::vector<Lit> next;
			for (int i = 0; i < sport.size(); i++) {
				Lit s = visit(cursor, sport[i]);
				next.clear();
				for (int j = 0; j < (int) data.size(); j += 2)
					next.push_back(MUX(data[j], data[j + 1], s));
				data.swap(next);
			}
			log_assert(data.size() == 1);
			return data[0];
		} else {
			log_abort();
		}
	}

	struct HierCursor {
		typedef std::pair<ModuleInfo&, Cell*> Level;
		std::vector<Level> levels;
		int instance_offset = 0;

		HierCursor()
		{
		}

		ModuleInfo &leaf_minfo(Index &index)
		{
			if (levels.empty())
				return *index.top_minfo;
			else
				return levels.back().first;
		}

		Module *leaf_module(Index &index)
		{
			return leaf_minfo(index).module;
		}

		int bitwire_index(Index &index, SigBit bit)
		{
			log_assert(bit.wire != nullptr);
			return instance_offset + leaf_minfo(index).windices[bit.wire] + bit.offset;
		}

		Cell *exit(Index &index)
		{
			log_assert(!levels.empty());
			Cell *instance = levels.back().second;

			levels.pop_back();
			instance_offset -= leaf_minfo(index).suboffsets.at(instance);

			// return the instance we just exited
			return instance;
		}

		Module *enter(Index &index, Cell *cell)
		{
			Design *design = index.design;
			auto &minfo = leaf_minfo(index);
			log_assert(minfo.suboffsets.count(cell));
			Module *def = design->module(cell->type);
			log_assert(def);
			levels.push_back(Level(index.modules.at(def), cell));
			instance_offset += minfo.suboffsets.at(cell);

			// return the module definition we just entered
			return def;
		}

		bool is_top()
		{
			return levels.empty();
		}

		std::string path()
		{
			std::string ret;
			bool first = true;
			for (auto pair : levels) {
				if (!first)
					ret += ".";
				if (!pair.second)
					ret += RTLIL::unescape_id(pair.first.module->name);
				else
					ret += RTLIL::unescape_id(pair.second->name);
				first = false;
			}
			return ret;
		}

		int hash() const
		{
			int hash = 0;
			for (auto pair : levels)
				hash += (uintptr_t) pair.second;
			return hash;
		}

		bool operator==(const HierCursor &other) const
		{
			if (levels.size() != other.levels.size())
				return false;

			for (int i = 0; i < levels.size(); i++)
				if (levels[i].second != other.levels[i].second)
					return false;

			return true;
		}
	};

	bool visit_hook(int, HierCursor&, SigBit)
	{
		return false;
	}

	Lit visit(HierCursor &cursor, SigBit bit)
	{
		if (!bit.wire) {
			if (bit == State::S1)
				return CTRUE;
			else if (bit == State::S0)
				return CFALSE;
			else if (bit == State::Sx)
				return CFALSE;
			else
				log_error("Unhandled state %s\n", log_signal(bit));
		}

		int idx = cursor.bitwire_index(*this, bit);
		if (lits[idx] != Writer::EMPTY_LIT) {
			// literal already assigned
			return lits[idx];
		}

		// provide means for the derived class to override
		// the visit behavior
		if ((static_cast<Writer*>(this))->visit_hook(idx, cursor, bit)) {
			return lits[idx];
		}

		Lit ret;
		if (!bit.wire->port_input) {
			// an output of a cell
			Cell *driver = bit.wire->driverCell();

			if (driver->type.in(KNOWN_OPS)) {
				ret = impl_op(cursor, driver, bit.wire->driverPort(), bit.offset);
			} else {
				Module *def = cursor.enter(*this, driver);
				{
					IdString portname = bit.wire->driverPort();
					Wire *w = def->wire(portname);
					if (!w)
						log_error("Output port %s on instance %s of %s doesn't exist\n",
								  log_id(portname), log_id(driver), log_id(def));
					if (bit.offset >= w->width)
						log_error("Bit position %d of output port %s on instance %s of %s is out of range (port has width %d)\n",
								  bit.offset, log_id(portname), log_id(driver), log_id(def), w->width);
					ret = visit(cursor, SigBit(w, bit.offset));
				}
				cursor.exit(*this);
			}
		} else {
			// a module input: we cannot be the top module, otherwise
			// the branch for pre-existing literals would have been taken
			log_assert(!cursor.is_top());

			// step into the upper module
			Cell *instance = cursor.exit(*this);
			{
				IdString portname = bit.wire->name;
				if (!instance->hasPort(portname))
					log_error("Input port %s on instance %s of %s unconnected\n",
							  log_id(portname), log_id(instance), log_id(instance->type));
				auto &port = instance->getPort(portname);
				if (bit.offset >= port.size())
					log_error("Bit %d of input port %s on instance %s of %s unconnected\n",
							  bit.offset, log_id(portname), log_id(instance), log_id(instance->type));
				ret = visit(cursor, port[bit.offset]);
			}
			cursor.enter(*this, instance);
		}

		lits[idx] = ret;
		return ret;
	}

	Lit &pi_literal(SigBit bit, HierCursor *cursor=nullptr)
	{
		log_assert(bit.wire);

		if (!cursor) {
			log_assert(bit.wire->module == top);
			log_assert(bit.wire->port_input);
			return lits[top_minfo->windices[bit.wire] + bit.offset];
		} else {
			log_assert(bit.wire->module == cursor->leaf_module(*this));
			return lits[cursor->bitwire_index(*this, bit)];
		}
	}

	Lit eval_po(SigBit bit, HierCursor *cursor=nullptr)
	{
		Lit ret;
		if (!cursor) {
			HierCursor cursor_;
			ret = visit(cursor_, bit);
			log_assert(cursor_.is_top());
			log_assert(cursor_.instance_offset == 0);
		} else {
			ret = visit(*cursor, bit);
		}
		return ret;
	}

	void visit_hierarchy(std::function<void(HierCursor&)> f,
						 HierCursor &cursor)
	{
		f(cursor);

		ModuleInfo &minfo = cursor.leaf_minfo(*this);
		for (auto cell : minfo.module->cells()) {
			if (minfo.suboffsets.count(cell)) {
				cursor.enter(*this, cell);
				visit_hierarchy(f, cursor);
				cursor.exit(*this);
			}
		}
	}

	void visit_hierarchy(std::function<void(HierCursor&)> f)
	{
		HierCursor cursor;
		visit_hierarchy(f, cursor);
	}
};

struct AigerWriter : Index<AigerWriter, unsigned int, 0, 1> {
	typedef unsigned int Lit;

	const static Lit CONST_FALSE = 0;
	const static Lit CONST_TRUE = 1;
	const static constexpr Lit EMPTY_LIT = std::numeric_limits<Lit>::max();

	static Lit negate(Lit lit) {
		return lit ^ 1;
	}

	std::ostream *f;
	Lit lit_counter;
	int ninputs, nlatches, noutputs, nands;

	void encode(int delta)
	{
		log_assert(delta >= 0);
		unsigned int x = delta;
		while (x & ~0x7f) {
			f->put((x & 0x7f) | 0x80);
			x = x >> 7;
		}
		f->put(x);
	}

	Lit emit_gate(Lit a, Lit b)
	{
		Lit out = lit_counter;
		nands++;
		lit_counter += 2;

		if (a < b) std::swap(a, b);
		encode(out - a);
		encode(a - b);
		return out;
	}

	void reset_counters()
	{
		lit_counter = 2;
		ninputs = nlatches = noutputs = nands = 0;
	}

	void write_header() {
		log_assert(lit_counter == (Lit) (ninputs + nlatches + nands) * 2 + 2);

		char buf[128];
		snprintf(buf, sizeof(buf) - 1, "aig %08d %08d %08d %08d %08d\n",
				 ninputs + nlatches + nands, ninputs, nlatches, noutputs, nands);
		f->write(buf, strlen(buf));
	}

	void write(std::ostream *f) {
		reset_counters();

		auto file_start = f->tellp();

		// populate inputs
		std::vector<SigBit> inputs;
		for (auto id : top->ports) {
		Wire *w = top->wire(id);
		log_assert(w);
		if (w->port_input)
		for (int i = 0; i < w->width; i++) {
			pi_literal(SigBit(w, i)) = lit_counter;
			inputs.push_back(SigBit(w, i));
			lit_counter += 2;
			ninputs++;
		}
		}

		this->f = f;
		// start with the header
		write_header();
		// insert padding where output literals will go (once known)
		for (auto id : top->ports) {
		Wire *w = top->wire(id);
		log_assert(w);
		if (w->port_output) {
			for (auto bit : SigSpec(w)) {
				(void) bit;
				char buf[16];
				snprintf(buf, sizeof(buf) - 1, "%08d\n", 0);
				f->write(buf, strlen(buf));
				noutputs++;
			}
		}
		}
		auto data_start = f->tellp();

		// now the guts
		std::vector<std::pair<SigBit, int>> outputs;
		for (auto w : top->wires())
		if (w->port_output) {
			for (auto bit : SigSpec(w))
				outputs.push_back({bit, eval_po(bit)});
		}
		auto data_end = f->tellp();

		// revisit header and the list of outputs
		f->seekp(file_start);
		write_header();
		for (auto pair : outputs) {
			char buf[16];
			snprintf(buf, sizeof(buf) - 1, "%08d\n", pair.second);
			f->write(buf, strlen(buf));
		}
		// double check we arrived at the same offset for the
		// main data section
		log_assert(data_start == f->tellp());

		f->seekp(data_end);
		int i = 0;
		for (auto pair : outputs) {
			if (SigSpec(pair.first).is_wire()) {
				char buf[32];
				snprintf(buf, sizeof(buf) - 1, "o%d ", i);
				f->write(buf, strlen(buf));
				std::string name = RTLIL::unescape_id(pair.first.wire->name);
				f->write(name.data(), name.size());
				f->put('\n');
			}
			i++;
		}
		i = 0;
		for (auto bit : inputs) {
			if (SigSpec(bit).is_wire()) {
				char buf[32];
				snprintf(buf, sizeof(buf) - 1, "i%d ", i);
				f->write(buf, strlen(buf));
				std::string name = RTLIL::unescape_id(bit.wire->name);
				f->write(name.data(), name.size());
				f->put('\n');
			}
			i++;
		}
	}
};

struct XAigerAnalysis : Index<XAigerAnalysis, int, 0, 0> {
	const static int CONST_FALSE = 0;
	const static int CONST_TRUE = 0;
	const static constexpr int EMPTY_LIT = -1;

	XAigerAnalysis()
	{
		allow_blackboxes = true;

		// Disable const folding and strashing as literal values are not unique
		const_folding = false;
		strashing = false;
	}

	static int negate(int lit)
	{
		return lit;
	}

	int emit_gate(int a, int b)
	{
		return max(a, b) + 1;
	}

	pool<Cell *> seen;

	bool visit_hook(int idx, HierCursor &cursor, SigBit bit)
	{
		log_assert(cursor.is_top()); // TOOD: fix analyzer to work with hierarchy

		if (bit.wire->port_input)
			return false;

		Cell *driver = bit.wire->driverCell();
		if (!driver->type.isPublic())
			return false;

		Module *mod = design->module(driver->type);
		log_assert(mod);
		if (!mod->has_attribute(ID::abc9_box_id))
			return false;

		int max = 1;
		for (auto wire : mod->wires())
		if (wire->port_input)
		for (int i = 0; i < wire->width; i++) {
			int ilevel = visit(cursor, driver->getPort(wire->name)[i]);
			max = std::max(max, ilevel + 1);
		}
		lits[idx] = max;

		if (!seen.count(driver))
			seen.insert(driver);

		return true;
	}

	void analyze(Module *top)
	{
		setup(top);

		for (auto id : top->ports) {
			Wire *w = top->wire(id);
			log_assert(w);
			if (w->port_input)
			for (int i = 0; i < w->width; i++)
				pi_literal(SigBit(w, i)) = 0;
		}

		HierCursor cursor;
		for (auto box : top_minfo->found_blackboxes) {
			Module *def = design->module(box->type);
			if (!box->type.isPublic() || (def && !def->has_attribute(ID::abc9_box_id)))
			for (auto &conn : box->connections_)
			if (box->output(conn.first))
			for (auto bit : conn.second)
				pi_literal(bit, &cursor) = 0;
		}

		for (auto w : top->wires())
		if (w->port_output) {
			for (auto bit : SigSpec(w))
				(void) eval_po(bit);
		}

		for (auto box : top_minfo->found_blackboxes) {
			Module *def = design->module(box->type);
			if (!box->type.isPublic() || (def && !def->has_attribute(ID::abc9_box_id)))
			for (auto &conn : box->connections_)
			if (box->input(conn.first))
			for (auto bit : conn.second)
				(void) eval_po(bit);
		}
	}
};

struct XAigerWriter : AigerWriter {
	XAigerWriter()
	{
		allow_blackboxes = true;
	}

	bool mapping_prep = false;
	pool<Wire *> keep_wires;
	std::ofstream map_file;

	typedef std::pair<SigBit, HierCursor> HierBit;
	std::vector<HierBit> pos;
	std::vector<HierBit> pis;
	int proper_pos_counter = 0;

	pool<SigBit> driven_by_opaque_box;

	void ensure_pi(SigBit bit, HierCursor cursor={},
				   bool box_port=false)
	{
		Lit &lit = pi_literal(bit, &cursor);
		if (lit == EMPTY_LIT) {
			lit = lit_counter;
			pis.push_back(std::make_pair(bit, cursor));
			lit_counter += 2;
			if (map_file.is_open() && !box_port) {
				log_assert(cursor.is_top()); // TODO
				driven_by_opaque_box.insert(bit);
				map_file << "pi " << pis.size() - 1 << " " << bit.offset
						<< " " << bit.wire->name.c_str() << "\n";
			}
		} else {
			log_assert(!box_port);
		}
	}

	bool is_pi(SigBit bit, HierCursor cursor={})
	{
		return pi_literal(bit, &cursor) != EMPTY_LIT;
	}

	void pad_pi()
	{
		pis.push_back(std::make_pair(RTLIL::Sx, HierCursor{}));
		lit_counter += 2;
	}

	void append_box_ports(Cell *box, HierCursor &cursor, bool inputs)
	{
		for (auto &conn : box->connections_) {
			bool is_input = box->input(conn.first);
			bool is_output = box->output(conn.first);

			if (!(is_input || is_output) || (is_input && is_output))
				log_error("Ambiguous port direction on %s/%s\n",
						  log_id(box->type), log_id(conn.first));

			if (is_input && inputs) {
				int bitp = 0;
				for (auto bit : conn.second) {
					if (!bit.wire) {
						bitp++;
						continue;
					}

					if (map_file.is_open()) {
						log_assert(cursor.is_top());
						map_file << "pseudopo " << proper_pos_counter++ << " " << bitp
							<< " " << box->name.c_str()
							<< " " << conn.first.c_str() << "\n";
					}

					pos.push_back(std::make_pair(bit, cursor));

					if (mapping_prep)
						conn.second[bitp] = RTLIL::Sx;

					bitp++;
				}
			} else if (is_output && !inputs) { 
				for (auto &bit : conn.second) {
					if (!bit.wire || bit.wire->port_input)
						log_error("Bad connection");


					ensure_pi(bit, cursor);
					keep_wires.insert(bit.wire);
				}
			}
		}
	}

	RTLIL::Module *holes_module;

	std::stringstream h_buffer;
	static void write_be32(std::ostream &buffer, uint32_t u32)
	{
		typedef unsigned char uchar;
		unsigned char u32_be[4] = {
			(uchar) (u32 >> 24), (uchar) (u32 >> 16), (uchar) (u32 >> 8), (uchar) u32
		};
		buffer.write((char *) u32_be, sizeof(u32_be));
	}

	void prep_boxes(int pending_pos_num)
	{
		XAigerAnalysis analysis;
		log_debug("preforming analysis on '%s'\n", log_id(top));
		analysis.analyze(top);
		log_debug("analysis on '%s' done\n", log_id(top));

		// boxes which have timing data, maybe a whitebox model
		std::vector<std::tuple<HierCursor, Cell *, Module *>> nonopaque_boxes;
		// boxes which are fully opaque
		std::vector<std::tuple<HierCursor, Cell *, Module *>> opaque_boxes;

		log_debug("found boxes:\n");
		visit_hierarchy([&](HierCursor &cursor) {
			auto &minfo = cursor.leaf_minfo(*this);

			for (auto box : minfo.found_blackboxes) {
				log_debug(" - %s.%s (type %s): ", cursor.path().c_str(),
						  RTLIL::unescape_id(box->name).c_str(),
						  log_id(box->type));

				Module *box_module = design->module(box->type), *box_derived;

				if (box_module && !box->parameters.empty()) {
					// TODO: This is potentially costly even if a cached derivation exists
					box_derived = design->module(box_module->derive(design, box->parameters));
					log_assert(box_derived);
				} else {
					box_derived = box_module;
				}

				if (box_derived && box_derived->has_attribute(ID::abc9_box_id)) {
					// This is an ABC9 box, we have timing data, maybe even a whitebox model
					// These need to go last in the AIGER port list.
					nonopaque_boxes.push_back(std::make_tuple(cursor, box, box_derived));
					log_debug("non-opaque\n");
				} else {
					opaque_boxes.push_back(std::make_tuple(cursor, box, box_derived));
					log_debug("opaque\n");
				}
			}
		});

		for (auto [cursor, box, def] : opaque_boxes)
			append_box_ports(box, cursor, false);

		holes_module = design->addModule(NEW_ID);
		std::vector<RTLIL::Wire *> holes_pis;
		int boxes_ci_num = 0, boxes_co_num = 0;

		int box_seq = 0;

		std::vector<Cell *> boxes_order(analysis.seen.begin(), analysis.seen.end());
		std::reverse(boxes_order.begin(), boxes_order.end());

		nonopaque_boxes.clear();
		for (auto box : boxes_order) {
			HierCursor cursor;
			Module *def = design->module(box->type);
			nonopaque_boxes.push_back(std::make_tuple(cursor, box, def));
		}

		for (auto [cursor, box, def] : nonopaque_boxes) {
			// use `def->name` not `box->type` as we want the derived type
			Cell *holes_wb = holes_module->addCell(NEW_ID, def->name);
			int holes_pi_idx = 0;

			if (map_file.is_open()) {
				log_assert(cursor.is_top());
				map_file << "box " << box_seq << " " << box->name.c_str() << "\n";
			}
			box_seq++;

			for (auto port_id : def->ports) {
				Wire *port = def->wire(port_id);
				log_assert(port);

				SigSpec conn = box->hasPort(port_id) ? box->getPort(port_id) : SigSpec{};

				if (port->port_input && !port->port_output) {
					// primary
					for (int i = 0; i < port->width; i++) {
						SigBit bit;
						if (i < conn.size()) {
							bit = conn[i];
						} else {
							// FIXME: hierarchical path
							log_warning("connection on port %s[%d] of instance %s (type %s) missing, using 1'bx\n",
										log_id(port_id), i, log_id(box), log_id(box->type));
							bit = RTLIL::Sx;
						}

						pos.push_back(std::make_pair(bit, cursor));
					}
					boxes_co_num += port->width;

					if (mapping_prep && !conn.empty())
						box->setPort(port_id, SigSpec(RTLIL::Sx, conn.size()));

					// holes
					SigSpec in_conn;
					for (int i = 0; i < port->width; i++) {
						while (holes_pi_idx >= (int) holes_pis.size()) {
							Wire *w = holes_module->addWire(NEW_ID, 1);
							w->port_input = true;
							holes_module->ports.push_back(w->name);
							holes_pis.push_back(w);
						}
						in_conn.append(holes_pis[i]);
						holes_pi_idx++;
					}
					holes_wb->setPort(port_id, in_conn);
				} else if (port->port_output && !port->port_input) {
					// primary
					for (int i = 0; i < port->width; i++) {
						SigBit bit;
						if (i < conn.size() && conn[i].is_wire()) {
							bit = conn[i];
						} else {
							// FIXME: hierarchical path
							log_warning("connection on port %s[%d] of instance %s (type %s) missing\n",
										log_id(port_id), i, log_id(box), log_id(box->type));
							pad_pi();
							continue;
						}

						ensure_pi(bit, cursor, true);
						keep_wires.insert(bit.wire);
					}
					boxes_ci_num += port->width;

					// holes
					Wire *w = holes_module->addWire(NEW_ID, port->width);
					w->port_output = true;
					holes_module->ports.push_back(w->name);
					holes_wb->setPort(port_id, w);
				} else {
					log_error("Ambiguous port direction on %s/%s\n",
							  log_id(box->type), log_id(port_id));
				}
			}
		}

		for (auto [cursor, box, def] : opaque_boxes)
			append_box_ports(box, cursor, true);

		write_be32(h_buffer, 1);
		write_be32(h_buffer, pis.size());
		log_debug("ciNum = %zu\n", pis.size());
		write_be32(h_buffer, pending_pos_num + pos.size());
		log_debug("coNum = %zu\n", pending_pos_num + pos.size());
		write_be32(h_buffer, pis.size() - boxes_ci_num);
		log_debug("piNum = %zu\n", pis.size() - boxes_ci_num);
		write_be32(h_buffer, pending_pos_num + pos.size() - boxes_co_num);
		log_debug("poNum = %zu\n", pending_pos_num + pos.size() - boxes_co_num);
		write_be32(h_buffer, nonopaque_boxes.size());

		box_seq = 0;
		for (auto [cursor, box, def] : nonopaque_boxes) {
			int box_ci_num = 0, box_co_num = 0;
			for (auto port_id : def->ports) {
				Wire *port = def->wire(port_id);
				log_assert(port);
				if (port->port_input && !port->port_output) {
					box_co_num += port->width;
				} else if (port->port_output && !port->port_input) {
					box_ci_num += port->width;
				} else {
					log_abort();
				}
			}

			write_be32(h_buffer, box_co_num);
			write_be32(h_buffer, box_ci_num);
			write_be32(h_buffer, def->attributes.at(ID::abc9_box_id).as_int());
			write_be32(h_buffer, box_seq++);
		}
	}

	void clear_boxes()
	{
		design->remove(holes_module);
	}

	void write(std::ostream *f) {
		reset_counters();

		for (auto w : top->wires())
		if (w->port_input)
		for (int i = 0; i < w->width; i++)
			ensure_pi(SigBit(w, i));

		int proper_po_num = 0;
		for (auto w : top->wires())
		if (w->port_output)
			proper_po_num += w->width;

		prep_boxes(proper_po_num);
		for (auto w : top->wires())
		if (w->port_output)
		for (int i = 0; i < w->width; i++) {
			if (map_file.is_open() && !driven_by_opaque_box.count(SigBit(w, i))) {
				map_file << "po " << proper_pos_counter++ << " " << i
							<< " " << w->name.c_str() << "\n";
			}
			pos.push_back(std::make_pair(SigBit(w, i), HierCursor{}));
		}

		this->f = f;
		// start with the header
		ninputs = pis.size();
		noutputs = pos.size();
		write_header();
		// insert padding where output literals will go (once known)
		for (auto _ : pos) {
			char buf[16];
			snprintf(buf, sizeof(buf) - 1, "%08d\n", 0);
			f->write(buf, strlen(buf));
		}
		auto data_start = f->tellp();

		// now the guts
		std::vector<Lit> outlits;
		for (auto &pair : pos)
			outlits.push_back(eval_po(pair.first, &pair.second));

		// revisit header and the list of outputs
		f->seekp(0);
		ninputs = pis.size();
		noutputs = pos.size();
		write_header();
		for (auto lit : outlits) {
			char buf[16];
			snprintf(buf, sizeof(buf) - 1, "%08d\n", lit);
			f->write(buf, strlen(buf));
		}
		// double check we arrived at the same offset for the
		// main data section
		log_assert(data_start == f->tellp());

		// extensions
		f->seekp(0, std::ios::end);

		f->put('c');

		// insert empty 'r' and 's' sections (abc crashes if we provide 'a' without those)
		f->put('r');
		write_be32(*f, 4);
		write_be32(*f, 0);
		f->put('s');
		write_be32(*f, 4);
		write_be32(*f, 0);

		f->put('h');
		// TODO: get rid of std::string copy
		std::string h_buffer_str = h_buffer.str();
		write_be32(*f, h_buffer_str.size());
		f->write(h_buffer_str.data(), h_buffer_str.size());

#if 1
		f->put('a');
		write_be32(*f, 0); // size to be filled later
		auto holes_aiger_start = f->tellp();
		{
			AigerWriter holes_writer;
			holes_writer.flatten = true;
			holes_writer.inline_whiteboxes = true;
			holes_writer.setup(holes_module);
			holes_writer.write(f);
		}
		auto holes_aiger_size = f->tellp() - holes_aiger_start;
		f->seekp(holes_aiger_start, std::ios::beg);
		f->seekp(-4, std::ios::cur);
		write_be32(*f, holes_aiger_size);
#endif
		f->seekp(0, std::ios::end);

		if (mapping_prep) {
			std::vector<Cell *> to_remove_cells;
			for (auto cell : top->cells())
				if (!top_minfo->found_blackboxes.count(cell))
					to_remove_cells.push_back(cell);
			for (auto cell : to_remove_cells)
				top->remove(cell);
			pool<Wire *> to_remove;
			for (auto wire : top->wires())
				if (!wire->port_input && !wire->port_output && !keep_wires.count(wire))
					to_remove.insert(wire);
			top->remove(to_remove);
		}

		clear_boxes();
	}
};

struct Aiger2Backend : Backend {
	Aiger2Backend() : Backend("aiger2", "(experimental) write design to AIGER file")
	{
		experimental();
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_aiger2 [options] [filename]\n");
		log("\n");
		log("Write the selected module to an AIGER file.\n");
		log("\n");
		log("    -strash\n");
		log("        perform structural hashing while writing\n");
		log("\n");
		log("    -flatten\n");
        log("        allow descending into submodules and write a flattened view of the design\n");
        log("        hierarchy starting at the selected top\n");
        log("\n");
		log("This command is able to ingest all combinational cells except for:\n");
		log("\n");
		pool<IdString> supported = {KNOWN_OPS};
		CellTypes ct;
		ct.setup_internals_eval();
		log("    ");
		int col = 0;
		for (auto pair : ct.cell_types)
		if (!supported.count(pair.first)) {
			if (col + pair.first.size() + 2 > 72) {
				log("\n    ");
				col = 0;
			}
			col += pair.first.size() + 2;
			log("%s, ", log_id(pair.first));
		}
		log("\n");
		log("\n");
		log("And all combinational gates except for:\n");
		log("\n");
		CellTypes ct2;
		ct2.setup_stdcells();
		log("    ");
		col = 0;
		for (auto pair : ct2.cell_types)
		if (!supported.count(pair.first)) {
			if (col + pair.first.size() + 2 > 72) {
				log("\n    ");
				col = 0;
			}
			col += pair.first.size() + 2;
			log("%s, ", log_id(pair.first));
		}
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing AIGER2 backend.\n");

		size_t argidx;
		AigerWriter writer;
		writer.const_folding = true;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strash")
				writer.strashing = true;
			else if (args[argidx] == "-flatten")
				writer.flatten = true;
			else
				break;
		}
		extra_args(f, filename, args, argidx);

		Module *top = design->top_module();

		if (!top || !design->selected_whole_module(top))
			log_cmd_error("No top module selected\n");

		design->bufNormalize(true);
		writer.setup(top);
		writer.write(f);

		// we are leaving the sacred land, un-bufnormalize
		// (if not, this will lead to bugs: the buf-normalized
		// flag must not be kept on past the code that can work
		// with it)
		design->bufNormalize(false);
	}
} Aiger2Backend;

struct XAiger2Backend : Backend {
	XAiger2Backend() : Backend("xaiger2", "(experimental) write module to XAIGER file")
	{
		experimental();
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_xaiger2 [options] [filename]\n");
		log("\n");
		log("Write the selected module to a XAIGER file including the 'h' and 'a' extensions\n");
		log("with box information for ABC.\n");
		log("\n");
		log("    -strash\n");
		log("        perform structural hashing while writing\n");
		log("\n");
		log("    -flatten\n");
        log("        allow descending into submodules and write a flattened view of the design\n");
        log("        hierarchy starting at the selected top\n");
        log("\n");
        log("    -mapping_prep\n");
        log("        after the file is written, prepare the module for reintegration of\n");
        log("        a mapping in a subsequent command. all cells which are not blackboxed nor\n");
        log("        whiteboxed are removed from the design as well as all wires which only\n");
        log("        connect to removed cells\n");
        log("        (conflicts with -flatten)\n");
        log("\n");
        log("    -map2 <file>\n");
        log("        write a map2 file which 'read_xaiger2 -sc_mapping' can read to\n");
        log("        reintegrate a mapping\n");
        log("        (conflicts with -flatten)\n");
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing XAIGER2 backend.\n");

		size_t argidx;
		XAigerWriter writer;
		std::string map_filename;
		writer.const_folding = true;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strash")
				writer.strashing = true;
			else if (args[argidx] == "-flatten")
				writer.flatten = true;
			else if (args[argidx] == "-mapping_prep")
				writer.mapping_prep = true;
			else if (args[argidx] == "-map2" && argidx + 1 < args.size())
				map_filename = args[++argidx];
			else
				break;
		}
		extra_args(f, filename, args, argidx);

		Module *top = design->top_module();

		if (!top || !design->selected_whole_module(top))
			log_cmd_error("No top module selected\n");

		if (!map_filename.empty()) {
			writer.map_file.open(map_filename);
			if (!writer.map_file)
				log_cmd_error("Failed to open '%s' for writing\n", map_filename.c_str());
		}

		design->bufNormalize(true);
		writer.setup(top);
		writer.write(f);

		// we are leaving the sacred land, un-bufnormalize
		// (if not, this will lead to bugs: the buf-normalized
		// flag must not be kept on past the code that can work
		// with it)
		design->bufNormalize(false);
	}
} XAiger2Backend;

PRIVATE_NAMESPACE_END
