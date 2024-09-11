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

#include "kernel/register.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define BITWISE_OPS ID($buf), ID($not), ID($mux), ID($and), ID($or), ID($xor), ID($xnor), ID($fa)

#define REDUCE_OPS ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)

#define LOGIC_OPS ID($logic_and), ID($logic_or), ID($logic_not)

#define GATE_OPS ID($_BUF_), ID($_NOT_), ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), \
				 ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_), ID($_MUX_), ID($_NMUX_), \
				 ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_)

// TODO
//#define ARITH_OPS ID($add), ID($sub), ID($lt), ID($le), ID($ge), ID($gt), ID($neg)

#define KNOWN_OPS BITWISE_OPS, REDUCE_OPS, LOGIC_OPS, GATE_OPS, ID($pos) /*, ARITH_OPS*/

template<typename Writer, typename Lit>
struct Index {
	struct HierCursor;
	struct ModuleInfo {
		Module *module;
		int len;
		dict<Wire *, int> windices;
		dict<Cell *, int> suboffsets;

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
			if (cell->type.in(KNOWN_OPS))
				continue;

			Module *submodule = m->design->module(cell->type);
			if (!submodule || submodule->get_blackbox_attribute())
				log_error("Unsupported cell type: %s (%s in %s)\n",
						  log_id(cell->type), log_id(cell), log_id(m));
			info.suboffsets[cell] = pos;
			pos += index_module(submodule);
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
		lits.resize(nlits, Writer::empty_lit());
		top_minfo = &modules.at(top);
	}

	bool const_folding = true;
	bool strashing = false;
	dict<std::pair<int, int>, int> cache;

	Lit AND(Lit a, Lit b)
	{
		if (const_folding) {
			if (a == Writer::CONST_FALSE || b == Writer::CONST_FALSE)
				return Writer::CONST_FALSE;
			if (a == Writer::CONST_TRUE)
				return b;
			if (b == Writer::CONST_TRUE)
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
			if (s == Writer::CONST_FALSE)
				return a;
			if (s == Writer::CONST_TRUE)
				return b;
		}

		return OR(AND(a, NOT(s)), AND(b, s));
	}

	Lit XOR(Lit a, Lit b)
	{
		return OR(AND(a, NOT(b)), AND(NOT(a), b));
	}

	Lit impl_op(HierCursor &cursor, Cell *cell, IdString oport, int obit)
	{
		if (cell->type.in(REDUCE_OPS, LOGIC_OPS) && obit != 0) {
			return Writer::CONST_FALSE;
		} else if (cell->type.in(REDUCE_OPS, ID($logic_not))) {
			SigSpec inport = cell->getPort(ID::A);

			log_assert(inport.size() > 0); // TODO

			Lit acc = visit(cursor, inport[0]);
			for (int i = 1; i < inport.size(); i++) {
				Lit l = visit(cursor, inport[i]);
				if (cell->type == ID($reduce_and)) {
					acc = AND(acc, l);
				} else if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($logic_not))) {
					acc = OR(acc, l);
				} else if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
					acc = XOR(acc, l);
				}
			}

			if (!cell->type.in(ID($reduce_xnor), ID($logic_not)))
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
					a = Writer::CONST_FALSE;
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
						b = Writer::CONST_FALSE;
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
		} else {
			log_abort();
		}
	}

	struct HierCursor {
		typedef std::pair<ModuleInfo&, Cell*> Level;
		std::vector<Level> levels;
		int instance_offset = 0;

		HierCursor(ModuleInfo &top)
		{
			levels.push_back(Level(top, nullptr));	
		}

		ModuleInfo &current_minfo()
		{
			log_assert(!levels.empty());
			return levels.back().first;
		}

		int bitwire_index(SigBit bit)
		{
			log_assert(bit.wire != nullptr);
			return instance_offset + current_minfo().windices[bit.wire] + bit.offset;
		}

		Cell *exit()
		{
			log_assert(levels.size() > 1);
			Cell *instance = levels.back().second;

			levels.pop_back();
			instance_offset -= current_minfo().suboffsets.at(instance);

			// return the instance we just exited
			return instance;
		}

		Module *enter(Index &index, Cell *cell)
		{
			Design *design = index.design;
			auto &minfo = current_minfo();
			log_assert(minfo.suboffsets.count(cell));
			Module *def = design->module(cell->type);
			log_assert(def);
			levels.push_back(Level(index.modules.at(def), cell));
			instance_offset += minfo.suboffsets.at(cell);

			// return the module definition we just entered
			return def;
		}
	};

	int visit(HierCursor &cursor, SigBit bit)
	{
		if (!bit.wire) {
			if (bit == State::S1)
				return Writer::CONST_TRUE;
			else if (bit == State::S0)
				return Writer::CONST_FALSE;
			else
				log_error("Unhandled state %s\n", log_signal(bit));
		}

		int idx = cursor.bitwire_index(bit);
		if (lits[idx] != Writer::empty_lit()) {
			// literal already assigned
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
				cursor.exit();
			}
			
		} else {
			// a module input: we cannot be the top module, otherwise
			// the branch for pre-existing literals would have been taken
			log_assert(cursor.levels.size() > 1);

			// step into the upper module
			Cell *instance = cursor.exit();
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

	void set_top_port(SigBit bit, Lit lit)
	{
		log_assert(bit.wire);
		log_assert(bit.wire->module == top);
		log_assert(bit.wire->port_input);

		lits[top_minfo->windices[bit.wire] + bit.offset] = lit;
	}

	Lit get_top_port(SigBit bit)
	{
		HierCursor cursor(*top_minfo);
		Lit ret = visit(cursor, bit);
		log_assert(cursor.levels.size() == 1);
		log_assert(cursor.instance_offset == 0);
		return ret;
	}
};

struct AigerWriter : Index<AigerWriter, unsigned int> {
	typedef unsigned int Lit;

	const static Lit CONST_FALSE = 0;
	const static Lit CONST_TRUE = 1;

	// for some reason having a 'const static int EMPTY_LIT'
	// led to linkage errors
	static Lit empty_lit()
	{
		return 0x80000000;
	}

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
		log_assert(lit_counter == (ninputs + nlatches + nands) * 2 + 2);

		char buf[128];
		snprintf(buf, sizeof(buf) - 1, "aig %08d %08d %08d %08d %08d\n",
				 ninputs + nlatches + nands, ninputs, nlatches, noutputs, nands);
		f->seekp(0);
		f->write(buf, strlen(buf));
	}

	void write(std::ostream *f) {
		reset_counters();

		// populate inputs
		std::vector<SigBit> inputs;
		for (auto w : top->wires())
		if (w->port_input)
		for (int i = 0; i < w->width; i++) {
			set_top_port(SigBit(w, i), lit_counter);
			inputs.push_back(SigBit(w, i));
			lit_counter += 2;
			ninputs++;
		}

		this->f = f;
		// start with the header
		write_header();
		// insert padding where output literals will go (once known)
		for (auto w : top->wires())
		if (w->port_output) {
			for (auto bit : SigSpec(w)) {
				(void) bit;
				char buf[16];
				snprintf(buf, sizeof(buf) - 1, "%08d\n", 0);
				f->write(buf, strlen(buf));
				noutputs++;
			}
		}
		auto data_start = f->tellp();

		// now the guts
		std::vector<std::pair<SigBit, int>> outputs;
		for (auto w : top->wires())
		if (w->port_output) {
			for (auto bit : SigSpec(w))
				outputs.push_back({bit, get_top_port(bit)});
		}
		auto data_end = f->tellp();

		// revisit header and the list of outputs
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

struct Aiger2Backend : Backend {
	Aiger2Backend() : Backend("aiger2", "write design to AIGER file (new)")
	{
		experimental();
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing AIGER2 backend.\n");

		size_t argidx;
		AigerWriter writer;
		writer.const_folding = true;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strash")
				writer.strashing = true;
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

struct AIGCounter : Index<AIGCounter, int> {
	typedef int Lit;
	const static Lit CONST_FALSE = -1;
	const static Lit CONST_TRUE = 1;
	static Lit empty_lit() { return 0; }
	static Lit negate(Lit lit) { return -lit; }
	int nvars = 1;
	int ngates = 0;

	Lit emit_gate([[maybe_unused]] Lit a, [[maybe_unused]] Lit b)
	{
		ngates++;
		return ++nvars;
	}

	void count() {
		// populate inputs
		for (auto w : top->wires())
		if (w->port_input)
		for (int i = 0; i < w->width; i++)
			set_top_port(SigBit(w, i), ++nvars);

		for (auto w : top->wires())
		if (w->port_output) {
			for (auto bit : SigSpec(w))
				(void) get_top_port(bit);
		}
	}
};

struct AigsizePass : Pass {
	AigsizePass() : Pass("aigsize", "estimate AIG size for design") {}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing AIGSIZE pass. (size design AIG)\n");

		size_t argidx;
		AIGCounter counter;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strash")
				counter.strashing = true;
			else
				break;
		}
		extra_args(args, argidx, design);

		Module *top = design->top_module();

		if (!top || !design->selected_whole_module(top))
			log_cmd_error("No top module selected\n");

		design->bufNormalize(true);
		counter.setup(top);
		counter.count();
		log("Counted %d gates\n", counter.ngates);

		// we are leaving the sacred land, un-bufnormalize
		// (if not, this will lead to bugs: the buf-normalized
		// flag must not be kept on past the code that can work
		// with it)
		design->bufNormalize(false);
	}
} AigsizePass;

PRIVATE_NAMESPACE_END
