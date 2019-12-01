/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  whitequark <whitequark@whitequark.org>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CxxrtlWorker {
	std::ostream &f;
	std::string indent;
	int temporary = 0;

	dict<const RTLIL::Module*, SigMap> sigmaps;
	pool<const RTLIL::Wire*> sync_wires;
	dict<RTLIL::SigBit, RTLIL::SyncType> sync_types;
	pool<const RTLIL::Memory*> writable_memories;

	CxxrtlWorker(std::ostream &f) : f(f) {}

	void inc_indent() {
		indent += "\t";
	}
	void dec_indent() {
		indent.resize(indent.size() - 1);
	}

	// RTLIL allows any characters in names other than whitespace. This presents an issue for generating C++ code
	// because C++ identifiers may be only alphanumeric, cannot clash with C++ keywords, and cannot clash with cxxrtl
	// identifiers. This issue can be solved with a name mangling scheme. We choose a name mangling scheme that results
	// in readable identifiers, does not depend on an up-to-date list of C++ keywords, and is easy to apply. Its rules:
	//  1. All generated identifiers start with `_`.
	//  1a. Generated identifiers for public names (beginning with `\`) start with `p_`.
	//  1b. Generated identifiers for internal names (beginning with `$`) start with `i_`.
	//  2. An underscore is escaped with another underscore, i.e. `__`.
	//  3. Any other non-alnum character is escaped with underscores around its lowercase hex code, e.g. `@` as `_40_`.
	std::string mangle_name(const RTLIL::IdString &name)
	{
		std::string mangled;
		bool first = true;
		for (char c : name.str()) {
			if (first) {
				first = false;
				if (c == '\\')
					mangled += "p_";
				else if (c == '$')
					mangled += "i_";
				else
					log_assert(false);
			} else {
				if (isalnum(c)) {
					mangled += c;
				} else if (c == '_') {
					mangled += "__";
				} else {
					char l = c & 0xf, h = (c >> 4) & 0xf;
					mangled += '_';
					mangled += (h < 10 ? '0' + h : 'a' + h - 10);
					mangled += (l < 10 ? '0' + l : 'a' + l - 10);
					mangled += '_';
				}
			}
		}
		return mangled;
	}

	std::string mangle_module_name(const RTLIL::IdString &name)
	{
		// Class namespace.
		return mangle_name(name);
	}

	std::string mangle_memory_name(const RTLIL::IdString &name)
	{
		// Class member namespace.
		return "memory_" + mangle_name(name);
	}

	std::string mangle_wire_name(const RTLIL::IdString &name)
	{
		// Class member namespace.
		return mangle_name(name);
	}

	std::string mangle(const RTLIL::Module *module)
	{
		return mangle_module_name(module->name);
	}

	std::string mangle(const RTLIL::Memory *memory)
	{
		return mangle_memory_name(memory->name);
	}

	std::string mangle(const RTLIL::Wire *wire)
	{
		return mangle_wire_name(wire->name);
	}

	std::string mangle(RTLIL::SigBit sigbit)
	{
		log_assert(sigbit.wire != NULL);
		if (sigbit.wire->width == 1)
			return mangle(sigbit.wire);
		return mangle(sigbit.wire) + "_" + std::to_string(sigbit.offset);
	}

	std::string fresh_temporary()
	{
		return stringf("tmp_%d", temporary++);
	}

	void dump_attrs(const RTLIL::AttrObject *object)
	{
		for (auto attr : object->attributes) {
			f << indent << "// " << attr.first.str() << ": ";
			if (attr.second.flags & RTLIL::CONST_FLAG_STRING) {
				f << attr.second.decode_string();
			} else {
				f << attr.second.as_int(/*is_signed=*/attr.second.flags & RTLIL::CONST_FLAG_SIGNED);
			}
			f << "\n";
		}
	}

	void dump_const_init(const RTLIL::Const &data, int width, int offset = 0, bool fixed_width = false)
	{
		f << "{";
		while (width > 0) {
			const int CHUNK_SIZE = 32;
			uint32_t chunk = data.extract(offset, width > CHUNK_SIZE ? CHUNK_SIZE : width).as_int();
			if (fixed_width)
				f << stringf("0x%08xu", chunk);
			else
				f << stringf("%#xu", chunk);
			if (width > CHUNK_SIZE)
				f << ',';
			offset += CHUNK_SIZE;
			width  -= CHUNK_SIZE;
		}
		f << "}";
	}

	void dump_const_init(const RTLIL::Const &data)
	{
		dump_const_init(data, data.size());
	}

	void dump_const(const RTLIL::Const &data, int width, int offset = 0, bool fixed_width = false)
	{
		f << "value<" << width << ">";
		dump_const_init(data, width, offset, fixed_width);
	}

	void dump_const(const RTLIL::Const &data)
	{
		dump_const(data, data.size());
	}

	bool dump_sigchunk(const RTLIL::SigChunk &chunk, bool is_lhs)
	{
		if (chunk.wire == NULL) {
			dump_const(chunk.data, chunk.width, chunk.offset);
			return false;
		} else {
			f << mangle(chunk.wire) << (is_lhs ? ".next" : ".curr");
			if (chunk.width == chunk.wire->width && chunk.offset == 0)
				return false;
			else if (chunk.width == 1)
				f << ".slice<" << chunk.offset << ">()";
			else
				f << ".slice<" << chunk.offset+chunk.width-1 << "," << chunk.offset << ">()";
			return true;
		}
	}

	bool dump_sigspec(const RTLIL::SigSpec &sig, bool is_lhs)
	{
		if (sig.empty()) {
			f << "value<0>()";
			return false;
		} else if (sig.is_chunk()) {
			return dump_sigchunk(sig.as_chunk(), is_lhs);
		} else {
			dump_sigchunk(*sig.chunks().rbegin(), is_lhs);
			for (auto it = sig.chunks().rbegin() + 1; it != sig.chunks().rend(); ++it) {
				f << ".concat(";
				dump_sigchunk(*it, is_lhs);
				f << ")";
			}
			return true;
		}
	}

	void dump_sigspec_lhs(const RTLIL::SigSpec &sig)
	{
		dump_sigspec(sig, /*is_lhs=*/true);
	}

	void dump_sigspec_rhs(const RTLIL::SigSpec &sig)
	{
		// In the contexts where we want template argument deduction to occur for `template<size_t Bits> ... value<Bits>`,
		// it is necessary to have the argument to already be a `value<N>`, since template argument deduction and implicit
		// type conversion are mutually exclusive. In these contexts, we use dump_sigspec_rhs() to emit an explicit
		// type conversion, but only if the expression needs it.
		bool is_complex = dump_sigspec(sig, /*is_lhs=*/false);
		if (is_complex)
			f << ".val()";
	}

	void dump_assign(const RTLIL::SigSig &sigsig)
	{
		f << indent;
		dump_sigspec_lhs(sigsig.first);
		f << " = ";
		dump_sigspec_rhs(sigsig.second);
		f << ";\n";
	}

	void dump_cell(const RTLIL::Cell *cell)
	{
		dump_attrs(cell);
		f << indent << "// cell " << cell->name.str() << "\n";
		// Unary cells
		if (cell->type.in(
		    ID($not), ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
		    ID($pos), ID($neg))) {
			f << indent;
			dump_sigspec_lhs(cell->getPort(ID(Y)));
			f << " = " << cell->type.substr(1) << '_' <<
			     (cell->getParam(ID(A_SIGNED)).as_bool() ? 's' : 'u') <<
			     "<" << cell->getParam(ID(Y_WIDTH)).as_int() << ">(";
			dump_sigspec_rhs(cell->getPort(ID(A)));
			f << ");\n";
		// Binary cells
		} else if (cell->type.in(
		    ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or),
		    ID($shl), ID($sshl), ID($shr), ID($sshr), ID($shift), ID($shiftx),
		    ID($eq), ID($ne), ID($eqx), ID($nex), ID($gt), ID($ge), ID($lt), ID($le),
		    ID($add), ID($sub), ID($mul), ID($div), ID($mod))) {
			f << indent;
			dump_sigspec_lhs(cell->getPort(ID(Y)));
			f << " = " << cell->type.substr(1) << '_' <<
			     (cell->getParam(ID(A_SIGNED)).as_bool() ? 's' : 'u') <<
			     (cell->getParam(ID(B_SIGNED)).as_bool() ? 's' : 'u') <<
			     "<" << cell->getParam(ID(Y_WIDTH)).as_int() << ">(";
			dump_sigspec_rhs(cell->getPort(ID(A)));
			f << ", ";
			dump_sigspec_rhs(cell->getPort(ID(B)));
			f << ");\n";
		// Muxes
		} else if (cell->type == ID($mux)) {
			f << indent;
			dump_sigspec_lhs(cell->getPort(ID(Y)));
			f << " = ";
			dump_sigspec_rhs(cell->getPort(ID(S)));
			f << " ? ";
			dump_sigspec_rhs(cell->getPort(ID(B)));
			f << " : ";
			dump_sigspec_rhs(cell->getPort(ID(A)));
			f << ";\n";
		// Parallel (one-hot) muxes
		} else if (cell->type == ID($pmux)) {
			int width = cell->getParam(ID(WIDTH)).as_int();
			int s_width = cell->getParam(ID(S_WIDTH)).as_int();
			bool first = true;
			for (int part = 0; part < s_width; part++) {
				f << (first ? indent : " else ");
				first = false;
				f << "if (";
				dump_sigspec_rhs(cell->getPort(ID(S)).extract(part));
				f << ") {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID(Y)));
					f << " = ";
					dump_sigspec_rhs(cell->getPort(ID(B)).extract(part * width, width));
					f << ";\n";
				dec_indent();
				f << indent << "}";
			}
			f << " else {\n";
			inc_indent();
				f << indent;
				dump_sigspec_lhs(cell->getPort(ID(Y)));
				f << " = ";
				dump_sigspec_rhs(cell->getPort(ID(A)));
				f << ";\n";
			dec_indent();
			f << indent << "}\n";
		// Flip-flops
		} else if (cell->type.in(ID($dff), ID($dffe), ID($adff), ID($dffsr))) {
			if (cell->getPort(ID(CLK)).is_wire()) {
				// Edge-sensitive logic
				RTLIL::SigBit clk_bit = cell->getPort(ID(CLK))[0];
				clk_bit = sigmaps[clk_bit.wire->module](clk_bit);
				f << indent << "if (" << (cell->getParam(ID(CLK_POLARITY)).as_bool() ? "posedge_" : "negedge_")
				            << mangle(clk_bit) << ") {\n";
				inc_indent();
					if (cell->type == ID($dffe)) {
						f << indent << "if (";
						dump_sigspec_rhs(cell->getPort(ID(EN)));
						f << " == value<1> {" << cell->getParam(ID(EN_POLARITY)).as_bool() << "}) {\n";
						inc_indent();
					}
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID(Q)));
					f << " = ";
					dump_sigspec_rhs(cell->getPort(ID(D)));
					f << ";\n";
					if (cell->type == ID($dffe)) {
						dec_indent();
						f << indent << "}\n";
					}
				dec_indent();
				f << indent << "}\n";
			}
			// Level-sensitive logic
			if (cell->type == ID($adff)) {
				f << indent << "if (";
				dump_sigspec_rhs(cell->getPort(ID(ARST)));
				f << " == value<1> {" << cell->getParam(ID(ARST_POLARITY)).as_bool() << "}) {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID(Q)));
					f << " = ";
					dump_const(cell->getParam(ID(ARST_VALUE)));
					f << ";\n";
				dec_indent();
				f << indent << "}\n";
			} else if (cell->type == ID($dffsr)) {
				f << indent << "if (";
				dump_sigspec_rhs(cell->getPort(ID(CLR)));
				f << " == value<1> {" << cell->getParam(ID(CLR_POLARITY)).as_bool() << "}) {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID(Q)));
					f << " = ";
					dump_const(RTLIL::Const(RTLIL::S0, cell->getParam(ID(WIDTH)).as_int()));
					f << ";\n";
				dec_indent();
				f << indent << "} else if (";
				dump_sigspec_rhs(cell->getPort(ID(SET)));
				f << " == value<1> {" << cell->getParam(ID(SET_POLARITY)).as_bool() << "}) {\n";
				inc_indent();
					f << indent;
					dump_sigspec_lhs(cell->getPort(ID(Q)));
					f << " = ";
					dump_const(RTLIL::Const(RTLIL::S1, cell->getParam(ID(WIDTH)).as_int()));
					f << ";\n";
				dec_indent();
				f << indent << "}\n";
			}
		// Memory ports
		} else if (cell->type.in(ID($memrd), ID($memwr))) {
			if (cell->getParam(ID(CLK_ENABLE)).as_bool()) {
				RTLIL::SigBit clk_bit = cell->getPort(ID(CLK))[0];
				clk_bit = sigmaps[clk_bit.wire->module](clk_bit);
				f << indent << "if (" << (cell->getParam(ID(CLK_POLARITY)).as_bool() ? "posedge_" : "negedge_")
				            << mangle(clk_bit) << ") {\n";
				inc_indent();
			}
			RTLIL::Memory *memory = cell->module->memories[cell->getParam(ID(MEMID)).decode_string()];
			if (cell->type == ID($memrd)) {
				if (!cell->getPort(ID(EN)).is_fully_ones()) {
					f << indent << "if (";
					dump_sigspec_rhs(cell->getPort(ID(EN)));
					f << ") {\n";
					inc_indent();
				}
				f << indent;
				dump_sigspec_lhs(cell->getPort(ID(DATA)));
				f << " = " << mangle(memory) << "[";
				dump_sigspec_rhs(cell->getPort(ID(ADDR)));
				if (writable_memories[memory]) {
					// FIXME: the handling of transparent read ports is a bit naughty: normally, nothing on RHS should ever
					// read from `next`, since this can result in evaluation order nondeterminism, as well as issues with
					// latches. However, for now this is the right tradeoff to make, since it allows to simplify $memrd/$memwr
					// codegen dramatically.
					f << "]." << (cell->getParam(ID(TRANSPARENT)).as_bool() ? "next" : "curr") << ";\n";
				} else {
					f << "];\n";
				}
				if (!cell->getPort(ID(EN)).is_fully_ones()) {
					dec_indent();
					f << indent << "}\n";
				}
			} else /*if (cell->type == ID($memwr))*/ {
				log_assert(writable_memories[memory]);
				// FIXME: handle write port priority.
				int width = cell->getParam(ID(WIDTH)).as_int();
				std::string lhs_temp = fresh_temporary();
				f << indent << "wire<" << width << "> &" << lhs_temp << " = " << mangle(memory) << "[";
				dump_sigspec_rhs(cell->getPort(ID(ADDR)));
				f << "];\n";
				int start = 0;
				RTLIL::SigBit prev_en_bit = RTLIL::Sm;
				for (int stop = 0; stop < width + 1; stop++) {
					if (stop == width || (prev_en_bit != RTLIL::Sm && prev_en_bit != cell->getPort(ID(EN))[stop])) {
						f << indent << "if (";
						dump_sigspec_rhs(prev_en_bit);
						f << ") {\n";
						inc_indent();
							f << indent << lhs_temp << ".next.slice<" << (stop - 1) << "," << start << ">() = ";
							dump_sigspec_rhs(cell->getPort(ID(DATA)).extract(start, stop - start));
							f << ";\n";
						dec_indent();
						f << indent << "}\n";
						start = stop + 1;
					}
					if (stop != width)
						prev_en_bit = cell->getPort(ID(EN))[stop];
				}
			}
			if (cell->getParam(ID(CLK_ENABLE)).as_bool()) {
				dec_indent();
				f << indent << "}\n";
			}
		// Memory initializers
		} else if (cell->type == ID($meminit)) {
			// Handled elsewhere.
		} else if (cell->type[0] == '$') {
			log_cmd_error("Unsupported internal cell `%s'.\n", cell->type.c_str());
		} else {
			log_assert(false);
		}
	}

	void dump_case_rule(const RTLIL::CaseRule *rule)
	{
		for (auto action : rule->actions)
			dump_assign(action);
		for (auto switch_ : rule->switches)
			dump_switch_rule(switch_);
	}

	void dump_switch_rule(const RTLIL::SwitchRule *rule)
	{
		// The switch attributes are printed before the switch condition is captured.
		dump_attrs(rule);
		std::string signal_temp = fresh_temporary();
		f << indent << "const value<" << rule->signal.size() << "> &" << signal_temp << " = ";
		dump_sigspec(rule->signal, /*is_lhs=*/false);
		f << ";\n";

		bool first = true;
		for (auto case_ : rule->cases) {
			// The case attributes (for nested cases) are printed before the if/else if/else statement.
			dump_attrs(rule);
			f << indent;
			if (!first)
				f << "} else ";
			first = false;
			if (!case_->compare.empty()) {
				f << "if (";
				bool first = true;
				for (auto &compare : case_->compare) {
					if (!first)
						f << " || ";
					first = false;
					if (compare.is_fully_def()) {
						f << signal_temp << " == ";
						dump_sigspec(compare, /*is_lhs=*/false);
					} else if (compare.is_fully_const()) {
						RTLIL::Const compare_mask, compare_value;
						for (auto bit : compare.as_const()) {
							switch (bit) {
								case RTLIL::S0:
								case RTLIL::S1:
									compare_mask.bits.push_back(RTLIL::S1);
									compare_value.bits.push_back(bit);
									break;

								case RTLIL::Sx:
								case RTLIL::Sz:
								case RTLIL::Sa:
									compare_mask.bits.push_back(RTLIL::S0);
									compare_value.bits.push_back(RTLIL::S0);
									break;

								default:
									log_assert(false);
							}
						}
						f << "and_uu<" << compare.size() << ">(" << signal_temp << ", ";
						dump_const(compare_mask);
						f << ") == ";
						dump_const(compare_value);
					} else {
						log_assert(false);
					}
				}
				f << ") ";
			}
			f << "{\n";
			inc_indent();
				dump_case_rule(case_);
			dec_indent();
		}
		f << indent << "}\n";
	}

	void dump_process(const RTLIL::Process *proc)
	{
		dump_attrs(proc);
		f << indent << "// process " << proc->name.str() << "\n";
		// The case attributes (for root case) are always empty.
		log_assert(proc->root_case.attributes.empty());
		dump_case_rule(&proc->root_case);
		for (auto sync : proc->syncs) {
			RTLIL::SigBit sync_bit = sync->signal[0];
			sync_bit = sigmaps[sync_bit.wire->module](sync_bit);

			pool<std::string> events;
			switch (sync->type) {
				case RTLIL::STp:
					events.insert("posedge_" + mangle(sync_bit));
					break;
				case RTLIL::STn:
					events.insert("negedge_" + mangle(sync_bit));
				case RTLIL::STe:
					events.insert("posedge_" + mangle(sync_bit));
					events.insert("negedge_" + mangle(sync_bit));
					break;

				case RTLIL::ST0:
				case RTLIL::ST1:
				case RTLIL::STa:
				case RTLIL::STg:
				case RTLIL::STi:
					log_assert(false);
			}
			if (!events.empty()) {
				f << indent << "if (";
				bool first = true;
				for (auto &event : events) {
					if (!first)
						f << " || ";
					first = false;
					f << event;
				}
				f << ") {\n";
				inc_indent();
					for (auto action : sync->actions)
						dump_assign(action);
				dec_indent();
				f << indent << "}\n";
			}
		}
	}

	void dump_wire(const RTLIL::Wire *wire)
	{
		dump_attrs(wire);
		f << indent << "wire<" << wire->width << "> " << mangle(wire);
		if (wire->attributes.count(ID(init))) {
			f << " ";
			dump_const_init(wire->attributes.at(ID(init)));
		}
		f << ";\n";
		if (sync_wires[wire]) {
			for (auto sync_type : sync_types) {
				if (sync_type.first.wire == wire) {
					if (sync_type.second != RTLIL::STn)
						f << indent << "bool posedge_" << mangle(sync_type.first) << " = false;\n";
					if (sync_type.second != RTLIL::STp)
						f << indent << "bool negedge_" << mangle(sync_type.first) << " = false;\n";
				}
			}
		}
	}

	void dump_memory(RTLIL::Module *module, const RTLIL::Memory *memory)
	{
		vector<const RTLIL::Cell*> init_cells;
		for (auto cell : module->cells())
			if (cell->type == ID($meminit) && cell->getParam(ID(MEMID)).decode_string() == memory->name.str())
				init_cells.push_back(cell);

		std::sort(init_cells.begin(), init_cells.end(), [](const RTLIL::Cell *a, const RTLIL::Cell *b) {
			int a_addr = a->getPort(ID(ADDR)).as_int(), b_addr = b->getPort(ID(ADDR)).as_int();
			int a_prio = a->getParam(ID(PRIORITY)).as_int(), b_prio = b->getParam(ID(PRIORITY)).as_int();
			return a_prio > b_prio || (a_prio == b_prio && a_addr < b_addr);
		});

		dump_attrs(memory);
		f << indent << "memory_" << (writable_memories[memory] ? "rw" : "ro")
		            << "<" << memory->width << "> " << mangle(memory)
		            << " { " << memory->size << "u";
		if (init_cells.empty()) {
			f << " };\n";
		} else {
			f << ",\n";
			inc_indent();
				for (auto cell : init_cells) {
					dump_attrs(cell);
					RTLIL::Const data = cell->getPort(ID(DATA)).as_const();
					size_t width = cell->getParam(ID(WIDTH)).as_int();
					size_t words = cell->getParam(ID(WORDS)).as_int();
					f << indent << "memory_" << (writable_memories[memory] ? "rw" : "ro")
					            << "<" << memory->width << ">::init<" << words << "> { "
					            << stringf("%#x", cell->getPort(ID(ADDR)).as_int()) << ", {";
					inc_indent();
						for (size_t n = 0; n < words; n++) {
							if (n % 4 == 0)
								f << "\n" << indent;
							else
								f << " ";
							dump_const(data, width, n * width, /*fixed_width=*/true);
							f << ",";
						}
					dec_indent();
					f << "\n" << indent << "}},\n";
				}
			dec_indent();
			f << indent << "};\n";
		}
	}

	void dump_module(RTLIL::Module *module)
	{
		dump_attrs(module);
		f << "struct " << mangle(module) << " : public module {\n";
		inc_indent();
			for (auto wire : module->wires())
				dump_wire(wire);
			f << "\n";
			for (auto memory : module->memories)
				dump_memory(module, memory.second);
			if (!module->memories.empty())
				f << "\n";
			f << indent << "void eval() override;\n";
			f << indent << "bool commit() override;\n";
		dec_indent();
		f << "}; // struct " << mangle(module) << "\n";
		f << "\n";

		f << "void " << mangle(module) << "::eval() {\n";
		inc_indent();
			for (auto cell : module->cells())
				dump_cell(cell);
			f << indent << "// connections\n";
			for (auto conn : module->connections())
				dump_assign(conn);
			for (auto proc : module->processes)
				dump_process(proc.second);
			for (auto sync_type : sync_types) {
				if (sync_type.first.wire->module == module) {
					if (sync_type.second != RTLIL::STn)
						f << indent << "posedge_" << mangle(sync_type.first) << " = false;\n";
					if (sync_type.second != RTLIL::STp)
						f << indent << "negedge_" << mangle(sync_type.first) << " = false;\n";
				}
			}
		dec_indent();
		f << "}\n";

		f << "\n";
		f << "bool " << mangle(module) << "::commit() {\n";
		inc_indent();
			f << indent << "bool changed = false;\n";
			for (auto wire : module->wires()) {
				if (sync_wires[wire]) {
					std::string wire_prev = mangle(wire) + "_prev";
					std::string wire_curr = mangle(wire) + ".curr";
					std::string wire_edge = mangle(wire) + "_edge";
					f << indent << "value<" << wire->width << "> " << wire_prev << " = " << wire_curr << ";\n";
					f << indent << "if (" << mangle(wire) << ".commit()) {\n";
					inc_indent();
						f << indent << "value<" << wire->width << "> " << wire_edge << " = "
						            << wire_prev << ".bit_xor(" << wire_curr << ");\n";
						for (auto sync_type : sync_types) {
							if (sync_type.first.wire != wire)
								continue;
							if (sync_type.second != RTLIL::STn) {
								f << indent << "if (" << wire_edge << ".slice<" << sync_type.first.offset << ">().val() && "
								            << wire_curr << ".slice<" << sync_type.first.offset << ">().val())\n";
								inc_indent();
									f << indent << "posedge_" << mangle(sync_type.first) << " = true;\n";
								dec_indent();
							}
							if (sync_type.second != RTLIL::STp) {
								f << indent << "if (" << wire_edge << ".slice<" << sync_type.first.offset << ">().val() && "
								            << "!" << wire_curr << ".slice<" << sync_type.first.offset << ">().val())\n";
								inc_indent();
									f << indent << "negedge_" << mangle(sync_type.first) << " = true;\n";
								dec_indent();
							}
							f << indent << "changed = true;\n";
						}
					dec_indent();
					f << indent << "}\n";
				} else {
					f << indent << "changed |= " << mangle(wire) << ".commit();\n";
				}
			}
			for (auto memory : module->memories) {
				if (!writable_memories[memory.second])
					continue;
				f << indent << "for (size_t i = 0; i < " << memory.second->size << "u; i++)\n";
				inc_indent();
					f << indent << "changed |= " << mangle(memory.second) << "[i].commit();\n";
				dec_indent();
			}
			f << indent << "return changed;\n";
		dec_indent();
		f << "}\n";
	}

	void dump_design(RTLIL::Design *design)
	{
		f << "#include <cxxrtl.h>\n";
		f << "\n";
		f << "using namespace cxxrtl_yosys;\n";
		f << "\n";
		f << "namespace cxxrtl_design {\n";
		for (auto module : design->modules()) {
			if (module->get_blackbox_attribute())
				continue;

			if (!design->selected_module(module))
				continue;

			f << "\n";
			dump_module(module);
		}
		f << "\n";
		f << "} // namespace cxxrtl_design\n";
	}

	// Edge-type sync rules require us to emit edge detectors, which require coordination between
	// eval and commit phases. To do this we need to collect them upfront.
	//
	// Note that the simulator commit phase operates at wire granularity but edge-type sync rules
	// operate at wire bit granularity; it is possible to have code similar to:
	//     wire [3:0] clocks;
	//     always @(posedge clocks[0]) ...
	// To handle this we track edge sensitivity both for wires and wire bits.
	void register_edge_signal(SigMap &sigmap, RTLIL::SigSpec signal, RTLIL::SyncType type)
	{
		signal = sigmap(signal);
		log_assert(signal.is_wire() && signal.is_bit());
		log_assert(type == RTLIL::STp || type == RTLIL::STn || type == RTLIL::STe);

		RTLIL::SigBit sigbit = signal[0];
		if (!sync_types.count(sigbit))
			sync_types[sigbit] = type;
		else if (sync_types[sigbit] != type)
			sync_types[sigbit] = RTLIL::STe;
		sync_wires.insert(signal.as_wire());
	}

	void analyze_design(RTLIL::Design *design)
	{
		for (auto module : design->modules()) {
			SigMap &sigmap = sigmaps[module];
			sigmap.set(module);

			for (auto cell : module->cells()) {
				// Various DFF cells are treated like posedge/negedge processes, see above for details.
				if (cell->type.in(ID($dff), ID($dffe), ID($adff), ID($dffsr))) {
					if (cell->getPort(ID(CLK)).is_wire())
						register_edge_signal(sigmap, cell->getPort(ID(CLK)),
							cell->parameters[ID(CLK_POLARITY)].as_bool() ? RTLIL::STp : RTLIL::STn);
					// The $adff and $dffsr cells are level-sensitive, not edge-sensitive (in spite of the fact that they
					// are inferred from an edge-sensitive Verilog process) and do not correspond to an edge-type sync rule.
				}
				// Similar for memory port cells.
				if (cell->type.in(ID($memrd), ID($memwr))) {
					if (cell->getParam(ID(CLK_ENABLE)).as_bool()) {
						if (cell->getPort(ID(CLK)).is_wire())
							register_edge_signal(sigmap, cell->getPort(ID(CLK)),
								cell->parameters[ID(CLK_POLARITY)].as_bool() ? RTLIL::STp : RTLIL::STn);
					}
				}
				// Optimize access to read-only memories.
				if (cell->type == ID($memwr))
					writable_memories.insert(module->memories[cell->getParam(ID(MEMID)).decode_string()]);
				// Handling of packed memories is delegated to the `memory_unpack` pass, so we can rely on the presence
				// of RTLIL memory objects and $memrd/$memwr/$meminit cells.
				if (cell->type.in(ID($mem)))
					log_assert(false);
			}

			for (auto proc : module->processes)
				for (auto sync : proc.second->syncs)
					switch (sync->type) {
						// Edge-type sync rules require pre-registration.
						case RTLIL::STp:
						case RTLIL::STn:
						case RTLIL::STe:
							register_edge_signal(sigmap, sync->signal, sync->type);
							break;

						// Level-type sync rules require no special handling.
						case RTLIL::ST0:
						case RTLIL::ST1:
						case RTLIL::STa:
							break;

						// Handling of init-type sync rules is delegated to the `proc_init` pass, so we can use the wire
						// attribute regardless of input.
						case RTLIL::STi:
							log_assert(false);

						case RTLIL::STg:
							log_cmd_error("Global clock is not supported.\n");
					}
		}
	}

	void check_design(RTLIL::Design *design, bool &has_sync_init, bool &has_packed_mem)
	{
		has_sync_init = has_packed_mem = false;

		for (auto module : design->modules()) {
			if (module->get_blackbox_attribute())
				continue;

			if (!design->selected_whole_module(module))
				if (design->selected_module(module))
					log_cmd_error("Can't handle partially selected module %s!\n", id2cstr(module->name));

			for (auto proc : module->processes)
				for (auto sync : proc.second->syncs)
					if (sync->type == RTLIL::STi)
						has_sync_init = true;

			for (auto cell : module->cells())
				if (cell->type == ID($mem))
					has_packed_mem = true;
		}
	}

	void prepare_design(RTLIL::Design *design)
	{
		bool has_sync_init, has_packed_mem;
		check_design(design, has_sync_init, has_packed_mem);
		if (has_sync_init)
			Pass::call(design, "proc_init");
		if (has_packed_mem)
			Pass::call(design, "memory_unpack");
		// Recheck the design if it was modified.
		if (has_sync_init || has_packed_mem)
			check_design(design, has_sync_init, has_packed_mem);

		log_assert(!(has_sync_init || has_packed_mem));
		analyze_design(design);
	}
};

struct CxxrtlBackend : public Backend {
	CxxrtlBackend() : Backend("cxxrtl", "convert design to C++ RTL simulation") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_cxxrtl [options] [filename]\n");
		log("\n");
		log("Write C++ code for simulating the design.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing CXXRTL backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-top" && argidx+1 < args.size()) {
			// 	top_module_name = args[++argidx];
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		CxxrtlWorker worker(*f);
		worker.prepare_design(design);
		worker.dump_design(design);
	}
} CxxrtlBackend;

PRIVATE_NAMESPACE_END
