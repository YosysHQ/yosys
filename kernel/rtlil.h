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

#ifndef RTLIL_H
#define RTLIL_H

#include <map>
#include <set>
#include <vector>
#include <string>
#include <assert.h>

std::string stringf(const char *fmt, ...);

namespace RTLIL
{
	enum State {
		S0 = 0,
		S1 = 1,
		Sx = 2, // undefined value or conflict
		Sz = 3, // high-impedance / not-connected
		Sa = 4, // don't care (used only in cases)
		Sm = 5  // marker (used internally by some passes)
	};

	enum SyncType {
		ST0 = 0, // level sensitive: 0
		ST1 = 1, // level sensitive: 1
		STp = 2, // edge sensitive: posedge
		STn = 3, // edge sensitive: negedge
		STe = 4, // edge sensitive: both edges
		STa = 5, // always active
		STi = 6  // init
	};

	enum ConstFlags {
		CONST_FLAG_NONE   = 0,
		CONST_FLAG_STRING = 1,
		CONST_FLAG_SIGNED = 2,  // only used for parameters
		CONST_FLAG_REAL   = 4   // unused -- to be used for parameters
	};

	extern int autoidx;

	struct Const;
	struct Selection;
	struct Design;
	struct Module;
	struct Wire;
	struct Memory;
	struct Cell;
	struct SigChunk;
	struct SigBit;
	struct SigSpec;
	struct CaseRule;
	struct SwitchRule;
	struct SyncRule;
	struct Process;

	typedef std::pair<SigSpec, SigSpec> SigSig;

#ifdef NDEBUG
	typedef std::string IdString;
#else
	struct IdString : public std::string {
		IdString() { }
		IdString(std::string str) : std::string(str) {
			check();
		}
		IdString(const char *s) : std::string(s) {
			check();
		}
		IdString &operator=(const std::string &str) {
			std::string::operator=(str);
			check();
			return *this;
		}
		IdString &operator=(const char *s) {
			std::string::operator=(s);
			check();
			return *this;
		}
		bool operator<(const IdString &rhs) {
			check(), rhs.check();
			return std::string(*this) < std::string(rhs);
		}
		void check() const {
			assert(empty() || (size() >= 2 && (at(0) == '$' || at(0) == '\\')));
		}
	};
#endif

	static IdString escape_id(std::string str) __attribute__((unused));
	static IdString escape_id(std::string str) {
		if (str.size() > 0 && str[0] != '\\' && str[0] != '$')
			return "\\" + str;
		return str;
	}

	static std::string unescape_id(std::string str) __attribute__((unused));
	static std::string unescape_id(std::string str) {
		if (str.size() > 1 && str[0] == '\\' && str[1] != '$')
			return str.substr(1);
		return str;
	}

	static const char *id2cstr(std::string str) __attribute__((unused));
	static const char *id2cstr(std::string str) {
		if (str.size() > 1 && str[0] == '\\' && str[1] != '$')
			return str.c_str() + 1;
		return str.c_str();
	}

	static IdString new_id(std::string file, int line, std::string func) __attribute__((unused));
	static IdString new_id(std::string file, int line, std::string func) {
		std::string str = "$auto$";
		size_t pos = file.find_last_of('/');
		str += pos != std::string::npos ? file.substr(pos+1) : file;
		str += stringf(":%d:%s$%d", line, func.c_str(), autoidx++);
		return str;
	}

#define NEW_ID \
	RTLIL::new_id(__FILE__, __LINE__, __FUNCTION__)

#define NEW_WIRE(_mod, _width) \
	(_mod)->new_wire(_width, NEW_ID)

	template <typename T> struct sort_by_name {
		bool operator()(T *a, T *b) const {
			return a->name < b->name;
		}
	};

	// see calc.cc for the implementation of this functions
	RTLIL::Const const_not         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_and         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_or          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_xor         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_xnor        (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_reduce_and  (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_reduce_or   (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_reduce_xor  (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_reduce_xnor (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_reduce_bool (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_logic_not   (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_logic_and   (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_logic_or    (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_shl         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_shr         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_sshl        (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_sshr        (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_lt          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_le          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_eq          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_ne          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_ge          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_gt          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_add         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_sub         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_mul         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_div         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_mod         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_pow         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_pos         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_neg         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
};

struct RTLIL::Const {
	int flags;
	std::vector<RTLIL::State> bits;
	Const();
	Const(std::string str);
	Const(int val, int width = 32);
	Const(RTLIL::State bit, int width = 1);
	Const(std::vector<RTLIL::State> bits) : bits(bits) { flags = CONST_FLAG_NONE; };
	bool operator <(const RTLIL::Const &other) const;
	bool operator ==(const RTLIL::Const &other) const;
	bool operator !=(const RTLIL::Const &other) const;
	bool as_bool() const;
	int as_int() const;
	std::string as_string() const;
	std::string decode_string() const;
};

struct RTLIL::Selection {
	bool full_selection;
	std::set<RTLIL::IdString> selected_modules;
	std::map<RTLIL::IdString, std::set<RTLIL::IdString>> selected_members;
	Selection(bool full = true) : full_selection(full) { }
	bool selected_module(RTLIL::IdString mod_name) const;
	bool selected_whole_module(RTLIL::IdString mod_name) const;
	bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;
	void optimize(RTLIL::Design *design);
	template<typename T1> void select(T1 *module) {
		if (!full_selection && selected_modules.count(module->name) == 0) {
			selected_modules.insert(module->name);
			selected_members.erase(module->name);
		}
	}
	template<typename T1, typename T2> void select(T1 *module, T2 *member) {
		if (!full_selection && selected_modules.count(module->name) == 0)
			selected_members[module->name].insert(member->name);
	}
};

struct RTLIL::Design {
	std::map<RTLIL::IdString, RTLIL::Module*> modules;
	std::vector<RTLIL::Selection> selection_stack;
	std::map<RTLIL::IdString, RTLIL::Selection> selection_vars;
	std::string selected_active_module;
	~Design();
	void check();
	void optimize();
	bool selected_module(RTLIL::IdString mod_name) const;
	bool selected_whole_module(RTLIL::IdString mod_name) const;
	bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;
	bool full_selection() const {
		return selection_stack.back().full_selection;
	}
	template<typename T1> bool selected(T1 *module) const {
		return selected_module(module->name);
	}
	template<typename T1, typename T2> bool selected(T1 *module, T2 *member) const {
		return selected_member(module->name, member->name);
	}
	template<typename T1, typename T2> void select(T1 *module, T2 *member) {
		if (selection_stack.size() > 0) {
			RTLIL::Selection &sel = selection_stack.back();
			sel.select(module, member);
		}
	}
};

#define RTLIL_ATTRIBUTE_MEMBERS                                \
	std::map<RTLIL::IdString, RTLIL::Const> attributes;    \
	void set_bool_attribute(RTLIL::IdString id) {          \
		attributes[id] = RTLIL::Const(1);              \
	}                                                      \
	bool get_bool_attribute(RTLIL::IdString id) const {    \
		if (attributes.count(id) == 0)                 \
			return false;                          \
		return attributes.at(id).as_bool();            \
	}

struct RTLIL::Module {
	RTLIL::IdString name;
	std::set<RTLIL::IdString> avail_parameters;
	std::map<RTLIL::IdString, RTLIL::Wire*> wires;
	std::map<RTLIL::IdString, RTLIL::Memory*> memories;
	std::map<RTLIL::IdString, RTLIL::Cell*> cells;
	std::map<RTLIL::IdString, RTLIL::Process*> processes;
	std::vector<RTLIL::SigSig> connections;
	RTLIL_ATTRIBUTE_MEMBERS
	virtual ~Module();
	virtual RTLIL::IdString derive(RTLIL::Design *design, std::map<RTLIL::IdString, RTLIL::Const> parameters);
	virtual size_t count_id(RTLIL::IdString id);
	virtual void check();
	virtual void optimize();
	RTLIL::Wire *new_wire(int width, RTLIL::IdString name);
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);
	void fixup_ports();

	template<typename T> void rewrite_sigspecs(T functor);
	void cloneInto(RTLIL::Module *new_mod) const;
	virtual RTLIL::Module *clone() const;

};

struct RTLIL::Wire {
	RTLIL::IdString name;
	int width, start_offset, port_id;
	bool port_input, port_output;
	RTLIL_ATTRIBUTE_MEMBERS
	Wire();
};

struct RTLIL::Memory {
	RTLIL::IdString name;
	int width, start_offset, size;
	RTLIL_ATTRIBUTE_MEMBERS
	Memory();
};

struct RTLIL::Cell {
	RTLIL::IdString name;
	RTLIL::IdString type;
	std::map<RTLIL::IdString, RTLIL::SigSpec> connections;
	std::map<RTLIL::IdString, RTLIL::Const> parameters;
	RTLIL_ATTRIBUTE_MEMBERS
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
};

struct RTLIL::SigChunk {
	RTLIL::Wire *wire;
	RTLIL::Const data; // only used if wire == NULL, LSB at index 0
	int width, offset;
	SigChunk();
	SigChunk(const RTLIL::Const &data);
	SigChunk(RTLIL::Wire *wire, int width, int offset);
	SigChunk(const std::string &str);
	SigChunk(int val, int width = 32);
	SigChunk(RTLIL::State bit, int width = 1);
	SigChunk(RTLIL::SigBit bit);
	RTLIL::SigChunk extract(int offset, int length) const;
	bool operator <(const RTLIL::SigChunk &other) const;
	bool operator ==(const RTLIL::SigChunk &other) const;
	bool operator !=(const RTLIL::SigChunk &other) const;
	static bool compare(const RTLIL::SigChunk &a, const RTLIL::SigChunk &b);
};

struct RTLIL::SigBit {
	RTLIL::Wire *wire;
	RTLIL::State data;
	int offset;
	SigBit() : wire(NULL), data(RTLIL::State::S0), offset(0) { }
	SigBit(RTLIL::State bit) : wire(NULL), data(bit), offset(0) { }
	SigBit(RTLIL::Wire *wire) : wire(wire), data(RTLIL::State::S0), offset(0) { assert(!wire || wire->width == 1); }
	SigBit(RTLIL::Wire *wire, int offset) : wire(wire), data(RTLIL::State::S0), offset(offset) { }
	SigBit(const RTLIL::SigChunk &chunk) : wire(chunk.wire), data(chunk.wire ? RTLIL::State::S0 : chunk.data.bits[0]), offset(chunk.offset) { assert(chunk.width == 1); }
	SigBit(const RTLIL::SigChunk &chunk, int index) : wire(chunk.wire), data(chunk.wire ? RTLIL::State::S0 : chunk.data.bits[index]), offset(chunk.wire ? chunk.offset + index : 0) { }
	SigBit(const RTLIL::SigSpec &sig);
	bool operator <(const RTLIL::SigBit &other) const {
		return (wire != other.wire) ? (wire < other.wire) : wire ? (offset < other.offset) : (data < other.data);
	}
	bool operator ==(const RTLIL::SigBit &other) const {
		return (wire == other.wire) && (wire ? (offset == other.offset) : (data == other.data));
	}
	bool operator !=(const RTLIL::SigBit &other) const {
		return (wire != other.wire) || (wire ? (offset != other.offset) : (data != other.data));
	}
};

struct RTLIL::SigSpec {
	std::vector<RTLIL::SigChunk> chunks; // LSB at index 0
	int width;
	SigSpec();
	SigSpec(const RTLIL::Const &data);
	SigSpec(const RTLIL::SigChunk &chunk);
	SigSpec(RTLIL::Wire *wire, int width = -1, int offset = 0);
	SigSpec(const std::string &str);
	SigSpec(int val, int width = 32);
	SigSpec(RTLIL::State bit, int width = 1);
	SigSpec(RTLIL::SigBit bit, int width = 1);
	SigSpec(std::vector<RTLIL::SigBit> bits);
	void expand();
	void optimize();
	void sort();
	void sort_and_unify();
	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with);
	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const;
	void remove(const RTLIL::SigSpec &pattern);
	void remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const;
	void remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other);
	RTLIL::SigSpec extract(RTLIL::SigSpec pattern, RTLIL::SigSpec *other = NULL) const;
	void replace(int offset, const RTLIL::SigSpec &with);
	void remove_const();
	void remove(int offset, int length);
	RTLIL::SigSpec extract(int offset, int length) const;
	void append(const RTLIL::SigSpec &signal);
	void append_bit(const RTLIL::SigBit &bit);
	bool combine(RTLIL::SigSpec signal, RTLIL::State freeState = RTLIL::State::Sz, bool override = false);
	void extend(int width, bool is_signed = false);
	void extend_u0(int width, bool is_signed = false);
	void check() const;
	bool operator <(const RTLIL::SigSpec &other) const;
	bool operator ==(const RTLIL::SigSpec &other) const;
	bool operator !=(const RTLIL::SigSpec &other) const;
	bool is_fully_const() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool has_marked_bits() const;
	bool as_bool() const;
	int as_int() const;
	std::string as_string() const;
	RTLIL::Const as_const() const;
	bool match(std::string pattern) const;
	std::set<RTLIL::SigBit> to_sigbit_set() const;
	std::vector<RTLIL::SigBit> to_sigbit_vector() const;
	static bool parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
	static bool parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
};

inline RTLIL::SigBit::SigBit(const RTLIL::SigSpec &sig) {
	assert(sig.width == 1 && sig.chunks.size() == 1);
	*this = SigBit(sig.chunks[0]);
}

struct RTLIL::CaseRule {
	std::vector<RTLIL::SigSpec> compare;
	std::vector<RTLIL::SigSig> actions;
	std::vector<RTLIL::SwitchRule*> switches;
	~CaseRule();
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::CaseRule *clone() const;
};

struct RTLIL::SwitchRule {
	RTLIL::SigSpec signal;
	RTLIL_ATTRIBUTE_MEMBERS
	std::vector<RTLIL::CaseRule*> cases;
	~SwitchRule();
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::SwitchRule *clone() const;
};

struct RTLIL::SyncRule {
	RTLIL::SyncType type;
	RTLIL::SigSpec signal;
	std::vector<RTLIL::SigSig> actions;
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::SyncRule *clone() const;
};

struct RTLIL::Process {
	RTLIL::IdString name;
	RTLIL_ATTRIBUTE_MEMBERS
	RTLIL::CaseRule root_case;
	std::vector<RTLIL::SyncRule*> syncs;
	~Process();
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::Process *clone() const;
};

template<typename T>
void RTLIL::Module::rewrite_sigspecs(T functor)
{
	for (auto &it : cells)
		it.second->rewrite_sigspecs(functor);
	for (auto &it : processes)
		it.second->rewrite_sigspecs(functor);
	for (auto &it : connections) {
		functor(it.first);
		functor(it.second);
	}
}

template<typename T>
void RTLIL::Cell::rewrite_sigspecs(T functor) {
	for (auto &it : connections)
		functor(it.second);
}

template<typename T>
void RTLIL::CaseRule::rewrite_sigspecs(T functor) {
	for (auto &it : compare)
		functor(it);
	for (auto &it : actions) {
		functor(it.first);
		functor(it.second);
	}
	for (auto it : switches)
		it->rewrite_sigspecs(functor);
}

template<typename T>
void RTLIL::SwitchRule::rewrite_sigspecs(T functor)
{
	functor(signal);
	for (auto it : cases)
		it->rewrite_sigspecs(functor);
}

template<typename T>
void RTLIL::SyncRule::rewrite_sigspecs(T functor)
{
	functor(signal);
	for (auto &it : actions) {
		functor(it.first);
		functor(it.second);
	}
}

template<typename T>
void RTLIL::Process::rewrite_sigspecs(T functor)
{
	root_case.rewrite_sigspecs(functor);
	for (auto it : syncs)
		it->rewrite_sigspecs(functor);
}

#endif
