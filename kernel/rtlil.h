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

#ifndef RTLIL_H
#define RTLIL_H

YOSYS_NAMESPACE_BEGIN

namespace RTLIL
{
	enum State : unsigned char {
		S0 = 0,
		S1 = 1,
		Sx = 2, // undefined value or conflict
		Sz = 3, // high-impedance / not-connected
		Sa = 4, // don't care (used only in cases)
		Sm = 5  // marker (used internally by some passes)
	};

	enum SyncType : unsigned char {
		ST0 = 0, // level sensitive: 0
		ST1 = 1, // level sensitive: 1
		STp = 2, // edge sensitive: posedge
		STn = 3, // edge sensitive: negedge
		STe = 4, // edge sensitive: both edges
		STa = 5, // always active
		STi = 6  // init
	};

	enum ConstFlags : unsigned char {
		CONST_FLAG_NONE   = 0,
		CONST_FLAG_STRING = 1,
		CONST_FLAG_SIGNED = 2,  // only used for parameters
		CONST_FLAG_REAL   = 4   // unused -- to be used for parameters
	};

	struct Const;
	struct Selection;
	struct Design;
	struct Module;
	struct Wire;
	struct Memory;
	struct Cell;
	struct SigChunk;
	struct SigBit;
	struct SigSpecIterator;
	struct SigSpecConstIterator;
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
			log_assert(empty() || (size() >= 2 && (at(0) == '$' || at(0) == '\\')));
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
	RTLIL::Const const_shift       (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_shiftx      (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_lt          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_le          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_eq          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_ne          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_eqx         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_nex         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_ge          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_gt          (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_add         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_sub         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_mul         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_div         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_mod         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_pow         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_pos         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_bu0         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_neg         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);


	// This iterator-range-pair is used for Design::modules(), Module::wires() and Module::cells().
	// It maintains a reference counter that is used to make sure that the container is not modified while being iterated over.

	template<typename T>
	struct ObjIterator
	{
		typename std::map<RTLIL::IdString, T>::iterator it;
		std::map<RTLIL::IdString, T> *list_p;
		int *refcount_p;

		ObjIterator() : list_p(nullptr), refcount_p(nullptr) {
		}

		ObjIterator(decltype(list_p) list_p, int *refcount_p) : list_p(list_p), refcount_p(refcount_p) {
			if (list_p->empty()) {
				this->list_p = nullptr;
				this->refcount_p = nullptr;
			} else {
				it = list_p->begin();
				(*refcount_p)++;
			}
		}

		ObjIterator(const RTLIL::ObjIterator<T> &other) {
			it = other.it;
			list_p = other.list_p;
			refcount_p = other.refcount_p;
			if (refcount_p)
				(*refcount_p)++;
		}

		ObjIterator &operator=(const RTLIL::ObjIterator<T> &other) {
			if (refcount_p)
				(*refcount_p)--;
			it = other.it;
			list_p = other.list_p;
			refcount_p = other.refcount_p;
			if (refcount_p)
				(*refcount_p)++;
			return *this;
		}

		~ObjIterator() {
			if (refcount_p)
				(*refcount_p)--;
		}

		inline T operator*() const {
			log_assert(list_p != nullptr);
			return it->second;
		}

		inline bool operator!=(const RTLIL::ObjIterator<T> &other) const {
			if (list_p == nullptr || other.list_p == nullptr)
				return list_p != other.list_p;
			return it != other.it;
		}

		inline void operator++() {
			log_assert(list_p != nullptr);
			if (++it == list_p->end()) {
				(*refcount_p)--;
				list_p = nullptr;
				refcount_p = nullptr;
			}
		}
	};

	template<typename T>
	struct ObjRange
	{
		std::map<RTLIL::IdString, T> *list_p;
		int *refcount_p;

		ObjRange(decltype(list_p) list_p, int *refcount_p) : list_p(list_p), refcount_p(refcount_p) { }
		RTLIL::ObjIterator<T> begin() { return RTLIL::ObjIterator<T>(list_p, refcount_p); }
		RTLIL::ObjIterator<T> end() { return RTLIL::ObjIterator<T>(); }

		operator std::set<T>() const {
			std::set<T> result;
			for (auto &it : *list_p)
				result.insert(it.second);
			return result;
		}

		operator std::vector<T>() const {
			std::vector<T> result;
			result.reserve(list_p->size());
			for (auto &it : *list_p)
				result.push_back(it.second);
			return result;
		}

		std::set<T> to_set() const { return *this; }
		std::vector<T> to_vector() const { return *this; }
	};
};

struct RTLIL::Const
{
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

struct RTLIL::Selection
{
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

	bool empty() const {
		return !full_selection && selected_modules.empty() && selected_members.empty();
	}
};

struct RTLIL::Design
{
	int refcount_modules_;
	std::map<RTLIL::IdString, RTLIL::Module*> modules_;

	std::vector<RTLIL::Selection> selection_stack;
	std::map<RTLIL::IdString, RTLIL::Selection> selection_vars;
	std::string selected_active_module;

	Design();
	~Design();

	RTLIL::ObjRange<RTLIL::Module*> modules();
	RTLIL::Module *module(RTLIL::IdString name);

	bool has(RTLIL::IdString id) const {
		return modules_.count(id) != 0;
	}

	void add(RTLIL::Module *module);
	RTLIL::Module *addModule(RTLIL::IdString name);
	void remove(RTLIL::Module *module);

	void check();
	void optimize();

	bool selected_module(RTLIL::IdString mod_name) const;
	bool selected_whole_module(RTLIL::IdString mod_name) const;
	bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;

	bool selected_module(RTLIL::Module *mod) const;
	bool selected_whole_module(RTLIL::Module *mod) const;

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

struct RTLIL::Module
{
protected:
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);

public:
	int refcount_wires_;
	int refcount_cells_;

	std::map<RTLIL::IdString, RTLIL::Wire*> wires_;
	std::map<RTLIL::IdString, RTLIL::Cell*> cells_;
	std::vector<RTLIL::SigSig> connections_;

	RTLIL::IdString name;
	std::set<RTLIL::IdString> avail_parameters;
	std::map<RTLIL::IdString, RTLIL::Memory*> memories;
	std::map<RTLIL::IdString, RTLIL::Process*> processes;
	RTLIL_ATTRIBUTE_MEMBERS

	Module();
	virtual ~Module();
	virtual RTLIL::IdString derive(RTLIL::Design *design, std::map<RTLIL::IdString, RTLIL::Const> parameters);
	virtual size_t count_id(RTLIL::IdString id);
	virtual void check();
	virtual void optimize();

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	const std::vector<RTLIL::SigSig> &connections() const;
	void fixup_ports();

	template<typename T> void rewrite_sigspecs(T functor);
	void cloneInto(RTLIL::Module *new_mod) const;
	virtual RTLIL::Module *clone() const;

	RTLIL::Wire* wire(RTLIL::IdString id) { return wires_.count(id) ? wires_.at(id) : nullptr; }
	RTLIL::Cell* cell(RTLIL::IdString id) { return cells_.count(id) ? cells_.at(id) : nullptr; }

	RTLIL::ObjRange<RTLIL::Wire*> wires() { return RTLIL::ObjRange<RTLIL::Wire*>(&wires_, &refcount_wires_); }
	RTLIL::ObjRange<RTLIL::Cell*> cells() { return RTLIL::ObjRange<RTLIL::Cell*>(&cells_, &refcount_cells_); }

	// Removing wires is expensive. If you have to remove wires, remove them all at once.
	void remove(const std::set<RTLIL::Wire*> &wires);
	void remove(RTLIL::Cell *cell);

	void rename(RTLIL::Wire *wire, RTLIL::IdString new_name);
	void rename(RTLIL::Cell *cell, RTLIL::IdString new_name);
	void rename(RTLIL::IdString old_name, RTLIL::IdString new_name);

	RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
	RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);

	RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
	RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);

	// The add* methods create a cell and return the created cell. All signals must exist in advance.

	RTLIL::Cell* addNot (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addPos (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addBu0 (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addNeg (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addAnd  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addOr   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addXor  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addXnor (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addReduceAnd  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addReduceOr   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addReduceXor  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addReduceXnor (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addReduceBool (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addShl    (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addShr    (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addSshl   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addSshr   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addShift  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addShiftx (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addLt  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addLe  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addEq  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addNe  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addEqx (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addNex (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addGe  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addGt  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addAdd (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addSub (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addMul (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addDiv (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addMod (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addPow (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool a_signed = false, bool b_signed = false);
                     
	RTLIL::Cell* addLogicNot (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addLogicAnd (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
	RTLIL::Cell* addLogicOr  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed = false);
                     
	RTLIL::Cell* addMux      (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addPmux     (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addSafePmux (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y);
                     
	RTLIL::Cell* addSlice  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset);
	RTLIL::Cell* addConcat (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addLut    (RTLIL::IdString name, RTLIL::SigSpec sig_i, RTLIL::SigSpec sig_o, RTLIL::Const lut);
	RTLIL::Cell* addAssert (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en);

	RTLIL::Cell* addSr    (RTLIL::IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, RTLIL::SigSpec sig_q, bool set_polarity = true, bool clr_polarity = true);
	RTLIL::Cell* addDff   (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d,   RTLIL::SigSpec sig_q, bool clk_polarity = true);
	RTLIL::Cell* addDffsr (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
			RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true);
	RTLIL::Cell* addAdff (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
			RTLIL::Const arst_value, bool clk_polarity = true, bool arst_polarity = true);
	RTLIL::Cell* addDlatch (RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true);
	RTLIL::Cell* addDlatchsr (RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
			RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true);

	RTLIL::Cell* addInvGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addAndGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addOrGate   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addXorGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y);
	RTLIL::Cell* addMuxGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y);

	RTLIL::Cell* addDffGate    (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true);
	RTLIL::Cell* addDffsrGate  (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
			RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true);
	RTLIL::Cell* addAdffGate   (RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
			bool arst_value = false, bool clk_polarity = true, bool arst_polarity = true);
	RTLIL::Cell* addDlatchGate (RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true);
	RTLIL::Cell* addDlatchsrGate  (RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
			RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true);

	// The methods without the add* prefix create a cell and an output signal. They return the newly created output signal.

	RTLIL::SigSpec Not (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec Pos (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec Bu0 (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec Neg (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);

	RTLIL::SigSpec And  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Or   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Xor  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Xnor (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);

	RTLIL::SigSpec ReduceAnd  (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec ReduceOr   (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec ReduceXor  (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec ReduceXnor (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec ReduceBool (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);

	RTLIL::SigSpec Shl    (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Shr    (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Sshl   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Sshr   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Shift  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Shiftx (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);

	RTLIL::SigSpec Lt  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Le  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Eq  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Ne  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Eqx (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Nex (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Ge  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Gt  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);

	RTLIL::SigSpec Add (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Sub (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Mul (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Div (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Mod (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec Pow (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool a_signed = false, bool b_signed = false);

	RTLIL::SigSpec LogicNot (RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed = false);
	RTLIL::SigSpec LogicAnd (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);
	RTLIL::SigSpec LogicOr  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed = false);

	RTLIL::SigSpec Mux      (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s);
	RTLIL::SigSpec Pmux     (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s);
	RTLIL::SigSpec SafePmux (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s);

	RTLIL::SigSpec InvGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a);
	RTLIL::SigSpec AndGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b);
	RTLIL::SigSpec OrGate   (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b);
	RTLIL::SigSpec XorGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b);
	RTLIL::SigSpec MuxGate  (RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s);
};

struct RTLIL::Wire
{
protected:
	// use module->addWire() and module->remove() to create or destroy wires
	friend struct RTLIL::Module;
	Wire();
	~Wire() { };

public:
	// do not simply copy wires
	Wire(RTLIL::Wire &other) = delete;
	void operator=(RTLIL::Wire &other) = delete;

	RTLIL::IdString name;
	int width, start_offset, port_id;
	bool port_input, port_output, upto;
	RTLIL_ATTRIBUTE_MEMBERS
};

struct RTLIL::Memory
{
	Memory();

	RTLIL::IdString name;
	int width, start_offset, size;
	RTLIL_ATTRIBUTE_MEMBERS
};

struct RTLIL::Cell
{
protected:
	// use module->addCell() and module->remove() to create or destroy cells
	friend struct RTLIL::Module;
	Cell() { };
	~Cell() { };

public:
	// do not simply copy cells
	Cell(RTLIL::Cell &other) = delete;
	void operator=(RTLIL::Cell &other) = delete;

	RTLIL::IdString name;
	RTLIL::IdString type;
	std::map<RTLIL::IdString, RTLIL::SigSpec> connections_;
	std::map<RTLIL::IdString, RTLIL::Const> parameters;
	RTLIL_ATTRIBUTE_MEMBERS

	// access cell ports
	bool has(RTLIL::IdString portname);
	void unset(RTLIL::IdString portname);
	void set(RTLIL::IdString portname, RTLIL::SigSpec signal);
	const RTLIL::SigSpec &get(RTLIL::IdString portname) const;
	const std::map<RTLIL::IdString, RTLIL::SigSpec> &connections() const;

	void check();
	void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false);

	template<typename T> void rewrite_sigspecs(T functor);
};

struct RTLIL::SigChunk
{
	RTLIL::Wire *wire;
	RTLIL::Const data; // only used if wire == NULL, LSB at index 0
	int width, offset;

	SigChunk();
	SigChunk(const RTLIL::Const &value);
	SigChunk(RTLIL::Wire *wire);
	SigChunk(RTLIL::Wire *wire, int offset, int width = 1);
	SigChunk(const std::string &str);
	SigChunk(int val, int width = 32);
	SigChunk(RTLIL::State bit, int width = 1);
	SigChunk(RTLIL::SigBit bit);

	RTLIL::SigChunk extract(int offset, int length) const;

	bool operator <(const RTLIL::SigChunk &other) const;
	bool operator ==(const RTLIL::SigChunk &other) const;
	bool operator !=(const RTLIL::SigChunk &other) const;
};

struct RTLIL::SigBit
{
	RTLIL::Wire *wire;
	RTLIL::State data;
	int offset;

	SigBit() : wire(NULL), data(RTLIL::State::S0), offset(0) { }
	SigBit(RTLIL::State bit) : wire(NULL), data(bit), offset(0) { }
	SigBit(RTLIL::Wire *wire) : wire(wire), data(RTLIL::State::S0), offset(0) { log_assert(wire && wire->width == 1); }
	SigBit(RTLIL::Wire *wire, int offset) : wire(wire), data(RTLIL::State::S0), offset(offset) { log_assert(wire); }
	SigBit(const RTLIL::SigChunk &chunk) : wire(chunk.wire), data(chunk.wire ? RTLIL::State::S0 : chunk.data.bits[0]), offset(chunk.offset) { log_assert(chunk.width == 1); }
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

struct RTLIL::SigSpecIterator
{
	RTLIL::SigSpec *sig_p;
	int index;

	inline RTLIL::SigBit &operator*() const;
	inline bool operator!=(const RTLIL::SigSpecIterator &other) const { return index != other.index; }
	inline void operator++() { index++; }
};

struct RTLIL::SigSpecConstIterator
{
	const RTLIL::SigSpec *sig_p;
	int index;

	inline const RTLIL::SigBit &operator*() const;
	inline bool operator!=(const RTLIL::SigSpecConstIterator &other) const { return index != other.index; }
	inline void operator++() { index++; }
};

struct RTLIL::SigSpec
{
private:
	int width_;
	unsigned long hash_;
	std::vector<RTLIL::SigChunk> chunks_; // LSB at index 0
	std::vector<RTLIL::SigBit> bits_; // LSB at index 0

	void pack() const;
	void unpack() const;
	void hash() const;

	inline bool packed() const {
		return bits_.empty();
	}

	inline void inline_unpack() const {
		if (!chunks_.empty())
			unpack();
	}

public:
	SigSpec();
	SigSpec(const RTLIL::SigSpec &other);
	SigSpec(std::initializer_list<RTLIL::SigSpec> parts);
	const RTLIL::SigSpec &operator=(const RTLIL::SigSpec &other);

	SigSpec(const RTLIL::Const &value);
	SigSpec(const RTLIL::SigChunk &chunk);
	SigSpec(RTLIL::Wire *wire);
	SigSpec(RTLIL::Wire *wire, int offset, int width = 1);
	SigSpec(const std::string &str);
	SigSpec(int val, int width = 32);
	SigSpec(RTLIL::State bit, int width = 1);
	SigSpec(RTLIL::SigBit bit, int width = 1);
	SigSpec(std::vector<RTLIL::SigChunk> chunks);
	SigSpec(std::vector<RTLIL::SigBit> bits);
	SigSpec(std::set<RTLIL::SigBit> bits);

	SigSpec(RTLIL::SigSpec &&other) {
		width_ = other.width_;
		hash_ = other.hash_;
		chunks_ = std::move(other.chunks_);
		bits_ = std::move(other.bits_);
	}

	const RTLIL::SigSpec &operator=(RTLIL::SigSpec &&other) {
		width_ = other.width_;
		hash_ = other.hash_;
		chunks_ = std::move(other.chunks_);
		bits_ = std::move(other.bits_);
		return *this;
	}

	inline const std::vector<RTLIL::SigChunk> &chunks() const { pack(); return chunks_; }
	inline const std::vector<RTLIL::SigBit> &bits() const { inline_unpack(); return bits_; }

	inline int size() const { return width_; }

	inline RTLIL::SigBit &operator[](int index) { inline_unpack(); return bits_.at(index); }
	inline const RTLIL::SigBit &operator[](int index) const { inline_unpack(); return bits_.at(index); }

	inline RTLIL::SigSpecIterator begin() { RTLIL::SigSpecIterator it; it.sig_p = this; it.index = 0; return it; }
	inline RTLIL::SigSpecIterator end() { RTLIL::SigSpecIterator it; it.sig_p = this; it.index = width_; return it; }

	inline RTLIL::SigSpecConstIterator begin() const { RTLIL::SigSpecConstIterator it; it.sig_p = this; it.index = 0; return it; }
	inline RTLIL::SigSpecConstIterator end() const { RTLIL::SigSpecConstIterator it; it.sig_p = this; it.index = width_; return it; }

	void sort();
	void sort_and_unify();

	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with);
	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const;
	void replace(int offset, const RTLIL::SigSpec &with);

	void remove(const RTLIL::SigSpec &pattern);
	void remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const;
	void remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other);
	void remove(int offset, int length = 1);
	void remove_const();

	RTLIL::SigSpec extract(RTLIL::SigSpec pattern, const RTLIL::SigSpec *other = NULL) const;
	RTLIL::SigSpec extract(int offset, int length = 1) const;

	void append(const RTLIL::SigSpec &signal);
	void append_bit(const RTLIL::SigBit &bit);

	void extend(int width, bool is_signed = false);
	void extend_u0(int width, bool is_signed = false);

	RTLIL::SigSpec repeat(int num) const;

	bool operator <(const RTLIL::SigSpec &other) const;
	bool operator ==(const RTLIL::SigSpec &other) const;
	inline bool operator !=(const RTLIL::SigSpec &other) const { return !(*this == other); }

	bool is_wire() const;
	bool is_chunk() const;

	bool is_fully_const() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool has_marked_bits() const;

	bool as_bool() const;
	int as_int() const;
	std::string as_string() const;
	RTLIL::Const as_const() const;
	RTLIL::Wire *as_wire() const;
	RTLIL::SigChunk as_chunk() const;

	bool match(std::string pattern) const;

	std::set<RTLIL::SigBit> to_sigbit_set() const;
	std::vector<RTLIL::SigBit> to_sigbit_vector() const;
	RTLIL::SigBit to_single_sigbit() const;

	static bool parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
	static bool parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str);
	static bool parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);

	operator std::vector<RTLIL::SigChunk>() const { return chunks(); }
	operator std::vector<RTLIL::SigBit>() const { return bits(); }

#ifndef NDEBUG
	void check() const;
#else
	inline void check() const { }
#endif
};

inline RTLIL::SigBit &RTLIL::SigSpecIterator::operator*() const {
	return (*sig_p)[index];
}

inline const RTLIL::SigBit &RTLIL::SigSpecConstIterator::operator*() const {
	return (*sig_p)[index];
}

inline RTLIL::SigBit::SigBit(const RTLIL::SigSpec &sig) {
	log_assert(sig.size() == 1 && sig.chunks().size() == 1);
	*this = SigBit(sig.chunks().front());
}

struct RTLIL::CaseRule
{
	std::vector<RTLIL::SigSpec> compare;
	std::vector<RTLIL::SigSig> actions;
	std::vector<RTLIL::SwitchRule*> switches;

	~CaseRule();
	void optimize();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::CaseRule *clone() const;
};

struct RTLIL::SwitchRule
{
	RTLIL::SigSpec signal;
	RTLIL_ATTRIBUTE_MEMBERS
	std::vector<RTLIL::CaseRule*> cases;

	~SwitchRule();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::SwitchRule *clone() const;
};

struct RTLIL::SyncRule
{
	RTLIL::SyncType type;
	RTLIL::SigSpec signal;
	std::vector<RTLIL::SigSig> actions;

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::SyncRule *clone() const;
};

struct RTLIL::Process
{
	RTLIL::IdString name;
	RTLIL_ATTRIBUTE_MEMBERS
	RTLIL::CaseRule root_case;
	std::vector<RTLIL::SyncRule*> syncs;

	~Process();

	template<typename T> void rewrite_sigspecs(T functor);
	RTLIL::Process *clone() const;
};

template<typename T>
void RTLIL::Module::rewrite_sigspecs(T functor)
{
	for (auto &it : cells_)
		it.second->rewrite_sigspecs(functor);
	for (auto &it : processes)
		it.second->rewrite_sigspecs(functor);
	for (auto &it : connections_) {
		functor(it.first);
		functor(it.second);
	}
}

template<typename T>
void RTLIL::Cell::rewrite_sigspecs(T functor) {
	for (auto &it : connections_)
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

YOSYS_NAMESPACE_END

#endif
