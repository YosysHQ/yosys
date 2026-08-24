/* -*- c++ -*-
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

#ifndef RTLIL_H
#define RTLIL_H

#include "kernel/yosys_common.h"
#include "kernel/yosys.h"
#include "kernel/twine.h"

#include <deque>
#include <string_view>
#include <unordered_map>

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
		STg = 6, // global clock
		STi = 7  // init
	};

	// Semantic metadata - how can this constant be interpreted?
	// Values may be generally non-exclusive
	enum ConstFlags : unsigned char {
		CONST_FLAG_NONE    = 0,
		CONST_FLAG_STRING  = 1,
		CONST_FLAG_SIGNED  = 2,  // only used for parameters
		CONST_FLAG_REAL    = 4,  // only used for parameters
		CONST_FLAG_UNSIZED = 8,  // only used for parameters
	};

	enum SelectPartials : unsigned char {
		SELECT_ALL = 0,          // include partial modules
		SELECT_WHOLE_ONLY = 1,   // ignore partial modules
		SELECT_WHOLE_WARN = 2,   // call log_warning on partial module
		SELECT_WHOLE_ERR = 3,    // call log_error on partial module
		SELECT_WHOLE_CMDERR = 4  // call log_cmd_error on partial module
	};

	enum SelectBoxes : unsigned char {
		SB_ALL = 0,            // include boxed modules
		SB_WARN = 1,           // helper for log_warning (not for direct use)
		SB_ERR = 2,            // helper for log_error (not for direct use)
		SB_CMDERR = 3,         // helper for log_cmd_error (not for direct use)
		SB_UNBOXED_ONLY = 4,   // ignore boxed modules
		SB_UNBOXED_WARN = 5,   // call log_warning on boxed module
		SB_UNBOXED_ERR = 6,    // call log_error on boxed module
		SB_UNBOXED_CMDERR = 7, // call log_cmd_error on boxed module
		SB_INCL_WB = 8,        // helper for white boxes (not for direct use)
		SB_EXCL_BB_ONLY = 12,  // ignore black boxes, but not white boxes
		SB_EXCL_BB_WARN = 13,  // call log_warning on black boxed module
		SB_EXCL_BB_ERR = 14,   // call log_error on black boxed module
		SB_EXCL_BB_CMDERR = 15 // call log_cmd_error on black boxed module
	};

	enum PortDir : unsigned char  {
		PD_UNKNOWN = 0,
		PD_INPUT = 1,
		PD_OUTPUT = 2,
		PD_INOUT = 3
	};

	// Maximum width in bits of RTLIL::Wire or RTLIL::Const
	constexpr int WIDTH_LIMIT = 1 << 30;

	struct Const;
	struct AttrObject;
	struct NamedObject;
	struct Selection;
	struct Monitor;
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
	struct MemWriteAction;
	struct SyncRule;
	struct Process;
	struct Binding;

	typedef std::pair<SigSpec, SigSpec> SigSig;
};

struct SigMap;


namespace RTLIL { using YOSYS_NAMESPACE_PREFIX ID; }
namespace RTLIL { using YOSYS_NAMESPACE_PREFIX IdString; }

namespace RTLIL {
	void copy_attr_dict(dict<IdString, RTLIL::Const> &dst,
			const dict<IdString, RTLIL::Const> &src,
			const RTLIL::Design *src_design, RTLIL::Design *dst_design);

	extern dict<std::string, std::string> constpad;

	[[deprecated("use StaticCellTypes::categories.is_ff() instead")]]
	const pool<IdString> &builtin_ff_cell_types();

	static inline std::string escape_id(const std::string &str) {
		if (str.size() > 0 && str[0] != '\\' && str[0] != '$')
			return "\\" + str;
		return str;
	}

	static inline std::string unescape_id(const std::string &str) {
		if (str.size() < 2)
			return str;
		if (str[0] != '\\')
			return str;
		if (str[1] == '$' || str[1] == '\\')
			return str;
		if (str[1] >= '0' && str[1] <= '9')
			return str;
		return str.substr(1);
	}

	template <typename T> struct sort_by_name_id {
		bool operator()(T *a, T *b) const {
			return a->name < b->name;
		}
	};

	template <typename T> struct sort_by_name_str {
		bool operator()(T *a, T *b) const {
			return a->name.lt_by_name(b->name);
		}
	};

	struct sort_by_id_str {
		const TwinePool& pool;
		explicit sort_by_id_str(const TwinePool& pool) : pool(pool) {}
		bool operator()(RTLIL::IdString a, RTLIL::IdString b) const {
			return pool.compare_by_name(a, b) < 0;
		}
	};

	static inline std::string encode_filename(const std::string &filename)
	{
		std::stringstream val;
		if (!std::any_of(filename.begin(), filename.end(), [](char c) {
			return static_cast<unsigned char>(c) < 33 || static_cast<unsigned char>(c) > 126;
		})) return filename;
		for (unsigned char const c : filename) {
			if (c < 33 || c > 126)
				val << stringf("$%02x", c);
			else
				val << c;
		}
		return val.str();
	}

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
	RTLIL::Const const_divfloor    (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_modfloor    (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_mod         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_pow         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_pos         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_buf         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);
	RTLIL::Const const_neg         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_mux         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);
	RTLIL::Const const_pmux        (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);
	RTLIL::Const const_bmux        (const RTLIL::Const &arg1, const RTLIL::Const &arg2);
	RTLIL::Const const_demux       (const RTLIL::Const &arg1, const RTLIL::Const &arg2);

	RTLIL::Const const_bweqx       (const RTLIL::Const &arg1, const RTLIL::Const &arg2);
	RTLIL::Const const_bwmux       (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);


	// This iterator-range-pair is used for Design::modules(), Module::wires() and Module::cells().
	// It maintains a reference counter that is used to make sure that the container is not modified while being iterated over.

	template<typename T, typename Key = IdString>
	struct ObjIterator {
		using iterator_category = std::forward_iterator_tag;
		using value_type = T;
		using difference_type = ptrdiff_t;
		using pointer = T*;
		using reference = T&;
		typename dict<Key, T>::iterator it;
		dict<Key, T> *list_p;
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

		ObjIterator(const RTLIL::ObjIterator<T, Key> &other) {
			it = other.it;
			list_p = other.list_p;
			refcount_p = other.refcount_p;
			if (refcount_p)
				(*refcount_p)++;
		}

		ObjIterator &operator=(const RTLIL::ObjIterator<T, Key> &other) {
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

		inline bool operator!=(const RTLIL::ObjIterator<T, Key> &other) const {
			if (list_p == nullptr || other.list_p == nullptr)
				return list_p != other.list_p;
			return it != other.it;
		}


		inline bool operator==(const RTLIL::ObjIterator<T, Key> &other) const {
			return !(*this != other);
		}

		inline ObjIterator<T, Key>& operator++() {
			log_assert(list_p != nullptr);
			if (++it == list_p->end()) {
				(*refcount_p)--;
				list_p = nullptr;
				refcount_p = nullptr;
			}
			return *this;
		}

		inline ObjIterator<T, Key>& operator+=(int amt) {
			log_assert(list_p != nullptr);
			it += amt;
			if (it == list_p->end()) {
				(*refcount_p)--;
				list_p = nullptr;
				refcount_p = nullptr;
			}
			return *this;
		}

		inline ObjIterator<T, Key> operator+(int amt) {
			log_assert(list_p != nullptr);
			ObjIterator<T, Key> new_obj(*this);
			new_obj.it += amt;
			if (new_obj.it == list_p->end()) {
				(*(new_obj.refcount_p))--;
				new_obj.list_p = nullptr;
				new_obj.refcount_p = nullptr;
			}
			return new_obj;
		}

		inline const ObjIterator<T, Key> operator++(int) {
			ObjIterator<T, Key> result(*this);
			++(*this);
			return result;
		}
	};

	template<typename T, typename Key = IdString>
	struct ObjRange
	{
		dict<Key, T> *list_p;
		int *refcount_p;

		ObjRange(decltype(list_p) list_p, int *refcount_p) : list_p(list_p), refcount_p(refcount_p) { }
		RTLIL::ObjIterator<T, Key> begin() { return RTLIL::ObjIterator<T, Key>(list_p, refcount_p); }
		RTLIL::ObjIterator<T, Key> end() { return RTLIL::ObjIterator<T, Key>(); }

		size_t size() const {
			return list_p->size();
		}

		operator pool<T>() const {
			pool<T> result;
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

		pool<T> to_pool() const { return *this; }
		std::vector<T> to_vector() const { return *this; }
	};
};

struct RTLIL::Const
{
	short int flags;
private:
	friend class KernelRtlilTest;
	FRIEND_TEST(KernelRtlilTest, ConstStr);
	using bitvectype = std::vector<RTLIL::State>;
	enum class backing_tag: bool { bits, string };
	// Do not access the union or tag even in Const methods unless necessary
	backing_tag tag;
	union {
		bitvectype bits_;
		std::string str_;
	};

	// Use these private utilities instead
	bool is_bits() const { return tag == backing_tag::bits; }
	bool is_str() const { return tag == backing_tag::string; }

	bitvectype* get_if_bits() { return is_bits() ? &bits_ : NULL; }
	std::string* get_if_str() { return is_str() ? &str_ : NULL; }
	const bitvectype* get_if_bits() const { return is_bits() ? &bits_ : NULL; }
	const std::string* get_if_str() const { return is_str() ? &str_ : NULL; }

	bitvectype& get_bits();
	std::string& get_str();
	const bitvectype& get_bits() const;
	const std::string& get_str() const;
	std::vector<RTLIL::State>& bits_internal();
	void bitvectorize_internal();

public:
	Const() : flags(RTLIL::CONST_FLAG_NONE), tag(backing_tag::bits), bits_(std::vector<RTLIL::State>()) {}
	Const(std::string str);
	Const(long long val); // default width is 32
	Const(long long val, int width);
	Const(RTLIL::State bit, int width = 1);
	Const(std::vector<RTLIL::State> bits) : flags(RTLIL::CONST_FLAG_NONE), tag(backing_tag::bits), bits_(std::move(bits)) {}
	Const(const std::vector<bool> &bits);
	Const(const RTLIL::Const &other);
	Const(RTLIL::Const &&other);
	RTLIL::Const &operator =(const RTLIL::Const &other);
	~Const();

	struct Builder
	{
		Builder() {}
		Builder(int expected_width) { bits.reserve(expected_width); }
		void push_back(RTLIL::State b) { bits.push_back(b); }
		int size() const { return static_cast<int>(bits.size()); }
		Const build() { return Const(std::move(bits)); }
	private:
		std::vector<RTLIL::State> bits;
	};

	bool operator <(const RTLIL::Const &other) const;
	bool operator ==(const RTLIL::Const &other) const;
	bool operator !=(const RTLIL::Const &other) const;

	[[deprecated("Don't use direct access to the internal std::vector<State>, that's an implementation detail.")]]
	std::vector<RTLIL::State>& bits() { return bits_internal(); }
	[[deprecated("Don't call bitvectorize() directly, it's an implementation detail.")]]
	void bitvectorize() const { const_cast<Const*>(this)->bitvectorize_internal(); }

	bool as_bool() const;

	// Convert the constant value to a C++ int.
	// NOTE: If the constant is too wide to fit in int (32 bits) this will
	// truncate any higher bits, potentially over/underflowing. Consider using
	// try_as_int, as_int_saturating, or guarding behind convertible_to_int
	// instead.
	int as_int(bool is_signed = false) const;

	// Returns true iff the constant can be converted to an int without
	// over/underflow.
	bool convertible_to_int(bool is_signed = false) const;

	// Returns the constant's value as an int if it can be represented without
	// over/underflow, or std::nullopt otherwise.
	std::optional<int> try_as_int(bool is_signed = false) const;

	// Returns the constant's value as an int if it can be represented without
	// over/underflow, otherwise the max/min value for int depending on the sign.
	int as_int_saturating(bool is_signed = false) const;

	void tag_bare_integer_const(const std::string &value);

	std::string as_string(const char* any = "-") const;
	static Const from_string(const std::string &str);
	std::vector<RTLIL::State> to_bits() const;

	std::string decode_string() const;
	int size() const;
	bool empty() const;

	void append(const RTLIL::Const &other);
	void set(int i, RTLIL::State state) {
		bits_internal()[i] = state;
	}
	void resize(int size, RTLIL::State fill) {
    log_assert(size >= 0 && size < RTLIL::WIDTH_LIMIT);
		bits_internal().resize(size, fill);
	}

	class const_iterator {
	private:
		const Const* parent;
		size_t idx;

	public:
		using iterator_category = std::bidirectional_iterator_tag;
		using value_type = State;
		using difference_type = std::ptrdiff_t;
		using pointer = const State*;
		using reference = const State&;

		const_iterator(const Const& c, size_t i) : parent(&c), idx(i) {}

		State operator*() const;

		const_iterator& operator++() { ++idx; return *this; }
		const_iterator& operator--() { --idx; return *this; }
		const_iterator operator++(int) { const_iterator result(*this); ++idx; return result; }
		const_iterator operator--(int) { const_iterator result(*this); --idx; return result; }
		const_iterator& operator+=(int i) { idx += i; return *this; }

		const_iterator operator+(int add) {
			return const_iterator(*parent, idx + add);
		}
		const_iterator operator-(int sub) {
			return const_iterator(*parent, idx - sub);
		}
		int operator-(const const_iterator& other) {
			return idx - other.idx;
		}

		bool operator==(const const_iterator& other) const {
			return idx == other.idx;
		}

		bool operator!=(const const_iterator& other) const {
			return !(*this == other);
		}
	};

	class iterator {
	private:
		Const* parent;
		size_t idx;

	public:
		class proxy {
		private:
			Const* parent;
			size_t idx;
		public:
			proxy(Const* parent, size_t idx) : parent(parent), idx(idx) {}
			operator State() const { return (*parent)[idx]; }
			proxy& operator=(State s) { parent->set(idx, s); return *this; }
			proxy& operator=(const proxy& other) { parent->set(idx, (*other.parent)[other.idx]); return *this; }
		};

		using iterator_category = std::bidirectional_iterator_tag;
		using value_type = State;
		using difference_type = std::ptrdiff_t;
		using pointer = proxy*;
		using reference = proxy;

		iterator(Const& c, size_t i) : parent(&c), idx(i) {}

		proxy operator*() const { return proxy(parent, idx); }
		iterator& operator++() { ++idx; return *this; }
		iterator& operator--() { --idx; return *this; }
		iterator operator++(int) { iterator result(*this); ++idx; return result; }
		iterator operator--(int) { iterator result(*this); --idx; return result; }
		iterator& operator+=(int i) { idx += i; return *this; }

		iterator operator+(int add) {
			return iterator(*parent, idx + add);
		}
		iterator operator-(int sub) {
			return iterator(*parent, idx - sub);
		}
		int operator-(const iterator& other) {
			return idx - other.idx;
		}

		bool operator==(const iterator& other) const {
			return idx == other.idx;
		}

		bool operator!=(const iterator& other) const {
			return !(*this == other);
		}
	};

	const_iterator begin() const {
		return const_iterator(*this, 0);
	}
	const_iterator end() const {
		return const_iterator(*this, size());
	}
	iterator begin() {
		return iterator(*this, 0);
	}
	iterator end() {
		return iterator(*this, size());
	}
	State back() const {
		return *(end() - 1);
	}
	State front() const {
		return *begin();
	}
	State at(size_t i) const {
		return *const_iterator(*this, i);
	}
	State operator[](size_t i) const {
		return *const_iterator(*this, i);
	}

	bool is_fully_zero() const;
	bool is_fully_ones() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool is_fully_undef_x_only() const;
	bool is_onehot(int *pos = nullptr) const;

	RTLIL::Const extract(int offset, int len = 1, RTLIL::State padding = RTLIL::State::S0) const;

	// find the MSB without redundant leading bits
	int get_min_size(bool is_signed) const;

	// compress representation to the minimum required bits
	void compress(bool is_signed = false);

	std::optional<int> as_int_compress(bool is_signed) const;

	void extu(int width) {
		resize(width, RTLIL::State::S0);
	}

	void exts(int width) {
		resize(width, empty() ? RTLIL::State::Sx : back());
	}

	[[nodiscard]] Hasher hash_into(Hasher h) const;
};

struct RTLIL::AttrObject
{
	dict<RTLIL::IdString, RTLIL::Const> attributes;

	bool has_attribute(RTLIL::IdString id) const;

	void set_bool_attribute(RTLIL::IdString id, bool value=true);
	bool get_bool_attribute(RTLIL::IdString id) const;

	[[deprecated("Use Module::get_blackbox_attribute() instead.")]]
	bool get_blackbox_attribute(bool ignore_wb=false) const {
		return get_bool_attribute(ID::blackbox) || (!ignore_wb && get_bool_attribute(ID::whitebox));
	}

	void set_string_attribute(IdString id, string value);
	string get_string_attribute(RTLIL::IdString id) const;

	void set_strpool_attribute(RTLIL::IdString id, const pool<string> &data);
	void add_strpool_attribute(RTLIL::IdString id, const pool<string> &data);
	pool<string> get_strpool_attribute(RTLIL::IdString id) const;

	void set_src_attribute(const std::string &src) {
		set_string_attribute(ID::src, src);
	}
	std::string get_src_attribute() const {
		return get_string_attribute(ID::src);
	}

	void set_hdlname_attribute(const vector<string> &hierarchy);
	vector<string> get_hdlname_attribute() const;

	void set_intvec_attribute(IdString id, const vector<int> &data);
	vector<int> get_intvec_attribute(RTLIL::IdString id) const;
};

struct RTLIL::NamedObject : public RTLIL::AttrObject
{
	IdString name_ = IdString::Null;
};

#include "kernel/rtlil_twine_compat.h"

struct RTLIL::SigChunk
{
	RTLIL::Wire *wire;
	std::vector<RTLIL::State> data; // only used if wire == NULL, LSB at index 0
	int width, offset;

	SigChunk() : wire(nullptr), width(0), offset(0) {}
	SigChunk(const RTLIL::Const &value) : wire(nullptr), data(value.to_bits()), width(GetSize(data)), offset(0) {}
	SigChunk(RTLIL::Const &&value) : wire(nullptr), data(value.to_bits()), width(GetSize(data)), offset(0) {}
	SigChunk(RTLIL::Wire *wire) : wire(wire), width(GetSize(wire)), offset(0) {}
	SigChunk(RTLIL::Wire *wire, int offset, int width = 1) : wire(wire), width(width), offset(offset) {}
	SigChunk(const std::string &str) : SigChunk(RTLIL::Const(str)) {}
	SigChunk(int val) /*default width 32*/ : SigChunk(RTLIL::Const(val)) {}
	SigChunk(int val, int width) : SigChunk(RTLIL::Const(val, width)) {}
	SigChunk(RTLIL::State bit, int width = 1) : SigChunk(RTLIL::Const(bit, width)) {}
	SigChunk(const RTLIL::SigBit &bit);

	RTLIL::SigChunk extract(int offset, int length) const;
	RTLIL::SigBit operator[](int offset) const;
	inline int size() const { return width; }
	inline bool is_wire() const { return wire != NULL; }

	bool operator <(const RTLIL::SigChunk &other) const;
	bool operator ==(const RTLIL::SigChunk &other) const;
	bool operator !=(const RTLIL::SigChunk &other) const;
};

struct RTLIL::SigBit
{
	RTLIL::Wire *wire;
	union {
		RTLIL::State data; // used if wire == NULL
		int offset;        // used if wire != NULL
	};

	SigBit();
	SigBit(RTLIL::State bit);
	explicit SigBit(bool bit);
	SigBit(RTLIL::Wire *wire);
	SigBit(RTLIL::Wire *wire, int offset);
	SigBit(const RTLIL::SigChunk &chunk);
	SigBit(const RTLIL::SigChunk &chunk, int index);
	SigBit(const RTLIL::SigSpec &sig);
	SigBit(const RTLIL::SigBit &sigbit) = default;
	RTLIL::SigBit &operator =(const RTLIL::SigBit &other) = default;

	inline bool is_wire() const { return wire != NULL; }

	bool operator <(const RTLIL::SigBit &other) const;
	bool operator ==(const RTLIL::SigBit &other) const;
	bool operator !=(const RTLIL::SigBit &other) const;
	[[nodiscard]] Hasher hash_into(Hasher h) const;
	[[nodiscard]] Hasher hash_top() const;
};

namespace hashlib {
	template <>
	struct hash_ops<RTLIL::SigBit> {
		static inline bool cmp(const RTLIL::SigBit &a, const RTLIL::SigBit &b) {
			return a == b;
		}
		[[nodiscard]] static inline Hasher hash(const RTLIL::SigBit sb) {
			return sb.hash_top();
		}
		[[nodiscard]] static inline Hasher hash_into(const RTLIL::SigBit sb, Hasher h) {
			return sb.hash_into(h);
		}
	};
};

struct RTLIL::SigSpecIterator
{
	typedef std::input_iterator_tag iterator_category;
	typedef RTLIL::SigBit value_type;
	typedef ptrdiff_t difference_type;
	typedef RTLIL::SigBit* pointer;
	typedef RTLIL::SigBit& reference;

	RTLIL::SigSpec *sig_p;
	int index;

	inline RTLIL::SigBit &operator*() const;
	inline bool operator!=(const RTLIL::SigSpecIterator &other) const { return index != other.index; }
	inline bool operator==(const RTLIL::SigSpecIterator &other) const { return index == other.index; }
	inline void operator++() { index++; }
};

struct RTLIL::SigSpecConstIterator
{
	typedef std::input_iterator_tag iterator_category;
	typedef RTLIL::SigBit value_type;
	typedef ptrdiff_t difference_type;
	typedef RTLIL::SigBit* pointer;
	typedef RTLIL::SigBit& reference;

	const RTLIL::SigSpec *sig_p;
	RTLIL::SigBit bit;
	int index;

	inline const RTLIL::SigBit &operator*();
	inline bool operator!=(const RTLIL::SigSpecConstIterator &other) const { return index != other.index; }
	inline bool operator==(const RTLIL::SigSpecIterator &other) const { return index == other.index; }
	inline void operator++() { index++; }
};

struct RTLIL::SigSpec
{
private:
	friend class SigSpecRepTest;
	FRIEND_TEST(SigSpecRepTest, Extract);
	enum Representation : char {
		CHUNK,
		BITS,
	};
	// An AtomicHash is either clear or a nonzero integer.
	struct AtomicHash {
		// Create an initially clear value.
		AtomicHash() : atomic_(0) {}
		AtomicHash(const AtomicHash &rhs) : atomic_(rhs.load()) {}
		AtomicHash &operator=(const AtomicHash &rhs) { store(rhs.load()); return *this; }
		// Read the hash. Returns nullopt if the hash is clear.
		std::optional<Hasher::hash_t> read() const {
			Hasher::hash_t value = load();
			if (value == 0)
				return std::nullopt;
			return value;
		}
		// Set the hash. If the value is already set, then the new value must
		// equal the current value.
		void set(Hasher::hash_t value) const {
			log_assert(value != 0);
			Hasher::hash_t old = const_cast<std::atomic<Hasher::hash_t>&>(atomic_)
					.exchange(value, std::memory_order_relaxed);
			log_assert(old == 0 || old == value);
		}
		void clear() { store(0); }
	private:
		int load() const { return atomic_.load(std::memory_order_relaxed); }
		void store(Hasher::hash_t value) const {
			const_cast<std::atomic<Hasher::hash_t>&>(atomic_).store(value, std::memory_order_relaxed);
		}

		std::atomic<Hasher::hash_t> atomic_;
	};

	Representation rep_;
	AtomicHash hash_;
	union {
		RTLIL::SigChunk chunk_;
		std::vector<RTLIL::SigBit> bits_; // LSB at index 0
	};

	void init_empty_bits() {
		rep_ = BITS;
		new (&bits_) std::vector<RTLIL::SigBit>;
	}

	void unpack();
	inline void inline_unpack() {
		if (rep_ == CHUNK)
			unpack();
	}
	void try_repack();

	Hasher::hash_t updhash() const;
	void destroy() {
		if (rep_ == CHUNK)
			chunk_.~SigChunk();
		else
			bits_.~vector();
	}
	friend struct Chunks;

public:
	SigSpec() { init_empty_bits(); }
	SigSpec(std::initializer_list<RTLIL::SigSpec> parts);
	SigSpec(const SigSpec &value) : rep_(value.rep_), hash_(value.hash_) {
		if (value.rep_ == CHUNK)
			new (&chunk_) RTLIL::SigChunk(value.chunk_);
		else
			new (&bits_) std::vector<RTLIL::SigBit>(value.bits_);
	}
	SigSpec(SigSpec &&value) : rep_(value.rep_), hash_(value.hash_) {
		if (value.rep_ == CHUNK)
			new (&chunk_) RTLIL::SigChunk(std::move(value.chunk_));
		else
			new (&bits_) std::vector<RTLIL::SigBit>(std::move(value.bits_));
	}
	SigSpec(const RTLIL::Const &value);
	SigSpec(RTLIL::Const &&value);
	SigSpec(const RTLIL::SigChunk &chunk);
	SigSpec(RTLIL::SigChunk &&chunk);
	SigSpec(RTLIL::Wire *wire);
	SigSpec(RTLIL::Wire *wire, int offset, int width = 1);
	SigSpec(const std::string &str);
	SigSpec(int val, int width = 32);
	SigSpec(RTLIL::State bit, int width = 1);
	SigSpec(const RTLIL::SigBit &bit, int width = 1);
	SigSpec(const std::vector<RTLIL::SigChunk> &chunks);
	SigSpec(const std::vector<RTLIL::SigBit> &bits);
	SigSpec(const pool<RTLIL::SigBit> &bits);
	SigSpec(const std::set<RTLIL::SigBit> &bits);
	explicit SigSpec(bool bit);
	~SigSpec() {
		destroy();
	}

	SigSpec &operator=(const SigSpec &rhs) {
		destroy();
		rep_ = rhs.rep_;
		hash_ = rhs.hash_;
		if (rep_ == CHUNK)
			new (&chunk_) RTLIL::SigChunk(rhs.chunk_);
		else
			new (&bits_) std::vector<RTLIL::SigBit>(rhs.bits_);
		return *this;
	}
	SigSpec &operator=(SigSpec &&rhs) {
		destroy();
		rep_ = rhs.rep_;
		hash_ = rhs.hash_;
		if (rep_ == CHUNK)
			new (&chunk_) RTLIL::SigChunk(std::move(rhs.chunk_));
		else
			new (&bits_) std::vector<RTLIL::SigBit>(std::move(rhs.bits_));
		return *this;
	}

	// SigSpec::Chunks holds one reconstructed chunk at a time
	// to provide the SigSpec::chunks() read-only chunks view
	// since vector<SigChunk> SigSpec::chunks_ has been removed
	struct Chunks {
		Chunks(const SigSpec &spec) : spec(spec) {}
		struct const_iterator {
			using iterator_category = std::forward_iterator_tag;
			using value_type = const SigChunk &;
			using difference_type = std::ptrdiff_t;
			using pointer = const SigChunk *;
			using reference = const SigChunk &;

			const SigSpec &spec;
			int bit_index;
			SigChunk chunk;

			const_iterator(const SigSpec &spec) : spec(spec) {
				bit_index = 0;
				if (spec.rep_ == BITS)
					next_chunk_bits();
			}
			enum End { END };
			const_iterator(const SigSpec &spec, End) : spec(spec) {
				bit_index = spec.size();
			}
			void next_chunk_bits();

			const SigChunk &operator*() {
				if (spec.rep_ == CHUNK)
					return spec.chunk_;
				return chunk;
			};
			const SigChunk *operator->() { return &**this; }
			const_iterator &operator++() {
				bit_index += (**this).width;
				if (spec.rep_ == BITS)
					next_chunk_bits();
				return *this;
			}
			bool operator==(const const_iterator &rhs) const { return bit_index == rhs.bit_index; }
			bool operator!=(const const_iterator &rhs) const { return !(*this == rhs); }
		};
		const_iterator begin() const { return const_iterator(spec); }
		const_iterator end() const {
			const_iterator it(spec, const_iterator::END);
			return it;
		}
		// Later we should deprecate these and remove their in-tree calls,
		// so we can eventually remove chunk_vector.
		std::vector<RTLIL::SigChunk>::const_reverse_iterator rbegin() {
			ensure_chunk_vector();
			return chunk_vector.rbegin();
		}
		std::vector<RTLIL::SigChunk>::const_reverse_iterator rend() {
			ensure_chunk_vector();
			return chunk_vector.rend();
		}
		int size() {
			ensure_chunk_vector();
			return chunk_vector.size();
		}
		int size() const {
			return std::distance(begin(), end());
		}
		const SigChunk &at(int index) {
			ensure_chunk_vector();
			return chunk_vector.at(index);
		}
		operator const std::vector<RTLIL::SigChunk>&() {
			ensure_chunk_vector();
			return chunk_vector;
		}
	private:
		void ensure_chunk_vector() {
			if (spec.size() > 0 && chunk_vector.empty()) {
				for (const RTLIL::SigChunk &c : *this)
					chunk_vector.push_back(c);
			}
		}
		const SigSpec &spec;
		std::vector<RTLIL::SigChunk> chunk_vector;
	};
	friend struct Chunks::const_iterator;

	inline Chunks chunks() const { return {*this}; }
	inline const SigSpec &bits() const { return *this; }

	inline int size() const { return rep_ == CHUNK ? chunk_.width : GetSize(bits_); }
	inline bool empty() const { return size() == 0; };

	inline RTLIL::SigBit &operator[](int index) { inline_unpack(); hash_.clear(); return bits_.at(index); }
	inline RTLIL::SigBit operator[](int index) const {
		if (rep_ == CHUNK) {
			if (index < 0 || index >= chunk_.width)
				throw std::out_of_range("SigSpec::operator[]");
			if (chunk_.wire)
				return RTLIL::SigBit(chunk_.wire, chunk_.offset + index);
			return RTLIL::SigBit(chunk_.data[index]);
		}
		return bits_.at(index);
	}

	inline RTLIL::SigSpecIterator begin() { RTLIL::SigSpecIterator it; it.sig_p = this; it.index = 0; return it; }
	inline RTLIL::SigSpecIterator end() { RTLIL::SigSpecIterator it; it.sig_p = this; it.index = size(); return it; }

	inline RTLIL::SigSpecConstIterator begin() const { RTLIL::SigSpecConstIterator it; it.sig_p = this; it.index = 0; return it; }
	inline RTLIL::SigSpecConstIterator end() const { RTLIL::SigSpecConstIterator it; it.sig_p = this; it.index = size(); return it; }

	void sort();
	void sort_and_unify();

	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with);
	void replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const;

	void replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules);
	void replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const;

	void replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules);
	void replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const;

	void replace(int offset, const RTLIL::SigSpec &with);

	void remove(const RTLIL::SigSpec &pattern);
	void remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const;
	void remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other);

	void remove(const pool<RTLIL::SigBit> &pattern);
	void remove(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other) const;
	void remove2(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other);
	void remove2(const std::set<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other);
	void remove2(const pool<RTLIL::Wire*> &pattern, RTLIL::SigSpec *other);

	void remove(int offset, int length = 1);
	void remove_const();

	RTLIL::SigSpec extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other = NULL) const;
	RTLIL::SigSpec extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other = NULL) const;
	RTLIL::SigSpec extract(int offset, int length = 1) const;
	RTLIL::SigSpec extract_end(int offset) const { return extract(offset, size() - offset); }

	void rewrite_wires(std::function<void(RTLIL::Wire*& wire)> rewrite);

	RTLIL::SigBit lsb() const { log_assert(size()); return (*this)[0]; };
	RTLIL::SigBit msb() const { log_assert(size()); return (*this)[size() - 1]; };
	RTLIL::SigBit front() const { return (*this)[0]; }
	RTLIL::SigBit back() const { return (*this)[size() - 1]; }

	void append(const RTLIL::SigSpec &signal);
	inline void append(Wire *wire) { append(RTLIL::SigSpec(wire)); }
	inline void append(const RTLIL::SigChunk &chunk) { append(RTLIL::SigSpec(chunk)); }
	inline void append(const RTLIL::Const &const_) { append(RTLIL::SigSpec(const_)); }

	void append(const RTLIL::SigBit &bit);
	inline void append(RTLIL::State state) { append(RTLIL::SigBit(state)); }
	inline void append(bool bool_) { append(RTLIL::SigBit(bool_)); }

	void extend_u0(int width, bool is_signed = false);

	RTLIL::SigSpec repeat(int num) const;

	void reverse() { inline_unpack(); std::reverse(bits_.begin(), bits_.end()); }

	bool operator <(const RTLIL::SigSpec &other) const;
	bool operator ==(const RTLIL::SigSpec &other) const;
	inline bool operator !=(const RTLIL::SigSpec &other) const { return !(*this == other); }

	bool is_wire() const;
	bool is_chunk() const;
	inline bool is_bit() const { return size() == 1; }

	bool known_driver() const;

	bool is_fully_const() const;
	bool is_fully_zero() const;
	bool is_fully_ones() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool has_const() const;
	bool has_const(State state) const;
	bool has_marked_bits() const;
	bool is_onehot(int *pos = nullptr) const;

	bool as_bool() const;

	// Convert the SigSpec to a C++ int, assuming all bits are constant.
	// NOTE: If the value is too wide to fit in int (32 bits) this will
	// truncate any higher bits, potentially over/underflowing. Consider using
	// try_as_int, as_int_saturating, or guarding behind convertible_to_int
	// instead.
	int as_int(bool is_signed = false) const;

	// Returns true iff the SigSpec is constant and can be converted to an int
	// without over/underflow.
	bool convertible_to_int(bool is_signed = false) const;

	// Returns the SigSpec's value as an int if it is a constant and can be
	// represented without over/underflow, or std::nullopt otherwise.
	std::optional<int> try_as_int(bool is_signed = false) const;

	// Returns an all constant SigSpec's value as an int if it can be represented
	// without over/underflow, otherwise the max/min value for int depending on
	// the sign.
	int as_int_saturating(bool is_signed = false) const;

	std::string as_string() const;
	// Returns std::nullopt if there are any non-constant bits. Returns an empty
	// Const if this has zero width.
	std::optional<RTLIL::Const> try_as_const() const;
	RTLIL::Const as_const() const;
	RTLIL::Wire *as_wire() const;
	RTLIL::SigChunk as_chunk() const;
	RTLIL::SigBit as_bit() const;

	bool match(const char* pattern) const;

	std::set<RTLIL::SigBit> to_sigbit_set() const;
	pool<RTLIL::SigBit> to_sigbit_pool() const;
	std::vector<RTLIL::SigBit> to_sigbit_vector() const;
	std::map<RTLIL::SigBit, RTLIL::SigBit> to_sigbit_map(const RTLIL::SigSpec &other) const;
	dict<RTLIL::SigBit, RTLIL::SigBit> to_sigbit_dict(const RTLIL::SigSpec &other) const;

	static bool parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);
	static bool parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str);
	static bool parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str);

	operator std::vector<RTLIL::SigChunk>() const;
	operator std::vector<RTLIL::SigBit>() const { return to_sigbit_vector(); }
	const RTLIL::SigBit &at(int offset, const RTLIL::SigBit &defval) { return offset < size() ? (*this)[offset] : defval; }
	RTLIL::SigBit& at(int offset) { return (*this)[offset]; }
	RTLIL::SigBit at(int offset) const { return (*this)[offset]; }

	[[nodiscard]] Hasher hash_into(Hasher h) const {
		Hasher::hash_t val;
		if (std::optional<Hasher::hash_t> current = hash_.read())
			val = *current;
		else
			val = updhash();
		h.eat(val);
		return h;
	}

#ifndef NDEBUG
	void check(const Module *mod = nullptr) const;
#else
	void check(const Module *mod = nullptr) const { (void)mod; }
#endif
};

struct RTLIL::Selection
{
	// selection includes boxed modules
	bool selects_boxes;
	// selection covers full design, including boxed modules
	bool complete_selection;
	// selection covers full design, not including boxed modules
	bool full_selection;
	pool<RTLIL::IdString> selected_modules;
	dict<RTLIL::IdString, pool<RTLIL::IdString>> selected_members;
	RTLIL::Design *current_design;

	// create a new selection
	Selection(
		// should the selection cover the full design
		bool full = true,
		// should the selection include boxed modules
		bool boxes = false,
		// the design to select from
		RTLIL::Design *design = nullptr
	) :
		selects_boxes(boxes), complete_selection(full && boxes), full_selection(full && !boxes), current_design(design) { }

	// checks if the given module exists in the current design and is a
	// boxed module, warning the user if the current design is not set
	bool boxed_module(RTLIL::IdString mod_name) const;

	// checks if the given module is included in this selection
	bool selected_module(RTLIL::IdString mod_name) const;

	// checks if the given module is wholly included in this selection,
	// i.e. not partially selected
	bool selected_whole_module(RTLIL::IdString mod_name) const;

	// checks if the given member from the given module is included in this
	// selection
	bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;

	// optimizes this selection for the given design by:
	// - removing non-existent modules and members, any boxed modules and
	//   their members (if selection does not include boxes), and any
	//   partially selected modules with no selected members;
	// - marking partially selected modules as wholly selected if all
	//   members of that module are selected; and
	// - marking selection as a complete_selection if all modules in the
	//   given design are selected, or a full_selection if it does not
	//   include boxes.
	void optimize(RTLIL::Design *design);

	// checks if selection covers full design (may or may not include
	// boxed-modules)
	bool selects_all() const {
		return full_selection || complete_selection;
	}

	// add whole module to this selection
	template<typename T1> void select(T1 *module) {
		if (!selects_all() && selected_modules.count(module->name) == 0) {
			IdString name = module->name;
			selected_modules.insert(name);
			selected_members.erase(name);
			if (module->get_blackbox_attribute())
				selects_boxes = true;
		}
	}

	// add member of module to this selection
	template<typename T1, typename T2> void select(T1 *module, T2 *member) {
		if (!selects_all() && selected_modules.count(module->name_) == 0) {
			selected_members[module->name_].insert(member->name_);
			if (module->get_blackbox_attribute())
				selects_boxes = true;
		}
	}

	// checks if selection is empty
	bool empty() const {
		return !selects_all() && selected_modules.empty() && selected_members.empty();
	}

	// clear this selection, leaving it empty
	void clear();

	// create a new selection which is empty
	static Selection EmptySelection(RTLIL::Design *design = nullptr) { return Selection(false, false, design); };

	// create a new selection with all non-boxed modules
	static Selection FullSelection(RTLIL::Design *design = nullptr) { return Selection(true, false, design); };

	// create a new selection with all modules, including boxes
	static Selection CompleteSelection(RTLIL::Design *design = nullptr) { return Selection(true, true, design); };
};

struct RTLIL::Monitor
{
	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

	Monitor() {
		static unsigned int hashidx_count = 123456789;
		hashidx_count = mkhash_xorshift(hashidx_count);
		hashidx_ = hashidx_count;
	}

	virtual ~Monitor() { }
	virtual void notify_module_add(RTLIL::Module*) { }
	virtual void notify_module_del(RTLIL::Module*) { }
	virtual void notify_connect(RTLIL::Cell*, RTLIL::IdString, const RTLIL::SigSpec&, const RTLIL::SigSpec&) { }
	virtual void notify_connect(RTLIL::Module*, const RTLIL::SigSig&) { }
	virtual void notify_connect(RTLIL::Module*, const std::vector<RTLIL::SigSig>&) { }
	virtual void notify_blackout(RTLIL::Module*) { }
};

// Forward declaration; defined in preproc.h.
struct define_map_t;

template<typename N>
inline constexpr bool is_unpooled_name_v =
	std::is_same_v<std::decay_t<N>, TwineSpec> || std::is_same_v<std::decay_t<N>, TwineSpec::Leaf> ||
	std::is_same_v<std::decay_t<N>, TwineSpec::Suffix> || std::is_same_v<std::decay_t<N>, TwineSpec::AutoSuffix> ||
	std::is_same_v<std::decay_t<N>, std::string> ||
	std::is_same_v<std::decay_t<N>, const char*> || std::is_same_v<std::decay_t<N>, char*>;

#define YS_UNPOOLED_NAME(N) std::enable_if_t<is_unpooled_name_v<N>, int> = 0

// Forwarders from various string-representing types into a canonical IdString method

// Forwards _func(name, arg1...)
#define YS_NAME_FWD_POOL(_func, _pool) \
	template<typename N, typename... Rest, YS_UNPOOLED_NAME(N)> \
	decltype(auto) _func(N name, Rest&&... rest) \
		{ return _func(_pool.add(std::move(name)), std::forward<Rest>(rest)...); }

// Forwards _func(arg0, name, arg2...)
#define YS_NAME_FWD_2ND_POOL(_func, _pool) \
	template<typename T, typename N, YS_UNPOOLED_NAME(N)> \
	decltype(auto) _func(T &&first, N name) \
		{ return _func(std::forward<T>(first), _pool.add(std::move(name))); }

#define YS_NAME_FWD(_func) YS_NAME_FWD_POOL(_func, design->twines)
#define YS_NAME_FWD_2ND(_func) YS_NAME_FWD_2ND_POOL(_func, design->twines)

struct RTLIL::Design
{
	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

	pool<RTLIL::Monitor*> monitors;
	dict<std::string, std::string> scratchpad;

	bool flagBufferedNormalized = false;
	void bufNormalize(bool enable=true);

	int refcount_modules_;
	dict<RTLIL::IdString, RTLIL::Module*> modules_;
	std::vector<RTLIL::Binding*> bindings_;

	TwinePool twines;

	std::string obj_name(const RTLIL::NamedObject *obj) const {
		return twines.str(obj->name_);
	}

	void absorb_attrs(RTLIL::AttrObject *obj, dict<IdString, RTLIL::Const> &&buf);

	size_t gc_twines();

	std::vector<std::unique_ptr<AST::AstNode>> verilog_packages, verilog_globals;
	std::unique_ptr<define_map_t> verilog_defines;

	std::vector<RTLIL::Selection> selection_stack;
	dict<RTLIL::IdString, RTLIL::Selection> selection_vars;
	IdString selected_active_module;

	Design();
	~Design();

	RTLIL::ObjRange<RTLIL::Module*, IdString> modules();
	RTLIL::Module *module(RTLIL::IdString name);
	const RTLIL::Module *module(RTLIL::IdString name) const;
	RTLIL::Module *top_module() const;

	bool has(RTLIL::IdString id) const {
		return modules_.count(id) != 0;
	}

	void add(RTLIL::Module *module);
	void add(RTLIL::Binding *binding);

	RTLIL::Module *addModule(RTLIL::IdString name);
	YS_NAME_FWD_POOL(addModule, twines)
	void remove(RTLIL::Module *module);
	void rename(RTLIL::Module *module, RTLIL::IdString new_name);
	YS_NAME_FWD_2ND_POOL(rename, twines)

	void scratchpad_unset(const std::string &varname);

	void scratchpad_set_int(const std::string &varname, int value);
	void scratchpad_set_bool(const std::string &varname, bool value);
	void scratchpad_set_string(const std::string &varname, std::string value);

	int scratchpad_get_int(const std::string &varname, int default_value = 0) const;
	bool scratchpad_get_bool(const std::string &varname, bool default_value = false) const;
	std::string scratchpad_get_string(const std::string &varname, const std::string &default_value = std::string()) const;

	void sort();
	void sort_modules();
	void check();
	void optimize();

	void clone_into(RTLIL::Design *dst) const;

	// checks if the given module is included in the current selection
	bool selected_module(RTLIL::IdString mod_name) const;

	// checks if the given module is wholly included in the current
	// selection, i.e. not partially selected
	bool selected_whole_module(RTLIL::IdString mod_name) const;

	// checks if the given member from the given module is included in the
	// current selection
	bool selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const;

	// checks if the given module is included in the current selection
	bool selected_module(RTLIL::Module *mod) const;

	// checks if the given module is wholly included in the current
	// selection, i.e. not partially selected
	bool selected_whole_module(RTLIL::Module *mod) const;

	// push the given selection to the selection stack
	void push_selection(RTLIL::Selection sel);
	// push a new selection to the selection stack, with nothing selected
	void push_empty_selection();
	// push a new selection to the selection stack, with all non-boxed
	// modules selected
	void push_full_selection();
	// push a new selection to the selection stack, with all modules
	// selected including boxes
	void push_complete_selection();
	// pop the current selection from the stack, returning to a full
	// selection (no boxes) if the stack is empty
	void pop_selection();

	// get the current selection
	RTLIL::Selection &selection() {
		return selection_stack.back();
	}

	// get the current selection
	const RTLIL::Selection &selection() const {
		return selection_stack.back();
	}

	// is the current selection a full selection (no boxes)
	bool full_selection() const {
		return selection().full_selection;
	}

	// is the given module in the current selection
	template<typename T1> bool selected(T1 *module) const {
		return selected_module(module->name);
	}

	// is the given member of the given module in the current selection
	template<typename T1, typename T2> bool selected(T1 *module, T2 *member) const {
		return selected_member(module->name, member->name);
	}

	// add whole module to the current selection
	template<typename T1> void select(T1 *module) {
		RTLIL::Selection &sel = selection();
		sel.select(module);
	}

	// add member of module to the current selection
	template<typename T1, typename T2> void select(T1 *module, T2 *member) {
		RTLIL::Selection &sel = selection();
		sel.select(module, member);
	}


	// returns all selected modules
	std::vector<RTLIL::Module*> selected_modules(
		// controls if partially selected modules are included
		RTLIL::SelectPartials partials = SELECT_ALL,
		// controls if boxed modules are included
		RTLIL::SelectBoxes boxes = SB_UNBOXED_WARN
	) const;

	// returns all selected modules, and may include boxes
	std::vector<RTLIL::Module*> all_selected_modules() const { return selected_modules(SELECT_ALL, SB_ALL); }
	// returns all selected unboxed modules, silently ignoring any boxed
	// modules in the selection
	std::vector<RTLIL::Module*> selected_unboxed_modules() const { return selected_modules(SELECT_ALL, SB_UNBOXED_ONLY); }
	// returns all selected unboxed modules, warning the user if any boxed
	// modules have been ignored
	std::vector<RTLIL::Module*> selected_unboxed_modules_warn() const { return selected_modules(SELECT_ALL, SB_UNBOXED_WARN); }

	[[deprecated("Use select_unboxed_whole_modules() to maintain prior behaviour, or consider one of the other selected whole module helpers.")]]
	std::vector<RTLIL::Module*> selected_whole_modules() const { return selected_modules(SELECT_WHOLE_ONLY, SB_UNBOXED_WARN); }
	// returns all selected whole modules, silently ignoring partially
	// selected modules, and may include boxes
	std::vector<RTLIL::Module*> all_selected_whole_modules() const { return selected_modules(SELECT_WHOLE_ONLY, SB_ALL); }
	// returns all selected whole modules, warning the user if any partially
	// selected or boxed modules have been ignored; optionally includes
	// selected whole modules with the 'whitebox' attribute
	std::vector<RTLIL::Module*> selected_whole_modules_warn(
		// should whole modules with the 'whitebox' attribute be
		// included
		bool include_wb = false
	) const { return selected_modules(SELECT_WHOLE_WARN, include_wb ? SB_EXCL_BB_WARN : SB_UNBOXED_WARN); }
	// returns all selected unboxed whole modules, silently ignoring
	// partially selected or boxed modules
	std::vector<RTLIL::Module*> selected_unboxed_whole_modules() const { return selected_modules(SELECT_WHOLE_ONLY, SB_UNBOXED_ONLY); }
	// returns all selected unboxed whole modules, warning the user if any
	// partially selected or boxed modules have been ignored
	std::vector<RTLIL::Module*> selected_unboxed_whole_modules_warn() const { return selected_modules(SELECT_WHOLE_WARN, SB_UNBOXED_WARN); }

	static std::map<unsigned int, RTLIL::Design*> *get_all_designs(void);

	std::string to_rtlil_str(bool only_selected = true) const;
};

struct RTLIL::Module : public RTLIL::NamedObject
{
	friend struct RTLIL::Cell;
	friend struct RTLIL::Design;

	YS_NO_UNIQUE_ADDRESS RTLIL::ModuleNameMasq name;

	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

protected:
	void add(RTLIL::Wire *wire);
	void add(RTLIL::Cell *cell);
	void add(RTLIL::Process *process);

public:
	RTLIL::Design *design;
	pool<RTLIL::Monitor*> monitors;

	int refcount_wires_;
	int refcount_cells_;

	dict<RTLIL::IdString, RTLIL::Wire*> wires_;
	dict<RTLIL::IdString, RTLIL::Cell*> cells_;

	std::vector<RTLIL::SigSig>   connections_;
	std::vector<RTLIL::Binding*> bindings_;

	idict<RTLIL::IdString> avail_parameters;
	dict<RTLIL::IdString, RTLIL::Const> parameter_default_values;
	dict<RTLIL::IdString, RTLIL::Memory*> memories;
	dict<RTLIL::IdString, RTLIL::Process*> processes;

	Module();
	virtual ~Module();
	virtual RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, bool mayfail = false);
	virtual RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, const dict<RTLIL::IdString, RTLIL::Module*> &interfaces, const dict<RTLIL::IdString, RTLIL::IdString> &modports, bool mayfail = false);
	virtual size_t count_id(RTLIL::IdString id);
	virtual void expand_interfaces(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Module *> &local_interfaces);
	virtual bool reprocess_if_necessary(RTLIL::Design *design);

	virtual void sort();
	virtual void check();
	virtual void optimize();
	virtual void makeblackbox();

	bool get_blackbox_attribute(bool ignore_wb=false) const {
		return get_bool_attribute(ID::blackbox) || (!ignore_wb && get_bool_attribute(ID::whitebox));
	}

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	void new_connections(const std::vector<RTLIL::SigSig> &new_conn);
	const std::vector<RTLIL::SigSig> &connections() const;

	std::vector<RTLIL::IdString> ports;
	void fixup_ports();

	pool<RTLIL::Cell *> buf_norm_cell_queue;
	pool<pair<RTLIL::Cell *, RTLIL::IdString>> buf_norm_cell_port_queue;
	pool<RTLIL::Wire *> buf_norm_wire_queue;
	pool<RTLIL::Cell *> pending_deleted_cells;
	dict<RTLIL::Wire *, pool<RTLIL::Cell *>> buf_norm_connect_index;
	void bufNormalize();

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	void cloneInto(RTLIL::Module *new_mod) const;
	virtual RTLIL::Module *clone() const;
	virtual RTLIL::Module *clone(RTLIL::Design *dst) const;
	virtual RTLIL::Module *clone(RTLIL::Design *dst, IdString target_name) const;

	bool has_memories() const;
	bool has_processes() const;

	bool has_memories_warn() const;
	bool has_processes_warn() const;

	bool is_selected() const;
	bool is_selected_whole() const;

	std::vector<RTLIL::Wire*> selected_wires() const;
	std::vector<RTLIL::Cell*> selected_cells() const;
	std::vector<RTLIL::Memory*> selected_memories() const;
	std::vector<RTLIL::Process*> selected_processes() const;
	std::vector<RTLIL::NamedObject*> selected_members() const;

	template<typename T> bool selected(T *member) const {
		return design->selected_member(name_, member->name_);
	}

	RTLIL::Wire* wire(RTLIL::IdString id) {
		auto it = wires_.find(id);
		return it == wires_.end() ? nullptr : it->second;
	}
	RTLIL::Cell* cell(RTLIL::IdString id) {
		auto it = cells_.find(id);
		return it == cells_.end() ? nullptr : it->second;
	}

	const RTLIL::Wire* wire(RTLIL::IdString id) const{
		auto it = wires_.find(id);
		return it == wires_.end() ? nullptr : it->second;
	}
	const RTLIL::Cell* cell(RTLIL::IdString id) const {
		auto it = cells_.find(id);
		return it == cells_.end() ? nullptr : it->second;
	}

	RTLIL::ObjRange<RTLIL::Wire*> wires() { return RTLIL::ObjRange<RTLIL::Wire*>(&wires_, &refcount_wires_); }
	int wires_size() const { return wires_.size(); }
	RTLIL::Wire* wire_at(int index) const { return wires_.element(index)->second; }
	RTLIL::ObjRange<RTLIL::Cell*> cells() { return RTLIL::ObjRange<RTLIL::Cell*>(&cells_, &refcount_cells_); }
	int cells_size() const { return cells_.size(); }
	RTLIL::Cell* cell_at(int index) const { return cells_.element(index)->second; }

	void add(RTLIL::Binding *binding);

	// Removing wires is expensive. If you have to remove wires, remove them all at once.
	void remove(const pool<RTLIL::Wire*> &wires);
	void remove(RTLIL::Cell *cell);
	void remove(RTLIL::Memory *memory);
	void remove(RTLIL::Process *process);

	void rename(RTLIL::Wire *wire, RTLIL::IdString new_name);
	void rename(RTLIL::Cell *cell, RTLIL::IdString new_name);
	void rename(RTLIL::IdString old_name, RTLIL::IdString new_name);
	YS_NAME_FWD_2ND(rename)

	void swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2);
	void swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2);

	RTLIL::IdString uniquify(RTLIL::IdString name);
	RTLIL::IdString uniquify(RTLIL::IdString name, int &index);
	YS_NAME_FWD(uniquify)

	RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
	RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);
	YS_NAME_FWD(addWire)

	RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
	RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);
	YS_NAME_FWD(addCell)
	template<typename T, YS_UNPOOLED_NAME(T)>
	RTLIL::Cell *addCell(RTLIL::IdString name, T type) { return addCell(name, design->twines.add(std::move(type))); }

	RTLIL::Memory *addMemory(RTLIL::IdString name);
	YS_NAME_FWD(addMemory)
	RTLIL::Memory *addMemory(RTLIL::IdString name, const RTLIL::Memory *other);

	RTLIL::Process *addProcess(RTLIL::IdString name);
	YS_NAME_FWD(addProcess)
	RTLIL::Process *addProcess(RTLIL::IdString name, const RTLIL::Process *other);

	// The add* methods create a cell and return the created cell. All signals must exist in advance.

	RTLIL::Cell* addNot (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addPos (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addBuf (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addNeg (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addAnd  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addOr   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addXor  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addXnor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addReduceAnd  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addReduceOr   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addReduceXor  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addReduceXnor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addReduceBool (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addShl    (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addShr    (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addSshl   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addSshr   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addShift  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addShiftx (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addLt  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addLe  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addEq  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addNe  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addEqx (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addNex (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addGe  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addGt  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addAdd (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addSub (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addMul (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	// truncating division
	RTLIL::Cell* addDiv (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	// truncating modulo
	RTLIL::Cell* addMod (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addDivFloor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addModFloor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addPow (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool a_signed = false, bool b_signed = false, const std::string &src = "");

	RTLIL::Cell* addFa (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_c, const RTLIL::SigSpec &sig_x, const RTLIL::SigSpec &sig_y, const std::string &src = "");

	RTLIL::Cell* addLogicNot (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addLogicAnd (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addLogicOr  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");

	RTLIL::Cell* addMux  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addPmux (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addBmux (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addDemux (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, const std::string &src = "");

	RTLIL::Cell* addBweqx  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addBwmux  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, const std::string &src = "");

	RTLIL::Cell* addSlice  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, RTLIL::Const offset, const std::string &src = "");
	RTLIL::Cell* addConcat (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addLut    (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, RTLIL::Const lut, const std::string &src = "");
	RTLIL::Cell* addTribuf (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::Cell* addAssert (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const std::string &src = "");
	RTLIL::Cell* addAssume (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const std::string &src = "");
	RTLIL::Cell* addLive   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const std::string &src = "");
	RTLIL::Cell* addFair   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const std::string &src = "");
	RTLIL::Cell* addCover  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const std::string &src = "");
	RTLIL::Cell* addEquiv  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, const std::string &src = "");

	RTLIL::Cell* addSr    (RTLIL::IdString name, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr, const RTLIL::SigSpec &sig_q, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addFf    (RTLIL::IdString name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, const std::string &src = "");
	RTLIL::Cell* addDff   (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_d,   const RTLIL::SigSpec &sig_q, bool clk_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffe  (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en,  const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffsr (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr, RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffsre (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr, RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdff (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const arst_value, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdffe (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst,  const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const arst_value, bool clk_polarity = true, bool en_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAldff (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, const RTLIL::SigSpec &sig_ad, bool clk_polarity = true, bool aload_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAldffe (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_aload,  const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, const RTLIL::SigSpec &sig_ad, bool clk_polarity = true, bool en_polarity = true, bool aload_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdff (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const srst_value, bool clk_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdffe (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst,  const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const srst_value, bool clk_polarity = true, bool en_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdffce (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const srst_value, bool clk_polarity = true, bool en_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDlatch (RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdlatch (RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, RTLIL::Const arst_value, bool en_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDlatchsr (RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr, RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");

	RTLIL::Cell* addBufGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addNotGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addAndGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addNandGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addOrGate     (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addNorGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addXorGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addXnorGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addAndnotGate (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addOrnotGate  (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addMuxGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_s, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addNmuxGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_s, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addAoi3Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addOai3Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addAoi4Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_d, const RTLIL::SigBit &sig_y, const std::string &src = "");
	RTLIL::Cell* addOai4Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_d, const RTLIL::SigBit &sig_y, const std::string &src = "");

	RTLIL::Cell* addSrGate     (RTLIL::IdString name, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			const RTLIL::SigSpec &sig_q, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addFfGate     (RTLIL::IdString name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, const std::string &src = "");
	RTLIL::Cell* addDffGate    (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffeGate   (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool en_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffsrGate  (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDffsreGate (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity = true, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdffGate   (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value = false, bool clk_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdffeGate  (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value = false, bool clk_polarity = true, bool en_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAldffGate   (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity = true, bool aload_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAldffeGate  (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity = true, bool en_polarity = true, bool aload_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdffGate   (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value = false, bool clk_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdffeGate  (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value = false, bool clk_polarity = true, bool en_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addSdffceGate (RTLIL::IdString name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value = false, bool clk_polarity = true, bool en_polarity = true, bool srst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDlatchGate (RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity = true, const std::string &src = "");
	RTLIL::Cell* addAdlatchGate(RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value = false, bool en_polarity = true, bool arst_polarity = true, const std::string &src = "");
	RTLIL::Cell* addDlatchsrGate  (RTLIL::IdString name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity = true, bool set_polarity = true, bool clr_polarity = true, const std::string &src = "");

	RTLIL::Cell* addAnyinit(RTLIL::IdString name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, const std::string &src = "");

	// The methods without the add* prefix create a cell and an output signal. They return the newly created output signal.

	RTLIL::SigSpec Not (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Pos (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Buf (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Neg (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec And  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Or   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Xor  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Xnor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec ReduceAnd  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec ReduceOr   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec ReduceXor  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec ReduceXnor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec ReduceBool (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec Shl    (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Shr    (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Sshl   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Sshr   (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Shift  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Shiftx (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec Lt  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Le  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Eq  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Ne  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Eqx (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Nex (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Ge  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Gt  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec Add (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Sub (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Mul (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	// truncating division
	RTLIL::SigSpec Div (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	// truncating modulo
	RTLIL::SigSpec Mod (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec DivFloor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec ModFloor (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec Pow (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool a_signed = false, bool b_signed = false, const std::string &src = "");

	RTLIL::SigSpec LogicNot (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec LogicAnd (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");
	RTLIL::SigSpec LogicOr  (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed = false, const std::string &src = "");

	RTLIL::SigSpec Mux      (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const std::string &src = "");
	RTLIL::SigSpec Pmux     (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const std::string &src = "");
	RTLIL::SigSpec Bmux     (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const std::string &src = "");
	RTLIL::SigSpec Demux     (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const std::string &src = "");

	RTLIL::SigSpec Bweqx      (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const std::string &src = "");
	RTLIL::SigSpec Bwmux      (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const std::string &src = "");

	RTLIL::SigBit BufGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const std::string &src = "");
	RTLIL::SigBit NotGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const std::string &src = "");
	RTLIL::SigBit AndGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit NandGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit OrGate     (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit NorGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit XorGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit XnorGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit AndnotGate (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit OrnotGate  (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const std::string &src = "");
	RTLIL::SigBit MuxGate    (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_s, const std::string &src = "");
	RTLIL::SigBit NmuxGate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_s, const std::string &src = "");
	RTLIL::SigBit Aoi3Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const std::string &src = "");
	RTLIL::SigBit Oai3Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const std::string &src = "");
	RTLIL::SigBit Aoi4Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_d, const std::string &src = "");
	RTLIL::SigBit Oai4Gate   (RTLIL::IdString name, const RTLIL::SigBit &sig_a, const RTLIL::SigBit &sig_b, const RTLIL::SigBit &sig_c, const RTLIL::SigBit &sig_d, const std::string &src = "");

	RTLIL::SigSpec Anyconst  (RTLIL::IdString name, int width = 1, const std::string &src = "");
	RTLIL::SigSpec Anyseq    (RTLIL::IdString name, int width = 1, const std::string &src = "");
	RTLIL::SigSpec Allconst  (RTLIL::IdString name, int width = 1, const std::string &src = "");
	RTLIL::SigSpec Allseq    (RTLIL::IdString name, int width = 1, const std::string &src = "");
	RTLIL::SigSpec Initstate (RTLIL::IdString name, const std::string &src = "");

	RTLIL::SigSpec SetTag          (RTLIL::IdString name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, const std::string &src = "");
	RTLIL::Cell*   addSetTag       (RTLIL::IdString name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, const RTLIL::SigSpec &sig_y, const std::string &src = "");
	RTLIL::SigSpec GetTag          (RTLIL::IdString name, const std::string &tag, const RTLIL::SigSpec &sig_a, const std::string &src = "");
	RTLIL::Cell*   addOverwriteTag (RTLIL::IdString name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, const std::string &src = "");
	RTLIL::SigSpec OriginalTag     (RTLIL::IdString name, const std::string &tag, const RTLIL::SigSpec &sig_a, const std::string &src = "");
	RTLIL::SigSpec FutureFF        (RTLIL::IdString name, const RTLIL::SigSpec &sig_e, const std::string &src = "");
	YS_NAME_FWD(addAnyinit)
	YS_NAME_FWD(Anyconst) YS_NAME_FWD(Anyseq) YS_NAME_FWD(Allconst) YS_NAME_FWD(Allseq)
	YS_NAME_FWD(Initstate)
	YS_NAME_FWD(SetTag) YS_NAME_FWD(addSetTag) YS_NAME_FWD(GetTag)
	YS_NAME_FWD(addOverwriteTag) YS_NAME_FWD(OriginalTag) YS_NAME_FWD(FutureFF)
	YS_NAME_FWD(addNot) YS_NAME_FWD(addPos) YS_NAME_FWD(addBuf) YS_NAME_FWD(addNeg)
	YS_NAME_FWD(addAnd) YS_NAME_FWD(addOr) YS_NAME_FWD(addXor) YS_NAME_FWD(addXnor)
	YS_NAME_FWD(addReduceAnd) YS_NAME_FWD(addReduceOr) YS_NAME_FWD(addReduceXor) YS_NAME_FWD(addReduceXnor)
	YS_NAME_FWD(addReduceBool) YS_NAME_FWD(addShl) YS_NAME_FWD(addShr) YS_NAME_FWD(addSshl)
	YS_NAME_FWD(addSshr) YS_NAME_FWD(addShift) YS_NAME_FWD(addShiftx) YS_NAME_FWD(addLt)
	YS_NAME_FWD(addLe) YS_NAME_FWD(addEq) YS_NAME_FWD(addNe) YS_NAME_FWD(addEqx)
	YS_NAME_FWD(addNex) YS_NAME_FWD(addGe) YS_NAME_FWD(addGt) YS_NAME_FWD(addAdd)
	YS_NAME_FWD(addSub) YS_NAME_FWD(addMul) YS_NAME_FWD(addDiv) YS_NAME_FWD(addMod)
	YS_NAME_FWD(addDivFloor) YS_NAME_FWD(addModFloor) YS_NAME_FWD(addPow) YS_NAME_FWD(addFa)
	YS_NAME_FWD(addLogicNot) YS_NAME_FWD(addLogicAnd) YS_NAME_FWD(addLogicOr) YS_NAME_FWD(addMux)
	YS_NAME_FWD(addPmux) YS_NAME_FWD(addBmux) YS_NAME_FWD(addDemux) YS_NAME_FWD(addBweqx)
	YS_NAME_FWD(addBwmux) YS_NAME_FWD(addSlice) YS_NAME_FWD(addConcat) YS_NAME_FWD(addLut)
	YS_NAME_FWD(addTribuf) YS_NAME_FWD(addAssert) YS_NAME_FWD(addAssume) YS_NAME_FWD(addLive)
	YS_NAME_FWD(addFair) YS_NAME_FWD(addCover) YS_NAME_FWD(addEquiv) YS_NAME_FWD(addSr)
	YS_NAME_FWD(addFf) YS_NAME_FWD(addDff) YS_NAME_FWD(addDffe) YS_NAME_FWD(addDffsr)
	YS_NAME_FWD(addDffsre) YS_NAME_FWD(addAdff) YS_NAME_FWD(addAdffe) YS_NAME_FWD(addAldff)
	YS_NAME_FWD(addAldffe) YS_NAME_FWD(addSdff) YS_NAME_FWD(addSdffe) YS_NAME_FWD(addSdffce)
	YS_NAME_FWD(addDlatch) YS_NAME_FWD(addAdlatch) YS_NAME_FWD(addDlatchsr) YS_NAME_FWD(addBufGate)
	YS_NAME_FWD(addNotGate) YS_NAME_FWD(addAndGate) YS_NAME_FWD(addNandGate) YS_NAME_FWD(addOrGate)
	YS_NAME_FWD(addNorGate) YS_NAME_FWD(addXorGate) YS_NAME_FWD(addXnorGate) YS_NAME_FWD(addAndnotGate)
	YS_NAME_FWD(addOrnotGate) YS_NAME_FWD(addMuxGate) YS_NAME_FWD(addNmuxGate) YS_NAME_FWD(addAoi3Gate)
	YS_NAME_FWD(addOai3Gate) YS_NAME_FWD(addAoi4Gate) YS_NAME_FWD(addOai4Gate) YS_NAME_FWD(addSrGate)
	YS_NAME_FWD(addFfGate) YS_NAME_FWD(addDffGate) YS_NAME_FWD(addDffeGate) YS_NAME_FWD(addDffsrGate)
	YS_NAME_FWD(addDffsreGate) YS_NAME_FWD(addAdffGate) YS_NAME_FWD(addAdffeGate) YS_NAME_FWD(addAldffGate)
	YS_NAME_FWD(addAldffeGate) YS_NAME_FWD(addSdffGate) YS_NAME_FWD(addSdffeGate) YS_NAME_FWD(addSdffceGate)
	YS_NAME_FWD(addDlatchGate) YS_NAME_FWD(addAdlatchGate) YS_NAME_FWD(addDlatchsrGate) YS_NAME_FWD(Not)
	YS_NAME_FWD(Pos) YS_NAME_FWD(Buf) YS_NAME_FWD(Neg) YS_NAME_FWD(And)
	YS_NAME_FWD(Or) YS_NAME_FWD(Xor) YS_NAME_FWD(Xnor) YS_NAME_FWD(ReduceAnd)
	YS_NAME_FWD(ReduceOr) YS_NAME_FWD(ReduceXor) YS_NAME_FWD(ReduceXnor) YS_NAME_FWD(ReduceBool)
	YS_NAME_FWD(Shl) YS_NAME_FWD(Shr) YS_NAME_FWD(Sshl) YS_NAME_FWD(Sshr)
	YS_NAME_FWD(Shift) YS_NAME_FWD(Shiftx) YS_NAME_FWD(Lt) YS_NAME_FWD(Le)
	YS_NAME_FWD(Eq) YS_NAME_FWD(Ne) YS_NAME_FWD(Eqx) YS_NAME_FWD(Nex)
	YS_NAME_FWD(Ge) YS_NAME_FWD(Gt) YS_NAME_FWD(Add) YS_NAME_FWD(Sub)
	YS_NAME_FWD(Mul) YS_NAME_FWD(Div) YS_NAME_FWD(Mod) YS_NAME_FWD(DivFloor)
	YS_NAME_FWD(ModFloor) YS_NAME_FWD(Pow) YS_NAME_FWD(LogicNot) YS_NAME_FWD(LogicAnd)
	YS_NAME_FWD(LogicOr) YS_NAME_FWD(Mux) YS_NAME_FWD(Pmux) YS_NAME_FWD(Bmux)
	YS_NAME_FWD(Demux) YS_NAME_FWD(Bweqx) YS_NAME_FWD(Bwmux) YS_NAME_FWD(BufGate)
	YS_NAME_FWD(NotGate) YS_NAME_FWD(AndGate) YS_NAME_FWD(NandGate) YS_NAME_FWD(OrGate)
	YS_NAME_FWD(NorGate) YS_NAME_FWD(XorGate) YS_NAME_FWD(XnorGate) YS_NAME_FWD(AndnotGate)
	YS_NAME_FWD(OrnotGate) YS_NAME_FWD(MuxGate) YS_NAME_FWD(NmuxGate) YS_NAME_FWD(Aoi3Gate)
	YS_NAME_FWD(Oai3Gate) YS_NAME_FWD(Aoi4Gate) YS_NAME_FWD(Oai4Gate)

	std::string to_rtlil_str() const;
#ifdef YOSYS_ENABLE_PYTHON
	static std::map<unsigned int, RTLIL::Module*> *get_all_modules(void);
#endif
};

struct RTLIL::Wire : public RTLIL::NamedObject
{
	YS_NO_UNIQUE_ADDRESS RTLIL::WireNameMasq name;

	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

protected:
	// use module->addWire() and module->remove() to create or destroy wires
	friend struct RTLIL::Module;
	Wire();
	~Wire();

	friend struct RTLIL::Design;
	friend struct RTLIL::Cell;
	RTLIL::Cell *driverCell_ = nullptr;
	IdString driverPort_ = IdString::Null;

public:
	// do not simply copy wires
	Wire(RTLIL::Wire &other) = delete;
	void operator=(RTLIL::Wire &other) = delete;

	RTLIL::Module *module;
	int width, start_offset, port_id;
	bool port_input, port_output, upto, is_signed;

	RTLIL::Design *design() const { return module ? module->design : nullptr; }

	bool known_driver() const { return driverCell_ != nullptr; }

	RTLIL::Cell *driverCell() const    { log_assert(driverCell_); return driverCell_; };
	RTLIL::IdString driverPort() const { log_assert(driverCell_); return driverPort_; };

	int from_hdl_index(int hdl_index) {
		int zero_index = hdl_index - start_offset;
		int rtlil_index = upto ? width - 1 - zero_index : zero_index;
		return rtlil_index >= 0 && rtlil_index < width ? rtlil_index : INT_MIN;
	}

	int to_hdl_index(int rtlil_index) {
		if (rtlil_index < 0 || rtlil_index >= width)
			return INT_MIN;
		int zero_index = upto ? width - 1 - rtlil_index : rtlil_index;
		return zero_index + start_offset;
	}

	std::string to_rtlil_str() const;

#ifdef YOSYS_ENABLE_PYTHON
	static std::map<unsigned int, RTLIL::Wire*> *get_all_wires(void);
#endif
};

inline int GetSize(RTLIL::Wire *wire) {
	return wire->width;
}

struct RTLIL::Memory : public RTLIL::NamedObject
{
	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

	Memory();
	~Memory();

	RTLIL::Module *module = nullptr;

	RTLIL::Design *design() const { return module ? module->design : nullptr; }

	YS_NO_UNIQUE_ADDRESS RTLIL::MemoryNameMasq name;

	int width, start_offset, size;
#ifdef YOSYS_ENABLE_PYTHON
	static std::map<unsigned int, RTLIL::Memory*> *get_all_memorys(void);
#endif

	std::string to_rtlil_str() const;
};

template<typename N>
inline constexpr bool is_name_string_v =
	std::is_same_v<std::decay_t<N>, std::string> ||
	std::is_same_v<std::decay_t<N>, const char *> || std::is_same_v<std::decay_t<N>, char *>;

#define YS_NAME_STRING(N) std::enable_if_t<is_name_string_v<N>, int> = 0

struct RTLIL::Cell : public RTLIL::NamedObject
{
private:
	void initIndex();

	bool bufnorm_handle_setPort(IdString portname, RTLIL::SigSpec &signal, dict<IdString, RTLIL::SigSpec>::iterator conn_it);
public:
	YS_NO_UNIQUE_ADDRESS RTLIL::CellNameMasq name;

	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

protected:
	// use module->addCell() and module->remove() to create or destroy cells
	friend struct RTLIL::Module;
	Cell();
	~Cell();

public:
	// do not simply copy cells
	Cell(RTLIL::Cell &other) = delete;
	void operator=(RTLIL::Cell &other) = delete;

	RTLIL::Module *module;

	RTLIL::Design *design() const { return module ? module->design : nullptr; }

	IdString type_impl;
	YS_NO_UNIQUE_ADDRESS RTLIL::CellTypeMasq type;
	dict<RTLIL::IdString, RTLIL::SigSpec> connections_;
	dict<RTLIL::IdString, RTLIL::Const> parameters;

	// access cell ports
	bool hasPort(RTLIL::IdString portname) const;
	void unsetPort(RTLIL::IdString portname);
	void setPort(RTLIL::IdString portname, RTLIL::SigSpec signal);
	template<typename N, YS_NAME_STRING(N)> void setPort(N portname, RTLIL::SigSpec signal)
		{ setPort(module->design->twines.add(std::move(portname)), std::move(signal)); }
	const RTLIL::SigSpec &getPort(RTLIL::IdString portname) const;
	const dict<RTLIL::IdString, RTLIL::SigSpec> &connections() const;

	bool known() const;
	bool input(RTLIL::IdString portname) const;
	bool output(RTLIL::IdString portname) const;
	PortDir port_dir(RTLIL::IdString portname) const;

	bool hasParam(RTLIL::IdString paramname) const;
	void unsetParam(RTLIL::IdString paramname);
	void setParam(RTLIL::IdString paramname, RTLIL::Const value);
	const RTLIL::Const &getParam(RTLIL::IdString paramname) const;

	template<typename N, YS_NAME_STRING(N)> bool hasParam(N name) const
		{ return hasParam(module->design->twines.add(std::move(name))); }
	template<typename N, YS_NAME_STRING(N)> void unsetParam(N name)
		{ unsetParam(module->design->twines.add(std::move(name))); }
	template<typename N, YS_NAME_STRING(N)> void setParam(N name, RTLIL::Const value)
		{ setParam(module->design->twines.add(std::move(name)), std::move(value)); }
	template<typename N, YS_NAME_STRING(N)> const RTLIL::Const &getParam(N name) const
		{ return getParam(module->design->twines.add(std::move(name))); }

	void sort();
	void check();
	void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false);

	bool has_keep_attr() const;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);

#ifdef YOSYS_ENABLE_PYTHON
	static std::map<unsigned int, RTLIL::Cell*> *get_all_cells(void);
#endif

	bool has_memid() const;
	bool is_mem_cell() const;
	bool is_builtin_ff() const;

	std::string to_rtlil_str() const;
};

struct RTLIL::CaseRule : public RTLIL::AttrObject
{
	std::vector<RTLIL::SigSpec> compare;
	std::vector<RTLIL::SigSig> actions;
	std::vector<RTLIL::SwitchRule*> switches;

	~CaseRule();

	bool empty() const;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	RTLIL::CaseRule *clone() const;
};

struct RTLIL::SwitchRule : public RTLIL::AttrObject
{
	RTLIL::SigSpec signal;
	std::vector<RTLIL::CaseRule*> cases;

	~SwitchRule();

	bool empty() const;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	RTLIL::SwitchRule *clone() const;
};

struct RTLIL::MemWriteAction : RTLIL::AttrObject
{
	RTLIL::IdString memid;
	RTLIL::SigSpec address;
	RTLIL::SigSpec data;
	RTLIL::SigSpec enable;
	RTLIL::Const priority_mask;
};

struct RTLIL::SyncRule
{
	RTLIL::SyncType type;
	RTLIL::SigSpec signal;
	std::vector<RTLIL::SigSig> actions;
	std::vector<RTLIL::MemWriteAction> mem_write_actions;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	RTLIL::SyncRule *clone() const;
};

struct RTLIL::Process : public RTLIL::NamedObject
{
	Hasher::hash_t hashidx_;
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(hashidx_); return h; }

protected:
	// use module->addProcess() and module->remove() to create or destroy processes
	friend struct RTLIL::Module;
	Process();
	~Process();

public:
	RTLIL::Module *module;
	RTLIL::CaseRule root_case;
	std::vector<RTLIL::SyncRule*> syncs;

	RTLIL::Design *design() const { return module ? module->design : nullptr; }

	YS_NO_UNIQUE_ADDRESS RTLIL::ProcessNameMasq name;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	RTLIL::Process *clone() const;

	std::string to_rtlil_str() const;
};

inline RTLIL::SigBit::SigBit() : wire(NULL), data(RTLIL::State::S0) { }
inline RTLIL::SigBit::SigBit(RTLIL::State bit) : wire(NULL), data(bit) { }
inline RTLIL::SigBit::SigBit(bool bit) : wire(NULL), data(bit ? State::S1 : State::S0) { }
inline RTLIL::SigBit::SigBit(RTLIL::Wire *wire) : wire(wire), offset(0) { log_assert(wire && wire->width == 1); }
inline RTLIL::SigBit::SigBit(RTLIL::Wire *wire, int offset) : wire(wire), offset(offset) { log_assert(wire != nullptr); }
inline RTLIL::SigBit::SigBit(const RTLIL::SigChunk &chunk) : wire(chunk.wire) { log_assert(chunk.width == 1); if (wire) offset = chunk.offset; else data = chunk.data[0]; }
inline RTLIL::SigBit::SigBit(const RTLIL::SigChunk &chunk, int index) : wire(chunk.wire) { if (wire) offset = chunk.offset + index; else data = chunk.data[index]; }

inline bool RTLIL::SigBit::operator<(const RTLIL::SigBit &other) const {
	if (wire == other.wire)
		return wire ? (offset < other.offset) : (data < other.data);
	if (wire != nullptr && other.wire != nullptr)
		return wire->name < other.wire->name;
	return (wire != nullptr) < (other.wire != nullptr);
}

inline bool RTLIL::SigBit::operator==(const RTLIL::SigBit &other) const {
	return (wire == other.wire) && (wire ? (offset == other.offset) : (data == other.data));
}

inline bool RTLIL::SigBit::operator!=(const RTLIL::SigBit &other) const {
	return (wire != other.wire) || (wire ? (offset != other.offset) : (data != other.data));
}

inline Hasher RTLIL::SigBit::hash_into(Hasher h) const {
	if (wire) {
		h.eat(offset);
		h.eat(wire->name);
		return h;
	}
	h.eat(data);
	return h;
}


inline Hasher RTLIL::SigBit::hash_top() const {
	Hasher h;
	if (wire) {
		IdString name = wire->name.ref();
		uint32_t n = (uint32_t)name.bits();
		h.force(hashlib::legacy::djb2_add(n, offset));
		return h;
	}
	h.force(data);
	return h;
}

inline RTLIL::SigBit &RTLIL::SigSpecIterator::operator*() const {
	return (*sig_p)[index];
}

inline const RTLIL::SigBit &RTLIL::SigSpecConstIterator::operator*() {
	bit = (*sig_p)[index];
	return bit;
}

inline RTLIL::SigBit::SigBit(const RTLIL::SigSpec &sig) {
	log_assert(sig.size() == 1);
	auto it = sig.chunks().begin();
	*this = SigBit(*it);
}

template<typename T>
void RTLIL::Module::rewrite_sigspecs(T &functor)
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
void RTLIL::Module::rewrite_sigspecs2(T &functor)
{
	for (auto &it : cells_)
		it.second->rewrite_sigspecs2(functor);
	for (auto &it : processes)
		it.second->rewrite_sigspecs2(functor);
	for (auto &it : connections_) {
		functor(it.first, it.second);
	}
}

template<typename T>
void RTLIL::Cell::rewrite_sigspecs(T &functor) {
	for (auto &it : connections_)
		functor(it.second);
}

template<typename T>
void RTLIL::Cell::rewrite_sigspecs2(T &functor) {
	for (auto &it : connections_)
		functor(it.second);
}

template<typename T>
void RTLIL::CaseRule::rewrite_sigspecs(T &functor) {
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
void RTLIL::CaseRule::rewrite_sigspecs2(T &functor) {
	for (auto &it : compare)
		functor(it);
	for (auto &it : actions) {
		functor(it.first, it.second);
	}
	for (auto it : switches)
		it->rewrite_sigspecs2(functor);
}

template<typename T>
void RTLIL::SwitchRule::rewrite_sigspecs(T &functor)
{
	functor(signal);
	for (auto it : cases)
		it->rewrite_sigspecs(functor);
}

template<typename T>
void RTLIL::SwitchRule::rewrite_sigspecs2(T &functor)
{
	functor(signal);
	for (auto it : cases)
		it->rewrite_sigspecs2(functor);
}

template<typename T>
void RTLIL::SyncRule::rewrite_sigspecs(T &functor)
{
	functor(signal);
	for (auto &it : actions) {
		functor(it.first);
		functor(it.second);
	}
	for (auto &it : mem_write_actions) {
		functor(it.address);
		functor(it.data);
		functor(it.enable);
	}
}

template<typename T>
void RTLIL::SyncRule::rewrite_sigspecs2(T &functor)
{
	functor(signal);
	for (auto &it : actions) {
		functor(it.first, it.second);
	}
	for (auto &it : mem_write_actions) {
		functor(it.address);
		functor(it.data);
		functor(it.enable);
	}
}

template<typename T>
void RTLIL::Process::rewrite_sigspecs(T &functor)
{
	root_case.rewrite_sigspecs(functor);
	for (auto it : syncs)
		it->rewrite_sigspecs(functor);
}

template<typename T>
void RTLIL::Process::rewrite_sigspecs2(T &functor)
{
	root_case.rewrite_sigspecs2(functor);
	for (auto it : syncs)
		it->rewrite_sigspecs2(functor);
}

namespace RTLIL {
}

#include "kernel/rtlil_twine_compat_impl.h"

YOSYS_NAMESPACE_END

#endif
