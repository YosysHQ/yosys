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
		STg = 6, // global clock
		STi = 7  // init
	};

	enum ConstFlags : unsigned char {
		CONST_FLAG_NONE   = 0,
		CONST_FLAG_STRING = 1,
		CONST_FLAG_SIGNED = 2,  // only used for parameters
		CONST_FLAG_REAL   = 4   // only used for parameters
	};

	struct Const;
	struct AttrObject;
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

	struct IdString
	{
		#undef YOSYS_XTRACE_GET_PUT
		#undef YOSYS_SORT_ID_FREE_LIST
		#undef YOSYS_USE_STICKY_IDS
		#undef YOSYS_NO_IDS_REFCNT

		// the global id string cache

		static struct destruct_guard_t {
			bool ok; // POD, will be initialized to zero
			destruct_guard_t() { ok = true; }
			~destruct_guard_t() { ok = false; }
		} destruct_guard;

		static std::vector<char*> global_id_storage_;
		static dict<char*, int, hash_cstr_ops> global_id_index_;
	#ifndef YOSYS_NO_IDS_REFCNT
		static std::vector<int> global_refcount_storage_;
		static std::vector<int> global_free_idx_list_;
	#endif

	#ifdef YOSYS_USE_STICKY_IDS
		static int last_created_idx_ptr_;
		static int last_created_idx_[8];
	#endif

		static inline void xtrace_db_dump()
		{
		#ifdef YOSYS_XTRACE_GET_PUT
			for (int idx = 0; idx < GetSize(global_id_storage_); idx++)
			{
				if (global_id_storage_.at(idx) == nullptr)
					log("#X# DB-DUMP index %d: FREE\n", idx);
				else
					log("#X# DB-DUMP index %d: '%s' (ref %d)\n", idx, global_id_storage_.at(idx), global_refcount_storage_.at(idx));
			}
		#endif
		}

		static inline void checkpoint()
		{
		#ifdef YOSYS_USE_STICKY_IDS
			last_created_idx_ptr_ = 0;
			for (int i = 0; i < 8; i++) {
				if (last_created_idx_[i])
					put_reference(last_created_idx_[i]);
				last_created_idx_[i] = 0;
			}
		#endif
		#ifdef YOSYS_SORT_ID_FREE_LIST
			std::sort(global_free_idx_list_.begin(), global_free_idx_list_.end(), std::greater<int>());
		#endif
		}

		static inline int get_reference(int idx)
		{
			if (idx) {
		#ifndef YOSYS_NO_IDS_REFCNT
				global_refcount_storage_[idx]++;
		#endif
		#ifdef YOSYS_XTRACE_GET_PUT
				if (yosys_xtrace)
					log("#X# GET-BY-INDEX '%s' (index %d, refcount %d)\n", global_id_storage_.at(idx), idx, global_refcount_storage_.at(idx));
		#endif
			}
			return idx;
		}

		static int get_reference(const char *p)
		{
			log_assert(destruct_guard.ok);

			if (!p[0])
				return 0;

			auto it = global_id_index_.find((char*)p);
			if (it != global_id_index_.end()) {
		#ifndef YOSYS_NO_IDS_REFCNT
				global_refcount_storage_.at(it->second)++;
		#endif
		#ifdef YOSYS_XTRACE_GET_PUT
				if (yosys_xtrace)
					log("#X# GET-BY-NAME '%s' (index %d, refcount %d)\n", global_id_storage_.at(it->second), it->second, global_refcount_storage_.at(it->second));
		#endif
				return it->second;
			}

			log_assert(p[0] == '$' || p[0] == '\\');
			log_assert(p[1] != 0);
			for (const char *c = p; *c; c++)
				if ((unsigned)*c <= (unsigned)' ')
					log_error("Found control character or space (0x%02x) in string '%s' which is not allowed in RTLIL identifiers\n", *c, p);

		#ifndef YOSYS_NO_IDS_REFCNT
			if (global_free_idx_list_.empty()) {
				if (global_id_storage_.empty()) {
					global_refcount_storage_.push_back(0);
					global_id_storage_.push_back((char*)"");
					global_id_index_[global_id_storage_.back()] = 0;
				}
				log_assert(global_id_storage_.size() < 0x40000000);
				global_free_idx_list_.push_back(global_id_storage_.size());
				global_id_storage_.push_back(nullptr);
				global_refcount_storage_.push_back(0);
			}

			int idx = global_free_idx_list_.back();
			global_free_idx_list_.pop_back();
			global_id_storage_.at(idx) = strdup(p);
			global_id_index_[global_id_storage_.at(idx)] = idx;
			global_refcount_storage_.at(idx)++;
		#else
			if (global_id_storage_.empty()) {
				global_id_storage_.push_back((char*)"");
				global_id_index_[global_id_storage_.back()] = 0;
			}
			int idx = global_id_storage_.size();
			global_id_storage_.push_back(strdup(p));
			global_id_index_[global_id_storage_.back()] = idx;
		#endif

			if (yosys_xtrace) {
				log("#X# New IdString '%s' with index %d.\n", p, idx);
				log_backtrace("-X- ", yosys_xtrace-1);
			}

		#ifdef YOSYS_XTRACE_GET_PUT
			if (yosys_xtrace)
				log("#X# GET-BY-NAME '%s' (index %d, refcount %d)\n", global_id_storage_.at(idx), idx, global_refcount_storage_.at(idx));
		#endif

		#ifdef YOSYS_USE_STICKY_IDS
			// Avoid Create->Delete->Create pattern
			if (last_created_idx_[last_created_idx_ptr_])
				put_reference(last_created_idx_[last_created_idx_ptr_]);
			last_created_idx_[last_created_idx_ptr_] = idx;
			get_reference(last_created_idx_[last_created_idx_ptr_]);
			last_created_idx_ptr_ = (last_created_idx_ptr_ + 1) & 7;
		#endif

			return idx;
		}

	#ifndef YOSYS_NO_IDS_REFCNT
		static inline void put_reference(int idx)
		{
			// put_reference() may be called from destructors after the destructor of
			// global_refcount_storage_ has been run. in this case we simply do nothing.
			if (!destruct_guard.ok || !idx)
				return;

		#ifdef YOSYS_XTRACE_GET_PUT
			if (yosys_xtrace) {
				log("#X# PUT '%s' (index %d, refcount %d)\n", global_id_storage_.at(idx), idx, global_refcount_storage_.at(idx));
			}
		#endif

			int &refcount = global_refcount_storage_[idx];

			if (--refcount > 0)
				return;

			log_assert(refcount == 0);
			free_reference(idx);
		}
		static inline void free_reference(int idx)
		{
			if (yosys_xtrace) {
				log("#X# Removed IdString '%s' with index %d.\n", global_id_storage_.at(idx), idx);
				log_backtrace("-X- ", yosys_xtrace-1);
			}

			global_id_index_.erase(global_id_storage_.at(idx));
			free(global_id_storage_.at(idx));
			global_id_storage_.at(idx) = nullptr;
			global_free_idx_list_.push_back(idx);
		}
	#else
		static inline void put_reference(int) { }
	#endif

		// the actual IdString object is just is a single int

		int index_;

		inline IdString() : index_(0) { }
		inline IdString(const char *str) : index_(get_reference(str)) { }
		inline IdString(const IdString &str) : index_(get_reference(str.index_)) { }
		inline IdString(IdString &&str) : index_(str.index_) { str.index_ = 0; }
		inline IdString(const std::string &str) : index_(get_reference(str.c_str())) { }
		inline ~IdString() { put_reference(index_); }

		inline void operator=(const IdString &rhs) {
			put_reference(index_);
			index_ = get_reference(rhs.index_);
		}

		inline void operator=(const char *rhs) {
			IdString id(rhs);
			*this = id;
		}

		inline void operator=(const std::string &rhs) {
			IdString id(rhs);
			*this = id;
		}

		inline const char *c_str() const {
			return global_id_storage_.at(index_);
		}

		inline std::string str() const {
			return std::string(global_id_storage_.at(index_));
		}

		inline bool operator<(const IdString &rhs) const {
			return index_ < rhs.index_;
		}

		inline bool operator==(const IdString &rhs) const { return index_ == rhs.index_; }
		inline bool operator!=(const IdString &rhs) const { return index_ != rhs.index_; }

		// The methods below are just convenience functions for better compatibility with std::string.

		bool operator==(const std::string &rhs) const { return c_str() == rhs; }
		bool operator!=(const std::string &rhs) const { return c_str() != rhs; }

		bool operator==(const char *rhs) const { return strcmp(c_str(), rhs) == 0; }
		bool operator!=(const char *rhs) const { return strcmp(c_str(), rhs) != 0; }

		char operator[](size_t i) const {
			const char *p = c_str();
			for (; i != 0; i--, p++)
				log_assert(*p != 0);
			return *p;
		}

		std::string substr(size_t pos = 0, size_t len = std::string::npos) const {
			if (len == std::string::npos || len >= strlen(c_str() + pos))
				return std::string(c_str() + pos);
			else
				return std::string(c_str() + pos, len);
		}

		int compare(size_t pos, size_t len, const char* s) const {
			return strncmp(c_str()+pos, s, len);
		}

		bool begins_with(const char* prefix) const {
			size_t len = strlen(prefix);
			if (size() < len) return false;
			return compare(0, len, prefix) == 0;
		}

		bool ends_with(const char* suffix) const {
			size_t len = strlen(suffix);
			if (size() < len) return false;
			return compare(size()-len, len, suffix) == 0;
		}

		bool contains(const char* str) const {
			return strstr(c_str(), str);
		}

		size_t size() const {
			return strlen(c_str());
		}

		bool empty() const {
			return c_str()[0] == 0;
		}

		void clear() {
			*this = IdString();
		}

		unsigned int hash() const {
			return index_;
		}

		// The following is a helper key_compare class. Instead of for example std::set<Cell*>
		// use std::set<Cell*, IdString::compare_ptr_by_name<Cell>> if the order of cells in the
		// set has an influence on the algorithm.

		template<typename T> struct compare_ptr_by_name {
			bool operator()(const T *a, const T *b) const {
				return (a == nullptr || b == nullptr) ? (a < b) : (a->name < b->name);
			}
		};

		// often one needs to check if a given IdString is part of a list (for example a list
		// of cell types). the following functions helps with that.

		template<typename... Args>
		bool in(Args... args) const {
			// Credit: https://articles.emptycrate.com/2016/05/14/folds_in_cpp11_ish.html
			bool result = false;
			(void) std::initializer_list<int>{ (result = result || in(args), 0)... };
			return result;
		}

		bool in(const IdString &rhs) const { return *this == rhs; }
		bool in(const char *rhs) const { return *this == rhs; }
		bool in(const std::string &rhs) const { return *this == rhs; }
		bool in(const pool<IdString> &rhs) const { return rhs.count(*this) != 0; }

		bool isPublic() const { return begins_with("\\"); }
	};

	namespace ID {
#define X(_id) extern IdString _id;
#include "kernel/constids.inc"
#undef X
	};

	extern dict<std::string, std::string> constpad;

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

	static inline std::string unescape_id(const RTLIL::IdString &str) {
		return unescape_id(str.str());
	}

	static inline const char *id2cstr(const RTLIL::IdString &str) {
		return log_id(str);
	}

	template <typename T> struct sort_by_name_id {
		bool operator()(T *a, T *b) const {
			return a->name < b->name;
		}
	};

	template <typename T> struct sort_by_name_str {
		bool operator()(T *a, T *b) const {
			return strcmp(a->name.c_str(), b->name.c_str()) < 0;
		}
	};

	struct sort_by_id_str {
		bool operator()(const RTLIL::IdString &a, const RTLIL::IdString &b) const {
			return strcmp(a.c_str(), b.c_str()) < 0;
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
	RTLIL::Const const_neg         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len);

	RTLIL::Const const_mux         (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);
	RTLIL::Const const_pmux        (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);
	RTLIL::Const const_bmux        (const RTLIL::Const &arg1, const RTLIL::Const &arg2);
	RTLIL::Const const_demux       (const RTLIL::Const &arg1, const RTLIL::Const &arg2);

	RTLIL::Const const_bweqx       (const RTLIL::Const &arg1, const RTLIL::Const &arg2);
	RTLIL::Const const_bwmux       (const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3);


	// This iterator-range-pair is used for Design::modules(), Module::wires() and Module::cells().
	// It maintains a reference counter that is used to make sure that the container is not modified while being iterated over.

	template<typename T>
	struct ObjIterator {
		using iterator_category = std::forward_iterator_tag;
		using value_type = T;
		using difference_type = ptrdiff_t;
		using pointer = T*;
		using reference = T&;
		typename dict<RTLIL::IdString, T>::iterator it;
		dict<RTLIL::IdString, T> *list_p;
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


		inline bool operator==(const RTLIL::ObjIterator<T> &other) const {
			return !(*this != other);
		}

		inline ObjIterator<T>& operator++() {
			log_assert(list_p != nullptr);
			if (++it == list_p->end()) {
				(*refcount_p)--;
				list_p = nullptr;
				refcount_p = nullptr;
			}
			return *this;
		}

		inline ObjIterator<T>& operator+=(int amt) {
			log_assert(list_p != nullptr);
			it += amt;
			if (it == list_p->end()) {
				(*refcount_p)--;
				list_p = nullptr;
				refcount_p = nullptr;
			}
			return *this;
		}

		inline ObjIterator<T> operator+(int amt) {
			log_assert(list_p != nullptr);
			ObjIterator<T> new_obj(*this);
			new_obj.it += amt;
			if (new_obj.it == list_p->end()) {
				(*(new_obj.refcount_p))--;
				new_obj.list_p = nullptr;
				new_obj.refcount_p = nullptr;
			}
			return new_obj;
		}

		inline const ObjIterator<T> operator++(int) {
			ObjIterator<T> result(*this);
			++(*this);
			return result;
		}
	};

	template<typename T>
	struct ObjRange
	{
		dict<RTLIL::IdString, T> *list_p;
		int *refcount_p;

		ObjRange(decltype(list_p) list_p, int *refcount_p) : list_p(list_p), refcount_p(refcount_p) { }
		RTLIL::ObjIterator<T> begin() { return RTLIL::ObjIterator<T>(list_p, refcount_p); }
		RTLIL::ObjIterator<T> end() { return RTLIL::ObjIterator<T>(); }

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
	int flags;
	std::vector<RTLIL::State> bits;

	Const() : flags(RTLIL::CONST_FLAG_NONE) {}
	Const(const std::string &str);
	Const(int val, int width = 32);
	Const(RTLIL::State bit, int width = 1);
	Const(const std::vector<RTLIL::State> &bits) : bits(bits) { flags = CONST_FLAG_NONE; }
	Const(const std::vector<bool> &bits);
	Const(const RTLIL::Const &c) = default;
	RTLIL::Const &operator =(const RTLIL::Const &other) = default;

	bool operator <(const RTLIL::Const &other) const;
	bool operator ==(const RTLIL::Const &other) const;
	bool operator !=(const RTLIL::Const &other) const;

	bool as_bool() const;
	int as_int(bool is_signed = false) const;
	std::string as_string() const;
	static Const from_string(const std::string &str);

	std::string decode_string() const;

	inline int size() const { return bits.size(); }
	inline bool empty() const { return bits.empty(); }
	inline RTLIL::State &operator[](int index) { return bits.at(index); }
	inline const RTLIL::State &operator[](int index) const { return bits.at(index); }
	inline decltype(bits)::iterator begin() { return bits.begin(); }
	inline decltype(bits)::iterator end() { return bits.end(); }

	bool is_fully_zero() const;
	bool is_fully_ones() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool is_fully_undef_x_only() const;
	bool is_onehot(int *pos = nullptr) const;

	inline RTLIL::Const extract(int offset, int len = 1, RTLIL::State padding = RTLIL::State::S0) const {
		RTLIL::Const ret;
		ret.bits.reserve(len);
		for (int i = offset; i < offset + len; i++)
			ret.bits.push_back(i < GetSize(bits) ? bits[i] : padding);
		return ret;
	}

	void extu(int width) {
		bits.resize(width, RTLIL::State::S0);
	}

	void exts(int width) {
		bits.resize(width, bits.empty() ? RTLIL::State::Sx : bits.back());
	}

	inline unsigned int hash() const {
		unsigned int h = mkhash_init;
		for (auto b : bits)
			mkhash(h, b);
		return h;
	}
};

struct RTLIL::AttrObject
{
	dict<RTLIL::IdString, RTLIL::Const> attributes;

	bool has_attribute(const RTLIL::IdString &id) const;

	void set_bool_attribute(const RTLIL::IdString &id, bool value=true);
	bool get_bool_attribute(const RTLIL::IdString &id) const;

	bool get_blackbox_attribute(bool ignore_wb=false) const {
		return get_bool_attribute(ID::blackbox) || (!ignore_wb && get_bool_attribute(ID::whitebox));
	}

	void set_string_attribute(const RTLIL::IdString& id, string value);
	string get_string_attribute(const RTLIL::IdString &id) const;

	void set_strpool_attribute(const RTLIL::IdString& id, const pool<string> &data);
	void add_strpool_attribute(const RTLIL::IdString& id, const pool<string> &data);
	pool<string> get_strpool_attribute(const RTLIL::IdString &id) const;

	void set_src_attribute(const std::string &src) {
		set_string_attribute(ID::src, src);
	}
	std::string get_src_attribute() const {
		return get_string_attribute(ID::src);
	}

	void set_hdlname_attribute(const vector<string> &hierarchy);
	vector<string> get_hdlname_attribute() const;

	void set_intvec_attribute(const RTLIL::IdString& id, const vector<int> &data);
	vector<int> get_intvec_attribute(const RTLIL::IdString &id) const;
};

struct RTLIL::SigChunk
{
	RTLIL::Wire *wire;
	std::vector<RTLIL::State> data; // only used if wire == NULL, LSB at index 0
	int width, offset;

	SigChunk() : wire(nullptr), width(0), offset(0) {}
	SigChunk(const RTLIL::Const &value) : wire(nullptr), data(value.bits), width(GetSize(data)), offset(0) {}
	SigChunk(RTLIL::Const &&value) : wire(nullptr), data(std::move(value.bits)), width(GetSize(data)), offset(0) {}
	SigChunk(RTLIL::Wire *wire) : wire(wire), width(GetSize(wire)), offset(0) {}
	SigChunk(RTLIL::Wire *wire, int offset, int width = 1) : wire(wire), width(width), offset(offset) {}
	SigChunk(const std::string &str) : SigChunk(RTLIL::Const(str)) {}
	SigChunk(int val, int width = 32) : SigChunk(RTLIL::Const(val, width)) {}
	SigChunk(RTLIL::State bit, int width = 1) : SigChunk(RTLIL::Const(bit, width)) {}
	SigChunk(const RTLIL::SigBit &bit);

	RTLIL::SigChunk extract(int offset, int length) const;
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
	unsigned int hash() const;
};

struct RTLIL::SigSpecIterator : public std::iterator<std::input_iterator_tag, RTLIL::SigSpec>
{
	RTLIL::SigSpec *sig_p;
	int index;

	inline RTLIL::SigBit &operator*() const;
	inline bool operator!=(const RTLIL::SigSpecIterator &other) const { return index != other.index; }
	inline bool operator==(const RTLIL::SigSpecIterator &other) const { return index == other.index; }
	inline void operator++() { index++; }
};

struct RTLIL::SigSpecConstIterator : public std::iterator<std::input_iterator_tag, RTLIL::SigSpec>
{
	const RTLIL::SigSpec *sig_p;
	int index;

	inline const RTLIL::SigBit &operator*() const;
	inline bool operator!=(const RTLIL::SigSpecConstIterator &other) const { return index != other.index; }
	inline bool operator==(const RTLIL::SigSpecIterator &other) const { return index == other.index; }
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
	void updhash() const;

	inline bool packed() const {
		return bits_.empty();
	}

	inline void inline_unpack() const {
		if (!chunks_.empty())
			unpack();
	}

	// Only used by Module::remove(const pool<Wire*> &wires)
	// but cannot be more specific as it isn't yet declared
	friend struct RTLIL::Module;

public:
	SigSpec() : width_(0), hash_(0) {}
	SigSpec(std::initializer_list<RTLIL::SigSpec> parts);

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

	size_t get_hash() const {
		if (!hash_) hash();
		return hash_;
	}

	inline const std::vector<RTLIL::SigChunk> &chunks() const { pack(); return chunks_; }
	inline const std::vector<RTLIL::SigBit> &bits() const { inline_unpack(); return bits_; }

	inline int size() const { return width_; }
	inline bool empty() const { return width_ == 0; }

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

	void remove(int offset, int length = 1);
	void remove_const();

	RTLIL::SigSpec extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other = NULL) const;
	RTLIL::SigSpec extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other = NULL) const;
	RTLIL::SigSpec extract(int offset, int length = 1) const;
	RTLIL::SigSpec extract_end(int offset) const { return extract(offset, width_ - offset); }

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
	inline bool is_bit() const { return width_ == 1; }

	bool is_fully_const() const;
	bool is_fully_zero() const;
	bool is_fully_ones() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool has_const() const;
	bool has_marked_bits() const;
	bool is_onehot(int *pos = nullptr) const;

	bool as_bool() const;
	int as_int(bool is_signed = false) const;
	std::string as_string() const;
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

	operator std::vector<RTLIL::SigChunk>() const { return chunks(); }
	operator std::vector<RTLIL::SigBit>() const { return bits(); }
	const RTLIL::SigBit &at(int offset, const RTLIL::SigBit &defval) { return offset < width_ ? (*this)[offset] : defval; }

	unsigned int hash() const { if (!hash_) updhash(); return hash_; };

#ifndef NDEBUG
	void check(Module *mod = nullptr) const;
#else
	void check(Module *mod = nullptr) const { (void)mod; }
#endif
};

struct RTLIL::Selection
{
	bool full_selection;
	pool<RTLIL::IdString> selected_modules;
	dict<RTLIL::IdString, pool<RTLIL::IdString>> selected_members;

	Selection(bool full = true) : full_selection(full) { }

	bool selected_module(const RTLIL::IdString &mod_name) const;
	bool selected_whole_module(const RTLIL::IdString &mod_name) const;
	bool selected_member(const RTLIL::IdString &mod_name, const RTLIL::IdString &memb_name) const;
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

struct RTLIL::Monitor
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

	Monitor() {
		static unsigned int hashidx_count = 123456789;
		hashidx_count = mkhash_xorshift(hashidx_count);
		hashidx_ = hashidx_count;
	}

	virtual ~Monitor() { }
	virtual void notify_module_add(RTLIL::Module*) { }
	virtual void notify_module_del(RTLIL::Module*) { }
	virtual void notify_connect(RTLIL::Cell*, const RTLIL::IdString&, const RTLIL::SigSpec&, const RTLIL::SigSpec&) { }
	virtual void notify_connect(RTLIL::Module*, const RTLIL::SigSig&) { }
	virtual void notify_connect(RTLIL::Module*, const std::vector<RTLIL::SigSig>&) { }
	virtual void notify_blackout(RTLIL::Module*) { }
};

// Forward declaration; defined in preproc.h.
struct define_map_t;

struct RTLIL::Design
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

	pool<RTLIL::Monitor*> monitors;
	dict<std::string, std::string> scratchpad;

	int refcount_modules_;
	dict<RTLIL::IdString, RTLIL::Module*> modules_;
	std::vector<RTLIL::Binding*> bindings_;

	std::vector<AST::AstNode*> verilog_packages, verilog_globals;
	std::unique_ptr<define_map_t> verilog_defines;

	std::vector<RTLIL::Selection> selection_stack;
	dict<RTLIL::IdString, RTLIL::Selection> selection_vars;
	std::string selected_active_module;

	Design();
	~Design();

	RTLIL::ObjRange<RTLIL::Module*> modules();
	RTLIL::Module *module(const RTLIL::IdString &name);
	const RTLIL::Module *module(const RTLIL::IdString &name) const;
	RTLIL::Module *top_module();

	bool has(const RTLIL::IdString &id) const {
		return modules_.count(id) != 0;
	}

	void add(RTLIL::Module *module);
	void add(RTLIL::Binding *binding);

	RTLIL::Module *addModule(RTLIL::IdString name);
	void remove(RTLIL::Module *module);
	void rename(RTLIL::Module *module, RTLIL::IdString new_name);

	void scratchpad_unset(const std::string &varname);

	void scratchpad_set_int(const std::string &varname, int value);
	void scratchpad_set_bool(const std::string &varname, bool value);
	void scratchpad_set_string(const std::string &varname, std::string value);

	int scratchpad_get_int(const std::string &varname, int default_value = 0) const;
	bool scratchpad_get_bool(const std::string &varname, bool default_value = false) const;
	std::string scratchpad_get_string(const std::string &varname, const std::string &default_value = std::string()) const;

	void sort();
	void check();
	void optimize();

	bool selected_module(const RTLIL::IdString &mod_name) const;
	bool selected_whole_module(const RTLIL::IdString &mod_name) const;
	bool selected_member(const RTLIL::IdString &mod_name, const RTLIL::IdString &memb_name) const;

	bool selected_module(RTLIL::Module *mod) const;
	bool selected_whole_module(RTLIL::Module *mod) const;

	RTLIL::Selection &selection() {
		return selection_stack.back();
	}

	const RTLIL::Selection &selection() const {
		return selection_stack.back();
	}

	bool full_selection() const {
		return selection_stack.back().full_selection;
	}

	template<typename T1> bool selected(T1 *module) const {
		return selected_module(module->name);
	}

	template<typename T1, typename T2> bool selected(T1 *module, T2 *member) const {
		return selected_member(module->name, member->name);
	}

	template<typename T1> void select(T1 *module) {
		if (selection_stack.size() > 0) {
			RTLIL::Selection &sel = selection_stack.back();
			sel.select(module);
		}
	}

	template<typename T1, typename T2> void select(T1 *module, T2 *member) {
		if (selection_stack.size() > 0) {
			RTLIL::Selection &sel = selection_stack.back();
			sel.select(module, member);
		}
	}


	std::vector<RTLIL::Module*> selected_modules() const;
	std::vector<RTLIL::Module*> selected_whole_modules() const;
	std::vector<RTLIL::Module*> selected_whole_modules_warn(bool include_wb = false) const;
#ifdef WITH_PYTHON
	static std::map<unsigned int, RTLIL::Design*> *get_all_designs(void);
#endif
};

struct RTLIL::Module : public RTLIL::AttrObject
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

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

	RTLIL::IdString name;
	idict<RTLIL::IdString> avail_parameters;
	dict<RTLIL::IdString, RTLIL::Const> parameter_default_values;
	dict<RTLIL::IdString, RTLIL::Memory*> memories;
	dict<RTLIL::IdString, RTLIL::Process*> processes;

	Module();
	virtual ~Module();
	virtual RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, bool mayfail = false);
	virtual RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, const dict<RTLIL::IdString, RTLIL::Module*> &interfaces, const dict<RTLIL::IdString, RTLIL::IdString> &modports, bool mayfail = false);
	virtual size_t count_id(const RTLIL::IdString& id);
	virtual void expand_interfaces(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Module *> &local_interfaces);
	virtual bool reprocess_if_necessary(RTLIL::Design *design);

	virtual void sort();
	virtual void check();
	virtual void optimize();
	virtual void makeblackbox();

	void connect(const RTLIL::SigSig &conn);
	void connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs);
	void new_connections(const std::vector<RTLIL::SigSig> &new_conn);
	const std::vector<RTLIL::SigSig> &connections() const;

	std::vector<RTLIL::IdString> ports;
	void fixup_ports();

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	void cloneInto(RTLIL::Module *new_mod) const;
	virtual RTLIL::Module *clone() const;

	bool has_memories() const;
	bool has_processes() const;

	bool has_memories_warn() const;
	bool has_processes_warn() const;

	std::vector<RTLIL::Wire*> selected_wires() const;
	std::vector<RTLIL::Cell*> selected_cells() const;

	template<typename T> bool selected(T *member) const {
		return design->selected_member(name, member->name);
	}

	RTLIL::Wire* wire(const RTLIL::IdString &id) {
		auto it = wires_.find(id);
		return it == wires_.end() ? nullptr : it->second;
	}
	RTLIL::Cell* cell(const RTLIL::IdString &id) {
		auto it = cells_.find(id);
		return it == cells_.end() ? nullptr : it->second;
	}

	const RTLIL::Wire* wire(const RTLIL::IdString &id) const{
		auto it = wires_.find(id);
		return it == wires_.end() ? nullptr : it->second;
	}
	const RTLIL::Cell* cell(const RTLIL::IdString &id) const {
		auto it = cells_.find(id);
		return it == cells_.end() ? nullptr : it->second;
	}

	RTLIL::ObjRange<RTLIL::Wire*> wires() { return RTLIL::ObjRange<RTLIL::Wire*>(&wires_, &refcount_wires_); }
	RTLIL::ObjRange<RTLIL::Cell*> cells() { return RTLIL::ObjRange<RTLIL::Cell*>(&cells_, &refcount_cells_); }

	void add(RTLIL::Binding *binding);

	// Removing wires is expensive. If you have to remove wires, remove them all at once.
	void remove(const pool<RTLIL::Wire*> &wires);
	void remove(RTLIL::Cell *cell);
	void remove(RTLIL::Process *process);

	void rename(RTLIL::Wire *wire, RTLIL::IdString new_name);
	void rename(RTLIL::Cell *cell, RTLIL::IdString new_name);
	void rename(RTLIL::IdString old_name, RTLIL::IdString new_name);

	void swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2);
	void swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2);

	RTLIL::IdString uniquify(RTLIL::IdString name);
	RTLIL::IdString uniquify(RTLIL::IdString name, int &index);

	RTLIL::Wire *addWire(RTLIL::IdString name, int width = 1);
	RTLIL::Wire *addWire(RTLIL::IdString name, const RTLIL::Wire *other);

	RTLIL::Cell *addCell(RTLIL::IdString name, RTLIL::IdString type);
	RTLIL::Cell *addCell(RTLIL::IdString name, const RTLIL::Cell *other);

	RTLIL::Memory *addMemory(RTLIL::IdString name, const RTLIL::Memory *other);

	RTLIL::Process *addProcess(RTLIL::IdString name);
	RTLIL::Process *addProcess(RTLIL::IdString name, const RTLIL::Process *other);

	// The add* methods create a cell and return the created cell. All signals must exist in advance.

	RTLIL::Cell* addNot (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
	RTLIL::Cell* addPos (RTLIL::IdString name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed = false, const std::string &src = "");
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

#ifdef WITH_PYTHON
	static std::map<unsigned int, RTLIL::Module*> *get_all_modules(void);
#endif
};

struct RTLIL::Wire : public RTLIL::AttrObject
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

protected:
	// use module->addWire() and module->remove() to create or destroy wires
	friend struct RTLIL::Module;
	Wire();
	~Wire();

public:
	// do not simply copy wires
	Wire(RTLIL::Wire &other) = delete;
	void operator=(RTLIL::Wire &other) = delete;

	RTLIL::Module *module;
	RTLIL::IdString name;
	int width, start_offset, port_id;
	bool port_input, port_output, upto, is_signed;

#ifdef WITH_PYTHON
	static std::map<unsigned int, RTLIL::Wire*> *get_all_wires(void);
#endif
};

inline int GetSize(RTLIL::Wire *wire) {
	return wire->width;
}

struct RTLIL::Memory : public RTLIL::AttrObject
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

	Memory();

	RTLIL::IdString name;
	int width, start_offset, size;
#ifdef WITH_PYTHON
	~Memory();
	static std::map<unsigned int, RTLIL::Memory*> *get_all_memorys(void);
#endif
};

struct RTLIL::Cell : public RTLIL::AttrObject
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

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
	RTLIL::IdString name;
	RTLIL::IdString type;
	dict<RTLIL::IdString, RTLIL::SigSpec> connections_;
	dict<RTLIL::IdString, RTLIL::Const> parameters;

	// access cell ports
	bool hasPort(const RTLIL::IdString &portname) const;
	void unsetPort(const RTLIL::IdString &portname);
	void setPort(const RTLIL::IdString &portname, RTLIL::SigSpec signal);
	const RTLIL::SigSpec &getPort(const RTLIL::IdString &portname) const;
	const dict<RTLIL::IdString, RTLIL::SigSpec> &connections() const;

	// information about cell ports
	bool known() const;
	bool input(const RTLIL::IdString &portname) const;
	bool output(const RTLIL::IdString &portname) const;

	// access cell parameters
	bool hasParam(const RTLIL::IdString &paramname) const;
	void unsetParam(const RTLIL::IdString &paramname);
	void setParam(const RTLIL::IdString &paramname, RTLIL::Const value);
	const RTLIL::Const &getParam(const RTLIL::IdString &paramname) const;

	void sort();
	void check();
	void fixup_parameters(bool set_a_signed = false, bool set_b_signed = false);

	bool has_keep_attr() const {
		return get_bool_attribute(ID::keep) || (module && module->design && module->design->module(type) &&
				module->design->module(type)->get_bool_attribute(ID::keep));
	}

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);

#ifdef WITH_PYTHON
	static std::map<unsigned int, RTLIL::Cell*> *get_all_cells(void);
#endif

	bool has_memid() const;
	bool is_mem_cell() const;
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

struct RTLIL::Process : public RTLIL::AttrObject
{
	unsigned int hashidx_;
	unsigned int hash() const { return hashidx_; }

protected:
	// use module->addProcess() and module->remove() to create or destroy processes
	friend struct RTLIL::Module;
	Process();
	~Process();

public:
	RTLIL::IdString name;
	RTLIL::Module *module;
	RTLIL::CaseRule root_case;
	std::vector<RTLIL::SyncRule*> syncs;

	template<typename T> void rewrite_sigspecs(T &functor);
	template<typename T> void rewrite_sigspecs2(T &functor);
	RTLIL::Process *clone() const;
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

inline unsigned int RTLIL::SigBit::hash() const {
	if (wire)
		return mkhash_add(wire->name.hash(), offset);
	return data;
}

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

YOSYS_NAMESPACE_END

#endif
