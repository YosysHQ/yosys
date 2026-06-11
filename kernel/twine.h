#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/yosys_common.h"
#include "kernel/hashlib.h"

#include <cassert>

#include "libs/plf_colony/plf_colony.h"
#include <cstdint>
#include <limits>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <list>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct Twine;
struct TwinePool;

struct TwineRef {
	size_t value;

	static constexpr size_t kLocalBit  = 1ULL << 63;
	static constexpr size_t kPublicBit = 1ULL << 62;
	static constexpr size_t kTagMask   = kLocalBit | kPublicBit;
	static constexpr size_t kNull      = ~size_t{0};

	constexpr TwineRef() : value(0) {}
	constexpr TwineRef(size_t val) : value(val) {}
	constexpr operator size_t() const { return value; }

	template <typename... Args>
	constexpr bool in(const Args&... args) const {
		return ((*this == args) || ...);
	}

	constexpr TwineRef operator|(TwineRef rhs) const { return TwineRef(value | rhs.value); }
	constexpr TwineRef operator&(TwineRef rhs) const { return TwineRef(value & rhs.value); }
	constexpr TwineRef operator~() const { return TwineRef(~value); }
	constexpr TwineRef& operator++() { ++value; return *this; }
	constexpr TwineRef  operator++(int) { return TwineRef(value++); }

	constexpr bool is_public() const { return value != kNull && (value & kPublicBit); }
	constexpr bool is_local()  const { return value != kNull && (value & kLocalBit); }

	constexpr TwineRef untag() const {
		return value == kNull ? *this : TwineRef(value & ~kPublicBit);
	}
	constexpr TwineRef tag(bool pub) const {
		return value == kNull ? *this : TwineRef(pub ? (value | kPublicBit) : (value & ~kPublicBit));
	}

	Hasher hash_into(Hasher h) const { h.hash64(value); return h; }
};

// Tags TwineChildPool-local refs; never set on refs handed out by TwinePool.
constexpr TwineRef TWINE_LOCAL_BIT = TwineRef(1LLU << 63);
// Publicity tag carried on name handles. Pool nodes store name *content*
// (no '\' escape); whether a name is public lives in this bit of the
// handle, never inside the pool. TwinePool strips it on every entry path.
constexpr TwineRef TWINE_PUBLIC_BIT = TwineRef(1LLU << 62);
constexpr TwineRef TWINE_TAG_MASK = TWINE_LOCAL_BIT | TWINE_PUBLIC_BIT;

enum : short {
	STATIC_TWINE_BEGIN = 0,
#define X(N) IDX_##N,
#include "kernel/constids.inc"
#undef X
	STATIC_TWINE_END
};

struct TW {
// Static ids are name handles: non-'$' constids were '\'-escaped publics,
// so their handles carry TWINE_PUBLIC_BIT baked in at compile time.
#define X(N) static constexpr TwineRef N = (#N)[0] == '$' ? TwineRef(IDX_##N) : (TwineRef(IDX_##N) | TWINE_PUBLIC_BIT);
#include "kernel/constids.inc"
#undef X

	static constexpr TwineRef lookup(std::string_view name)
	{
#define X(N) \
		if (name == #N) return N;
#include "kernel/constids.inc"
#undef X

		throw "unknown twine id";
	}
};

#define TW(id) (size_t)lookup_well_known_id(#id)
// #define TW(name) TW::lookup(#name)

struct Twine {
	static constexpr TwineRef Null = std::numeric_limits<size_t>::max();

	struct Suffix {
		TwineRef prefix;
		std::string tail;
		// TODO check
		auto operator<=>(const Suffix&) const = default;
	};

	std::variant<std::monostate, std::string, std::vector<TwineRef>, Suffix> data;

	bool is_dead() const { return std::holds_alternative<std::monostate>(data); }
	bool is_leaf() const { return std::holds_alternative<std::string>(data); }
	bool is_concat() const { return std::holds_alternative<std::vector<TwineRef>>(data); }
	bool is_suffix() const { return std::holds_alternative<Suffix>(data); }
	bool is_flat() const { return is_leaf() || is_suffix(); }
	const std::string &leaf() const { return std::get<std::string>(data); }
	const std::vector<TwineRef> &children() const { return std::get<std::vector<TwineRef>>(data); }
	const Suffix &suffix() const { return std::get<Suffix>(data); }
};

constexpr bool twine_is_public(TwineRef ref) { return ref.is_public(); }
constexpr TwineRef twine_untag(TwineRef ref)  { return ref.untag(); }
constexpr TwineRef twine_tag(TwineRef ref, bool is_public) { return ref.tag(is_public); }

struct TwineHash {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	size_t operator()(const Twine& t) const noexcept;
	size_t operator()(TwineRef ref) const noexcept;
	// size_t operator()(std::string_view v) const noexcept;
};

struct TwineEq {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	bool operator()(TwineRef a, TwineRef b) const noexcept;
	bool operator()(TwineRef a, const Twine& b) const noexcept;
	bool operator()(const Twine& a, TwineRef b) const noexcept;
	// bool operator()(TwineRef a, std::string_view b) const noexcept;
	// bool operator()(std::string_view a, TwineRef b) const noexcept;
};


TwineRef twine_populate(std::string name);
void twine_prepopulate();

struct TwinePool {
	static std::vector<Twine> globals_;
	plf::colony<Twine> backing;
	std::unordered_set<TwineRef, TwineHash, TwineEq> index;

	const Twine& operator[] (TwineRef ref) const {
		ref = twine_untag(ref);
		if (ref < STATIC_TWINE_END)
			return globals_[ref];
		else
			return backing[ref - STATIC_TWINE_END];
	}

	void dump(TwineRef ref, std::ostream& os = std::cout) const {
		const Twine& twine = (*this)[ref];
		std::visit([&](const auto& val) {
			using T = std::decay_t<decltype(val)>;
			if constexpr (std::is_same_v<T, std::monostate>) {
				os << "Dead()";
			} else if constexpr (std::is_same_v<T, std::string>) {
				os << "Leaf(\"" << val << "\")";
			} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
				os << "Concat[";
				for (size_t i = 0; i < val.size(); ++i) {
					if (i > 0)
						os << ", ";
					dump(val[i], os);
				}
				os << "]";
			} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
				os << "Suffix(prefix: ";
				dump(val.prefix, os);
				os << ", tail: \"" << val.tail << "\")";
			}
		}, twine.data);
	}
	void print(TwineRef ref, std::ostream& os = std::cout) const {
		if (ref == Twine::Null)
			return;
		if (twine_is_public(ref))
			os << '\\';
		std::visit([&](const auto& val) {
			using T = std::decay_t<decltype(val)>;
			if constexpr (std::is_same_v<T, std::monostate>) {
			} else if constexpr (std::is_same_v<T, std::string>) {
				os << val;
			} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
				for (size_t i = 0; i < val.size(); ++i) {
					if (i > 0)
						os << "|";
					print(val[i], os);
				}
			} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
				print(val.prefix, os);
				os << val.tail;
			}
		}, (*this)[ref].data);
	}
	// Escaped form: leading '\' for public name handles, content otherwise.
	std::string str(TwineRef ref) const {
		std::ostringstream os;
		print(ref, os);
		return os.str();
	}

	// Name content without the publicity escape.
	std::string unescaped_str(TwineRef ref) const {
		return str(twine_untag(ref));
	}

	TwinePool() : index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool(const TwinePool& other) : backing(other.backing), index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool(TwinePool&& other) : backing(std::move(other.backing)), index(0, TwineHash{this}, TwineEq{this}) {
		rebuild_index();
	}
	TwinePool& operator=(const TwinePool& other) {
		if (this != &other) {
			backing = other.backing;
			index = std::unordered_set<TwineRef, TwineHash, TwineEq>(0, TwineHash{this}, TwineEq{this});
			rebuild_index();
		}
		return *this;
	}
	TwinePool& operator=(TwinePool&& other) {
		if (this != &other) {
			backing = std::move(other.backing);
			index = std::unordered_set<TwineRef, TwineHash, TwineEq>(0, TwineHash{this}, TwineEq{this});
			rebuild_index();
		}
		return *this;
	}

	void rebuild_index() {
		for (TwineRef ref = 0; ref < globals_.size(); ref++)
			index.insert(ref);
		for (auto it = backing.begin(); it != backing.end(); ++it)
			index.insert(STATIC_TWINE_END + backing.get_index(it));
	}

	TwineRef find(Twine t) const {
		if (auto *children = std::get_if<std::vector<TwineRef>>(&t.data)) {
			for (TwineRef &c : *children)
				c = twine_untag(c);
		} else if (auto *sfx = std::get_if<Twine::Suffix>(&t.data)) {
			sfx->prefix = twine_untag(sfx->prefix);
		}
		if (auto it = index.find(t); it != index.end()) {
			return *it;
		}
		return Twine::Null;
	}

	TwineRef add_inner(Twine t) {
		// Nodes store content only: strip publicity tags off child handles.
		if (auto *children = std::get_if<std::vector<TwineRef>>(&t.data)) {
			for (TwineRef &c : *children)
				c = twine_untag(c);
		} else if (auto *sfx = std::get_if<Twine::Suffix>(&t.data)) {
			sfx->prefix = twine_untag(sfx->prefix);
		}

		if (auto it = index.find(t); it != index.end()) {
			return *it;
		}

		auto colony_it = backing.insert(std::move(t));
		TwineRef ref = STATIC_TWINE_END + backing.get_index(colony_it);
		index.insert(ref);
		return ref;
	}

	// Interns an object name and returns a publicity-tagged handle. Leaf
	// strings follow the escaped convention: a leading '\' marks a public
	// name (stripped from the stored content), '$' a private one. Suffix
	// and concat names inherit the prefix/first-child handle's publicity.
	TwineRef add(Twine t) {
		bool is_public = false;
		if (auto *leaf = std::get_if<std::string>(&t.data)) {
			assert(!leaf->empty());
			if ((*leaf)[0] == '\\') {
				is_public = true;
				leaf->erase(0, 1);
				assert(!leaf->empty());
			} else {
				assert((*leaf)[0] == '$');
			}
		} else if (auto *sfx = std::get_if<Twine::Suffix>(&t.data)) {
			is_public = twine_is_public(sfx->prefix);
		} else if (auto *children = std::get_if<std::vector<TwineRef>>(&t.data)) {
			is_public = false;
		}
		return twine_tag(add_inner(std::move(t)), is_public);
	}

	TwineRef add(std::string&& s) {
		if (s.size()) {
			if (s[0] == '\\')
				return twine_tag(add(Twine{s.substr(1)}), true);
			else
				return twine_tag(add(Twine{std::move(s)}), true);
		} else {
		 	return Twine::Null;
		}
	}

	size_t size() const { return backing.size(); }

	TwineRef concat(std::span<const TwineRef> ids) {
		if (ids.size() == 1)
			return ids[0];
		return add(Twine{std::vector<TwineRef>(ids.begin(), ids.end())});
	}

	TwineRef copy_from(const TwinePool& src, TwineRef ref) {
		if (ref == Twine::Null)
			return ref;
		// Statics are shared across pools; preserve the handle's publicity
		// tag across the copy in either case.
		bool is_public = twine_is_public(ref);
		TwineRef untagged = twine_untag(ref);
		if (untagged < STATIC_TWINE_END)
			return ref;
		const Twine& t = src[untagged];
		if (t.is_leaf())
			return twine_tag(add(Twine{t.leaf()}), is_public);
		if (t.is_concat()) {
			std::vector<TwineRef> children;
			children.reserve(t.children().size());
			for (TwineRef c : t.children())
				children.push_back(copy_from(src, c));
			return twine_tag(add(Twine{std::move(children)}), is_public);
		}
		if (t.is_suffix())
			return twine_tag(add(Twine{Twine::Suffix{copy_from(src, t.suffix().prefix), t.suffix().tail}}), is_public);
		return Twine::Null;
	}

	// linear deep scan; only for rare by-string lookups. Accepts the
	// escaped name convention: a leading '\' is stripped and the returned
	// handle carries TWINE_PUBLIC_BIT.
	TwineRef lookup(std::string_view sv) const;

	// Erases every backing node not reachable from `roots`; refs to
	// surviving nodes stay valid. Returns the number of erased nodes.
	template<typename Pool>
	size_t gc(const Pool& roots) {
		pool<TwineRef> live;
		for (TwineRef ref : roots)
			mark_live(ref, live);
		size_t erased = 0;
		for (auto it = backing.begin(); it != backing.end();) {
			TwineRef ref = STATIC_TWINE_END + backing.get_index(it);
			if (live.count(ref)) {
				++it;
			} else {
				index.erase(ref);
				it = backing.erase(it);
				erased++;
			}
		}
		return erased;
	}

	void mark_live(TwineRef ref, pool<TwineRef>& live) const {
		ref = twine_untag(ref);
		if (ref == Twine::Null || ref < STATIC_TWINE_END || !live.insert(ref).second)
			return;
		const Twine& t = (*this)[ref];
		if (t.is_concat()) {
			for (TwineRef c : t.children())
				mark_live(c, live);
		} else if (t.is_suffix()) {
			mark_live(t.suffix().prefix, live);
		}
	}

	void dump(std::ostream& os = std::cout) const {
		os << "--- TwinePool Dump (" << backing.size() << " nodes) ---\n";
		for (auto it = backing.begin(); it != backing.end(); ++it) {
			TwineRef ref = STATIC_TWINE_END + backing.get_index(it);
			os << ref << " -> ";
			dump(ref, os);
			os << '\n';
		}
		os << "--------------------------------\n";
	}
	// Silly compat
	std::string flat_string(TwineRef t) const { return str(t); }
};

inline size_t TwineHash::operator()(const Twine& t) const noexcept {
	// size_t h = std::hash<size_t>{}(t.data.index());
	Hasher h;

	std::visit([&h](const auto& val) {
		using T = std::decay_t<decltype(val)>;

		// auto combine = [&h](auto v) {
		// 	h ^= v + 0x9e3779b9 + (h << 6) + (h >> 2);
		// };

		if constexpr (std::is_same_v<T, std::string>) {
			h.eat(val);
			// combine(std::hash<std::string>{}(val));
		} else if constexpr (std::is_same_v<T, std::vector<TwineRef>>) {
			for (auto ref : val) {
				h.eat(ref);
				// combine(std::hash<TwineRef>{}(ref));
			}
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			h.eat(val.prefix);
			h.eat(val.tail);
			// combine(std::hash<TwineRef>{}(val.prefix));
			// combine(std::hash<std::string>{}(val.tail));
		}
	}, t.data);

	return h.yield();
}

inline size_t TwineHash::operator()(TwineRef ref) const noexcept {
	return (*this)((*pool)[ref]);
}

inline bool TwineEq::operator()(TwineRef a, TwineRef b) const noexcept {
	return (*pool)[a].data == (*pool)[b].data;
}

inline bool TwineEq::operator()(TwineRef a, const Twine& b) const noexcept {
	return (*pool)[a].data == b.data;
}

inline bool TwineEq::operator()(const Twine& a, TwineRef b) const noexcept {
	return a.data == (*pool)[b].data;
}


struct DeepTwineHash {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	// FNV-1a constants for 64-bit
	static constexpr size_t FNV_OFFSET_BASIS = 14695981039346656037ull;
	static constexpr size_t FNV_PRIME = 1099511628211ull;

	static void combine(size_t& hash, std::string_view sv) noexcept {
		for (char c : sv) {
			hash ^= static_cast<size_t>(c);
			hash *= FNV_PRIME;
		}
	}

	// Recursively hash the fragments of a Twine
	void combine(size_t& hash, TwineRef t) const noexcept {
		if (t == Twine::Null)
			return;
		const Twine& n = (*pool)[t];
		if (n.is_dead()) return;

		if (n.is_leaf()) {
			combine(hash, std::string_view(n.leaf()));
		} else if (n.is_concat()) {
			for (auto child : n.children()) combine(hash, child);
		} else if (n.is_suffix()) {
			combine(hash, n.suffix().prefix);
			combine(hash, std::string_view(n.suffix().tail));
		}
	}

	size_t operator()(std::string_view sv) const noexcept {
		size_t h = FNV_OFFSET_BASIS;
		combine(h, sv);
		return h;
	}

	size_t operator()(TwineRef t) const noexcept {
		size_t h = FNV_OFFSET_BASIS;
		combine(h, t);
		return h;
	}
};

struct DeepTwineEq {
	using is_transparent = void;

	const TwinePool* pool = nullptr;

	// Recursively consumes the string_view to check for deep equality
	bool consume(TwineRef t, std::string_view& sv) const noexcept {
		if (t == Twine::Null)
			return true;
		const Twine& n = (*pool)[t];
		if (n.is_dead()) return true;

		if (n.is_leaf()) {
			if (!sv.starts_with(n.leaf())) return false;
			sv.remove_prefix(n.leaf().size());
			return true;
		} else if (n.is_concat()) {
			for (auto child : n.children()) {
				if (!consume(child, sv)) return false;
			}
			return true;
		} else if (n.is_suffix()) {
			if (!consume(n.suffix().prefix, sv)) return false;
			if (!sv.starts_with(n.suffix().tail)) return false;
			sv.remove_prefix(n.suffix().tail.size());
			return true;
		}
		return false;
	}

	bool operator()(TwineRef t, std::string_view sv) const noexcept {
		return consume(t, sv) && sv.empty();
	}

	bool operator()(std::string_view sv, TwineRef t) const noexcept {
		return (*this)(t, sv);
	}

	// Required by unordered_set to handle hash collisions between two TwineRefs.
	bool operator()(TwineRef a, TwineRef b) const {
		if (a == b) return true; // Index or structural equality shortcut
		std::string fb = flatten(b);
		return (*this)(a, std::string_view(fb));
	}

	// Helper to flatten a twine (used only during rare hash collisions)
	std::string flatten(TwineRef t) const {
		std::string result;
		auto append = [&](auto& self, TwineRef ref) -> void {
			if (ref == Twine::Null)
				return;
			const Twine& node = (*pool)[ref];
			if (node.is_dead()) return;
			if (node.is_leaf()) result += node.leaf();
			else if (node.is_concat()) {
				for (auto child : node.children()) self(self, child);
			} else if (node.is_suffix()) {
				self(self, node.suffix().prefix);
				result += node.suffix().tail;
			}
		};
		append(append, t);
		return result;
	}
};

// Parallel-safe staging while the parent stays read-only; nodes may reference parent refs and earlier local refs
struct TwineChildPool {
	const TwinePool* parent;
	std::vector<Twine> local_;
	std::vector<TwineRef> remap_;

	TwineChildPool(const TwinePool* parent) : parent(parent) {}

	static bool is_local(TwineRef ref) { return ref.is_local(); }

	const Twine& operator[] (TwineRef ref) const {
		if (is_local(ref))
			return local_[ref & ~TWINE_TAG_MASK];
		return (*parent)[ref];
	}

	TwineRef add_inner(Twine t) {
		local_.push_back(std::move(t));
		return (local_.size() - 1) | TWINE_LOCAL_BIT;
	}

	// Local analog of TwinePool::add; see there for the convention.
	TwineRef add(Twine t) {
		bool is_public = false;
		if (auto *leaf = std::get_if<std::string>(&t.data)) {
			assert(!leaf->empty());
			if ((*leaf)[0] == '\\') {
				is_public = true;
				leaf->erase(0, 1);
				assert(!leaf->empty());
			} else {
				assert((*leaf)[0] == '$');
			}
		} else if (auto *sfx = std::get_if<Twine::Suffix>(&t.data)) {
			is_public = twine_is_public(sfx->prefix);
		} else if (auto *children = std::get_if<std::vector<TwineRef>>(&t.data)) {
			is_public = !children->empty() && twine_is_public(children->front());
		}
		return twine_tag(add_inner(std::move(t)), is_public);
	}

	// TODO duplicated code
	TwineRef add(std::string&& s) {
		if (s.size()) {
			if (s[0] == '\\')
				return twine_tag(add(Twine{s.substr(1)}), true);
			else
				return twine_tag(add(Twine{std::move(s)}), true);
		} else {
		 	return Twine::Null;
		}
	}

	bool empty() const { return local_.empty(); }

	// serial phase only; dest must be *parent; resolve() covers refs added since the previous commit
	void commit_into(TwinePool& dest) {
		remap_.clear();
		remap_.reserve(local_.size());
		for (Twine& t : local_) {
			if (t.is_concat()) {
				for (TwineRef& c : std::get<std::vector<TwineRef>>(t.data))
					c = resolve(c);
			} else if (t.is_suffix()) {
				std::get<Twine::Suffix>(t.data).prefix = resolve(std::get<Twine::Suffix>(t.data).prefix);
			}
			remap_.push_back(dest.add(std::move(t)));
		}
		local_.clear();
	}

	TwineRef resolve(TwineRef ref) const {
		if (!is_local(ref))
			return ref;
		return twine_tag(remap_[ref & ~TWINE_TAG_MASK], twine_is_public(ref));
	}
};

inline TwineRef TwinePool::lookup(std::string_view sv) const {
	bool is_public = !sv.empty() && sv[0] == '\\';
	if (is_public)
		sv.remove_prefix(1);
	DeepTwineEq eq{this};
	for (TwineRef ref = 0; ref < globals_.size(); ref++)
		if (eq(ref, sv))
			return twine_tag(ref, is_public);
	for (auto it = backing.begin(); it != backing.end(); ++it) {
		TwineRef ref = STATIC_TWINE_END + backing.get_index(it);
		if (eq(ref, sv))
			return twine_tag(ref, is_public);
	}
	return Twine::Null;
}

struct TwineSearch {
	TwinePool* pool;
	std::unordered_set<TwineRef, DeepTwineHash, DeepTwineEq> index;
	TwineSearch(TwinePool* pool) : pool(pool), index(0, DeepTwineHash{pool}, DeepTwineEq{pool}) {
		for (auto it = pool->backing.begin(); it != pool->backing.end(); ++it) {
			index.insert(STATIC_TWINE_END + pool->backing.get_index(it));
		}
	}
	// Escaped-name aware, same contract as TwinePool::lookup.
	TwineRef find(std::string_view sv) const {
		bool is_public = !sv.empty() && sv[0] == '\\';
		if (is_public)
			sv.remove_prefix(1);
		if (auto it = index.find(sv); it != index.end()) {
			return twine_tag(*it, is_public);
		}
		return Twine::Null;
	}
};

// struct TwinePoolExtender {
// 	TwinePool& pool;
// 	size_t offset;
// private:
// 	size_t resize_for_idx(size_t idx) {
// 		auto real_idx = offset + idx;
// 		pool.nodes_.resize(std::max(pool.nodes_.size(), real_idx + 1));
// 		return real_idx;
// 	}
// 	void commit(Twine&& twine, size_t idx) {
// 		pool.nodes_[idx] = std::move(twine);
// 		pool.leaf_index_.insert(&pool.nodes_[idx]);
// 	}
// public:
// 	// TwinePoolExtender(Design* design) : pool(design->twines), offset(design->twines.size()) {}
// 	void extend_leaf(std::string leaf, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		commit(Twine(leaf), real_idx);
// 	}
// 	void extend_concat(std::vector<size_t> children, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		Twine* first = &pool.nodes_.front() + offset;
// 		std::vector<Twine*> real_children;
// 		real_children.reserve(children.size());
// 		for (auto child : children)
// 			real_children.push_back(first + child);
// 		commit(Twine(std::move(real_children)), real_idx);
// 	}
// 	void extend_suffix(size_t prefix, std::string tail, size_t idx) {
// 		auto real_idx = resize_for_idx(idx);
// 		Twine* first = &pool.nodes_.front() + offset;
// 		Twine* real_prefix = first + prefix;
// 		commit(Twine(Twine::Suffix(real_prefix, std::move(tail))), real_idx);
// 	}
// 	void finish() {
// 		for (size_t i = offset; i < pool.nodes_.size(); i++)
// 			if (pool.nodes_[i].is_dead())
// 				pool.free_list_.push_back(&pool.nodes_[i]);
// 	}
// };

YOSYS_NAMESPACE_END

#endif
