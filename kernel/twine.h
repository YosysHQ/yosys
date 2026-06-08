#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/yosys_common.h"

#include <cstdint>
#include <limits>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>
#include <list>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

// A Twine is an interned, possibly composite source-location string. Leaves
// are flat path:line.col substrings (the existing src-attribute literal). A
// Concat node holds an ordered sequence of child twines, so merging the src
// of N cells is O(N) lookups plus one concat-table probe — independent of
// the total path-string length the materialized result would have.
//
// Twines are valid only relative to the TwinePool that minted them. The pool
// lives on RTLIL::Design (design->twines).
struct Twine
{
	using Id = Twine*;
	static constexpr Id Null = nullptr;

	// Suffix shares a `prefix` prefix with other suffixes and contributes
	// its own `tail` string. The materialized leaf string is
	// flat_string(prefix) + tail, i.e. suffixes form trees whose leaves
	// (string variant) are the roots — like a reverse-trie of common
	// prefixes. The prefix is itself flat (Leaf or Suffix), never a
	// Concat.
	struct Suffix {
		Id prefix;
		std::string tail;
	};

	// Leaf holds the literal path:line.col string. Suffix holds a prefix
	// id + own tail (see above). Concat holds the ordered children.
	// Concats are kept flat by TwinePool::concat — children are always
	// flat (Leaf or Suffix), never other Concats. monostate is the
	// tombstone marker for freed slots awaiting reuse via the free list.
	std::variant<std::monostate, std::string, std::vector<Id>, Suffix> data;

	bool is_dead() const { return std::holds_alternative<std::monostate>(data); }
	bool is_leaf() const { return std::holds_alternative<std::string>(data); }
	bool is_concat() const { return std::holds_alternative<std::vector<Id>>(data); }
	bool is_suffix() const { return std::holds_alternative<Suffix>(data); }
	bool is_flat() const { return is_leaf() || is_suffix(); }
	const std::string &leaf() const { return std::get<std::string>(data); }
	const std::vector<Id> &children() const { return std::get<std::vector<Id>>(data); }
	const Suffix &suffix() const { return std::get<Suffix>(data); }
};

struct TwinePoolExtender;
class TwinePool
{
private:
	friend struct TwinePoolExtender;
	uint32_t& refcount(Twine::Id id);
public:
	TwinePool();
	// Custom copy: functor pointers must target the NEW pool's nodes_.
	TwinePool(const TwinePool &other);
	TwinePool &operator=(const TwinePool &other);
	// Move is deleted; the intrusive functors hold `this`, so a move would
	// silently leave them pointing at the old (now-empty) pool.
	TwinePool(TwinePool &&) = delete;
	TwinePool &operator=(TwinePool &&) = delete;

	// Intern a leaf string. Returns the same Id for byte-equal inputs. The
	// returned Id carries one reference for the caller — release it when
	// you are done holding it. Empty input returns Twine::Null.
	Twine::Id intern(std::string_view leaf);

	// Intern a Suffix node. The resulting flat string is
	// flat_string(prefix) + tail. `prefix` must be a flat node (Leaf or
	// Suffix) — pass Twine::Null with a non-empty `tail` to fall back to
	// intern(tail). Suffixes with the same (prefix, tail) dedup. The
	// returned Id carries one reference for the caller. Internally the
	// new suffix retains a reference on `prefix`; releasing the suffix
	// releases that internal prefix ref. Empty `tail` returns `prefix`
	// (with +1 ref for the caller).
	Twine::Id intern_suffix(Twine::Id prefix, std::string_view tail);

	// Build a Concat node referencing `parts` in order. Concat children are
	// always leaves (flat-leaf invariant): any Concat passed in `parts` has
	// its leaves spliced in instead. Duplicate leaves and Twine::Null are
	// dropped. If only one distinct leaf remains its Id is returned directly
	// (no Concat node created). Concats with the same child sequence dedup.
	// The returned Id carries one reference for the caller. Internally the
	// concat retains each child it stores; releasing the concat releases
	// those internal child references.
	Twine::Id concat(std::span<const Twine::Id> parts);
	Twine::Id concat(Twine::Id a, Twine::Id b);

	// Non-interning lookup: return the Id of the leaf whose string equals
	// `sv`, or Twine::Null if no such leaf exists. Does not allocate.
	Twine::Id lookup(std::string_view sv) const;

	// Refcount control. retain bumps; release decrements and, on reaching
	// zero, marks the slot dead, drops it from the dedup indexes, releases
	// any child refs the slot owned, and pushes the slot id onto the free
	// list for reuse by the next intern/concat. Both no-op on Twine::Null.

	size_t index(Twine* p) const;
	void retain(Twine::Id id);
	void release(Twine::Id id);
	uint32_t refcount(Twine::Id id) const;
	bool is_alive(Twine::Id id) const;

	// Quick character queries on any flat node — avoids materializing the
	// full string for the common `name[0] == '$'` / `.isPublic()` tests.
	char first_char(Twine::Id id) const;
	bool is_public(Twine::Id id) const { return first_char(id) == '\\'; }

	// Materialize a Twine to the pipe-separated flat string used by the
	// existing src attribute convention. Leaves visit in left-to-right DFS
	// order; duplicate leaves are skipped to match `pool`-style semantics.
	std::string flatten(Twine::Id id, char sep = '|') const;

	// Materialize a flat node (Leaf or Suffix) to its single string. id
	// must be a flat node (not a Concat) and not Twine::Null.
	std::string flat_string(Twine::Id id) const { return flat_string_(id); }

	// Format an interned Id as the canonical src-attribute reference "@N".
	// Twine::Null formats as the empty string.
	std::string format_ref(Twine::Id id) const;

	// Parse an "@N" reference back to an Id
	static std::optional<size_t> parse_ref(std::string_view s);
	Twine::Id get_ref(std::string_view s);

	const Twine &operator[](Twine::Id id) const { return *id; }

	size_t size() const { return nodes_.size(); }
	size_t leaf_count() const { return leaf_index_.size(); }
	size_t concat_count() const { return concat_index_.size(); }
	size_t suffix_count() const { return suffix_index_.size(); }

	// One-shot debug dump of the entire pool to stdout via log(). Each leaf
	// shows its string; each concat shows its child id list. Intended for
	// `dump -twines` or ad-hoc tracing — output volume scales with size().
	void dump(const char *banner = nullptr) const;

	// Rebuild the pool to contain only the nodes named in `live` plus the
	// transitive children of any live concats. Returns an old-id -> new-id
	// remap; ids not in the result are dead. Callers must rewrite every
	// stored "@N" cell src through the returned remap immediately, since
	// after this call the old ids no longer mean what they used to.
	dict<Twine::Id, Twine::Id> gc(const pool<Twine::Id> &live);

	// Reconstruct `src->nodes_[src_id]` inside *this. Walks the structure
	// — intern leaves, concat children — so a concat in `src` becomes a
	// concat in this pool, not a flat literal of its leaves. Returns the
	// id in this pool with +1 for the caller (release when done). Both
	// pools may differ; the source is consulted read-only.
	Twine::Id copy_from(const TwinePool &src, Twine::Id src_id);

	// Iterate every live (non-tombstoned) node. fn is `void(Twine::Id, const Twine&)`.
	template <typename Fn>
	void for_each_live(Fn fn) const {
		for (auto& n : nodes_) {
			if (n.is_dead())
				continue;
			fn(&n, n); // TODO de-stupid this
		}
	}

private:
	std::vector<Twine> nodes_;
	std::vector<uint32_t> refcount_;
	std::list<Twine::Id> free_list_;

	// --- Intrusive dedup indexes (Step 0) -----------------------------------
	// Each set stores only the Twine::Id; hash/eq functors reach into
	// nodes_[id] for the keying data. This avoids the duplicate-string cost
	// of the old dict<std::string, Twine::Id> approach.
	// All functors hold a raw pointer to *this; TwinePool is non-movable
	// and copy-assignment rebuilds the sets from scratch so the pointer
	// always stays valid.

	using SuffixKey = std::pair<Twine::Id, std::string_view>;

	struct LeafHash {
		using is_transparent = void;
		const TwinePool *pool;
		size_t operator()(Twine::Id id) const noexcept {
			return std::hash<std::string_view>{}(id->leaf());
		}
		size_t operator()(std::string_view sv) const noexcept {
			return std::hash<std::string_view>{}(sv);
		}
	};
	struct LeafEq {
		using is_transparent = void;
		const TwinePool *pool;
		bool operator()(Twine::Id a, Twine::Id b) const noexcept {
			return a->leaf() == b->leaf();
		}
		bool operator()(Twine::Id id, std::string_view sv) const noexcept {
			return id->leaf() == sv;
		}
		bool operator()(std::string_view sv, Twine::Id id) const noexcept {
			return sv == id->leaf();
		}
	};
	struct SuffixHash {
		using is_transparent = void;
		const TwinePool *pool;
		static size_t combine(size_t a, size_t b) noexcept {
			return a ^ (b + 0x9e3779b9u + (a << 6) + (a >> 2));
		}
		size_t operator()(Twine::Id id) const noexcept {
			const auto &s = id->suffix();
			return combine(std::hash<Twine::Id>{}(s.prefix),
			               std::hash<std::string_view>{}(s.tail));
		}
		size_t operator()(SuffixKey k) const noexcept {
			return combine(std::hash<Twine::Id>{}(k.first),
			               std::hash<std::string_view>{}(k.second));
		}
	};
	struct SuffixEq {
		using is_transparent = void;
		const TwinePool *pool;
		bool operator()(Twine::Id a, Twine::Id b) const noexcept {
			const auto &sa = a->suffix();
			const auto &sb = b->suffix();
			return sa.prefix == sb.prefix && sa.tail == sb.tail;
		}
		bool operator()(Twine::Id id, SuffixKey k) const noexcept {
			const auto &s = id->suffix();
			return s.prefix == k.first && s.tail == k.second;
		}
		bool operator()(SuffixKey k, Twine::Id id) const noexcept {
			return (*this)(id, k);
		}
	};
	struct ConcatHash {
		using is_transparent = void;
		const TwinePool *pool;
		static size_t hash_ids(std::span<const Twine::Id> v) noexcept {
			size_t h = 0;
			for (Twine::Id c : v)
				h ^= std::hash<Twine::Id>{}(c) + 0x9e3779b9u + (h << 6) + (h >> 2);
			return h;
		}
		size_t operator()(Twine::Id id) const noexcept {
			return hash_ids(id->children());
		}
		size_t operator()(std::span<const Twine::Id> v) const noexcept {
			return hash_ids(v);
		}
	};
	struct ConcatEq {
		using is_transparent = void;
		const TwinePool *pool;
		bool operator()(Twine::Id a, Twine::Id b) const noexcept {
			return a->children() == b->children();
		}
		bool operator()(Twine::Id id, std::span<const Twine::Id> v) const noexcept {
			const auto &ch = id->children();
			return ch.size() == v.size() &&
			       std::equal(ch.begin(), ch.end(), v.begin());
		}
		bool operator()(std::span<const Twine::Id> v, Twine::Id id) const noexcept {
			return (*this)(id, v);
		}
	};

	std::unordered_set<Twine::Id, LeafHash,   LeafEq>   leaf_index_;
	std::unordered_set<Twine::Id, SuffixHash, SuffixEq> suffix_index_;
	std::unordered_set<Twine::Id, ConcatHash, ConcatEq> concat_index_;
	// -------------------------------------------------------------------------

	Twine::Id alloc_slot_(Twine &&node);
	void destroy_slot_(Twine::Id id);
	void collect_leaves(Twine::Id id, pool<std::string> &out) const;
	// Materialize a flat node (Leaf or Suffix) into its full string.
	std::string flat_string_(Twine::Id id) const;
	// Populate the three indexes from the current nodes_ vector (used by
	// the copy constructor/assignment and by gc()).
	void rebuild_indexes_();
};

// // Owning reference to a Twine slot. Retains on construction (and on copy
// // of a non-empty ref), releases on destruction. Use this in transient
// // container types — FfData, Mem helpers — that need to keep a src_id_
// // alive across destruction of the original AttrObject that minted it,
// // without having to fall back to a flattened path-string stash.
// //
// // Empty (no pool/no id) by default. A non-empty ref always carries a
// // non-null pool and a live id.
// class OwnedTwine
// {
// public:
// 	OwnedTwine() = default;

// 	// Adopt the +1 reference returned by `intern` / `concat` / `intern_suffix`
// 	// / `copy_from`. Use OwnedTwine(pool, id, retain=true) when copying an
// 	// id already held elsewhere (e.g. another AttrObject's src_id_).
// 	OwnedTwine(TwinePool *pool, Twine::Id id, bool retain = true) : pool_(pool), id_(id) {
// 		if (retain && pool_ && id_ != Twine::Null)
// 			pool_->retain(id_);
// 	}

// 	OwnedTwine(const OwnedTwine &other) : pool_(other.pool_), id_(other.id_) {
// 		if (pool_ && id_ != Twine::Null)
// 			pool_->retain(id_);
// 	}

// 	OwnedTwine(OwnedTwine &&other) noexcept : pool_(other.pool_), id_(other.id_) {
// 		other.pool_ = nullptr;
// 		other.id_ = Twine::Null;
// 	}

// 	OwnedTwine &operator=(const OwnedTwine &other) {
// 		if (this == &other)
// 			return *this;
// 		release_();
// 		pool_ = other.pool_;
// 		id_ = other.id_;
// 		if (pool_ && id_ != Twine::Null)
// 			pool_->retain(id_);
// 		return *this;
// 	}

// 	OwnedTwine &operator=(OwnedTwine &&other) noexcept {
// 		if (this == &other)
// 			return *this;
// 		release_();
// 		pool_ = other.pool_;
// 		id_ = other.id_;
// 		other.pool_ = nullptr;
// 		other.id_ = Twine::Null;
// 		return *this;
// 	}

// 	~OwnedTwine() { release_(); }

// 	void reset() {
// 		release_();
// 		pool_ = nullptr;
// 		id_ = Twine::Null;
// 	}

// 	TwinePool *pool() const { return pool_; }
// 	Twine::Id id() const { return id_; }
// 	bool empty() const { return id_ == Twine::Null; }

// private:
// 	TwinePool *pool_ = nullptr;
// 	Twine::Id id_ = Twine::Null;

// 	void release_() {
// 		if (pool_ && id_ != Twine::Null)
// 			pool_->release(id_);
// 	}
// };

struct TwinePoolExtender {
	TwinePool& pool;
	size_t offset;
private:
	size_t resize_for_idx(size_t idx) {
		auto real_idx = offset + idx;
		pool.nodes_.resize(std::max(pool.nodes_.size(), real_idx + 1));
		return real_idx;
	}
	void commit(Twine&& twine, size_t idx) {
		pool.nodes_[idx] = std::move(twine);
		pool.leaf_index_.insert(&pool.nodes_[idx]);
	}
public:
	// TwinePoolExtender(Design* design) : pool(design->twines), offset(design->twines.size()) {}
	void extend_leaf(std::string leaf, size_t idx) {
		auto real_idx = resize_for_idx(idx);
		commit(Twine(leaf), real_idx);
	}
	void extend_concat(std::vector<size_t> children, size_t idx) {
		auto real_idx = resize_for_idx(idx);
		Twine* first = &pool.nodes_.front() + offset;
		std::vector<Twine*> real_children;
		real_children.reserve(children.size());
		for (auto child : children)
			real_children.push_back(first + child);
		commit(Twine(std::move(real_children)), real_idx);
	}
	void extend_suffix(size_t prefix, std::string tail, size_t idx) {
		auto real_idx = resize_for_idx(idx);
		Twine* first = &pool.nodes_.front() + offset;
		Twine* real_prefix = first + prefix;
		commit(Twine(Twine::Suffix(real_prefix, std::move(tail))), real_idx);
	}
	void finish() {
		for (size_t i = offset; i < pool.nodes_.size(); i++)
			if (pool.nodes_[i].is_dead())
				pool.free_list_.push_back(&pool.nodes_[i]);
	}
};

YOSYS_NAMESPACE_END

#endif
