#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/yosys_common.h"

#include <cstdint>
#include <limits>
#include <span>
#include <string>
#include <string_view>
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
// lives on RTLIL::Design (design->src_twines).
struct Twine
{
	using Id = uint32_t;
	static constexpr Id Null = std::numeric_limits<Id>::max();

	// Suffix shares a `parent` prefix with other suffixes and contributes
	// its own `tail` string. The materialized leaf string is
	// flat_string(parent) + tail, i.e. suffixes form trees whose leaves
	// (string variant) are the roots — like a reverse-trie of common
	// prefixes. The parent is itself flat (Leaf or Suffix), never a
	// Concat.
	struct Suffix {
		Id parent;
		std::string tail;
	};

	// Leaf holds the literal path:line.col string. Suffix holds a parent
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

class TwinePool
{
public:
	TwinePool() = default;

	// Intern a leaf string. Returns the same Id for byte-equal inputs. The
	// returned Id carries one reference for the caller — release it when
	// you are done holding it. Empty input returns Twine::Null.
	Twine::Id intern(std::string_view leaf);

	// Intern a Suffix node. The resulting flat string is
	// flat_string(parent) + tail. `parent` must be a flat node (Leaf or
	// Suffix) — pass Twine::Null with a non-empty `tail` to fall back to
	// intern(tail). Suffixes with the same (parent, tail) dedup. The
	// returned Id carries one reference for the caller. Internally the
	// new suffix retains a reference on `parent`; releasing the suffix
	// releases that internal parent ref. Empty `tail` returns `parent`
	// (with +1 ref for the caller).
	Twine::Id intern_suffix(Twine::Id parent, std::string_view tail);

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

	// Refcount control. retain bumps; release decrements and, on reaching
	// zero, marks the slot dead, drops it from the dedup indexes, releases
	// any child refs the slot owned, and pushes the slot id onto the free
	// list for reuse by the next intern/concat. Both no-op on Twine::Null.
	void retain(Twine::Id id);
	void release(Twine::Id id);
	uint32_t refcount(Twine::Id id) const;
	bool is_alive(Twine::Id id) const;

	// Materialize a Twine to the pipe-separated flat string used by the
	// existing src attribute convention. Leaves visit in left-to-right DFS
	// order; duplicate leaves are skipped to match `pool`-style semantics.
	std::string flatten(Twine::Id id, char sep = '|') const;

	// Materialize a flat node (Leaf or Suffix) to its single string. id
	// must be a flat node (not a Concat) and not Twine::Null.
	std::string flat_string(Twine::Id id) const { return flat_string_(id); }

	// Format an interned Id as the canonical src-attribute reference "@N".
	// Twine::Null formats as the empty string.
	static std::string format_ref(Twine::Id id);

	// Parse an "@N" reference back to an Id. Returns Twine::Null if `s` is
	// not exactly "@" followed by one or more decimal digits — so legacy
	// literal src strings (which always contain ':' separators and have no
	// reason to start with '@') are passed through unrecognized.
	static Twine::Id parse_ref(std::string_view s);

	// Lookup. Bounds-checked: out-of-range Id triggers log_assert via op.
	const Twine &operator[](Twine::Id id) const { return nodes_.at(id); }

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
		for (size_t i = 0; i < nodes_.size(); i++) {
			const Twine &n = nodes_[i];
			if (n.is_dead())
				continue;
			fn(static_cast<Twine::Id>(i), n);
		}
	}

private:
	std::vector<Twine> nodes_;
	std::vector<uint32_t> refcount_;
	std::vector<Twine::Id> free_list_;
	dict<std::string, Twine::Id> leaf_index_;
	dict<std::vector<Twine::Id>, Twine::Id> concat_index_;
	dict<std::pair<Twine::Id, std::string>, Twine::Id> suffix_index_;

	Twine::Id alloc_slot_(Twine &&node);
	void destroy_slot_(Twine::Id id);
	void collect_leaves(Twine::Id id, pool<std::string> &out) const;
	// Materialize a flat node (Leaf or Suffix) into its full string.
	std::string flat_string_(Twine::Id id) const;
};

// Owning reference to a Twine slot. Retains on construction (and on copy
// of a non-empty ref), releases on destruction. Use this in transient
// container types — FfData, Mem helpers — that need to keep a src_id_
// alive across destruction of the original AttrObject that minted it,
// without having to fall back to a flattened path-string stash.
//
// Empty (no pool/no id) by default. A non-empty ref always carries a
// non-null pool and a live id.
class OwnedTwine
{
public:
	OwnedTwine() = default;

	// Adopt the +1 reference returned by `intern` / `concat` / `intern_suffix`
	// / `copy_from`. Use OwnedTwine(pool, id, retain=true) when copying an
	// id already held elsewhere (e.g. another AttrObject's src_id_).
	OwnedTwine(TwinePool *pool, Twine::Id id, bool retain = true) : pool_(pool), id_(id) {
		if (retain && pool_ && id_ != Twine::Null)
			pool_->retain(id_);
	}

	OwnedTwine(const OwnedTwine &other) : pool_(other.pool_), id_(other.id_) {
		if (pool_ && id_ != Twine::Null)
			pool_->retain(id_);
	}

	OwnedTwine(OwnedTwine &&other) noexcept : pool_(other.pool_), id_(other.id_) {
		other.pool_ = nullptr;
		other.id_ = Twine::Null;
	}

	OwnedTwine &operator=(const OwnedTwine &other) {
		if (this == &other)
			return *this;
		release_();
		pool_ = other.pool_;
		id_ = other.id_;
		if (pool_ && id_ != Twine::Null)
			pool_->retain(id_);
		return *this;
	}

	OwnedTwine &operator=(OwnedTwine &&other) noexcept {
		if (this == &other)
			return *this;
		release_();
		pool_ = other.pool_;
		id_ = other.id_;
		other.pool_ = nullptr;
		other.id_ = Twine::Null;
		return *this;
	}

	~OwnedTwine() { release_(); }

	void reset() {
		release_();
		pool_ = nullptr;
		id_ = Twine::Null;
	}

	TwinePool *pool() const { return pool_; }
	Twine::Id id() const { return id_; }
	bool empty() const { return id_ == Twine::Null; }

private:
	TwinePool *pool_ = nullptr;
	Twine::Id id_ = Twine::Null;

	void release_() {
		if (pool_ && id_ != Twine::Null)
			pool_->release(id_);
	}
};

YOSYS_NAMESPACE_END

#endif
