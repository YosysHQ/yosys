#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/hashcons.h"
#include "kernel/yosys_common.h"

#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstring>
#include <deque>
#include <limits>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct TwineSpec;
struct TwinePool;
struct IdString;

/**
 * A twine is a data structure designed to deduplicate prefixes.
 * The key idea is that a twine is a suffix node or a leaf node.
 * A leaf node holds a string,
 * while a suffix node appends a string to a twine.
 *
 * Twines are used here to implement IdString, the Yosys interned
 * string type. They're extended to the needs of Yosys, specifically
 * with efficient static NEW_ID prefixes,
 * and IdString holding a special bit marking the publicity of a name.
 * When public, a backslash is prepended when printing an IdString.
 *
 * An IdString references a TwineNode in a per-Design TwinePool
 * by indexing into it. It is constructed by interning a TwineSpec
 * into a TwinePool.
 *
 * A general IdString can't be constructed, converted to a string, or printed
 * without a pointer to the TwinePool.
 * Compile-time allocated indices defined in kernel/constids.inc
 * live in a global read-only pool, so they're an exception to that.
 *
 * Two IdStrings that resolve to the same string won't generally compare
 * equal with operator== so that comparisons are cheap,
 * but alternate mechanisms are provided for cases
 * where that is absolutely necessary but it should be avoided for performance,
 * like DeepTwine and TwineSearch.
 * Twines are deduplicated within a TwinePool in a "shallow" way, similar to FRAIGing.
 * Lookup from a string to IdString is expensive and provided by TwineSearch.
 *
 * TwinePool is backed by an std::deque and a free list
 * and provides stable indices outside of garbage collection.
 * "Content" refers to the untagged backing.
 */

struct NullIdString {
	constexpr operator IdString() const;
	constexpr bool operator==(IdString ref) const;
};

struct IdString {
private:
#ifdef YOSYS_ENABLE_TWINE_PROVENANCE
	using bits_t = uint64_t;
#else
	using bits_t = uint32_t;
#endif
	bits_t value;

	static constexpr int TWINE_WIDTH = std::numeric_limits<bits_t>::digits;
	static constexpr int TWINE_PUBLIC_SHIFT = TWINE_WIDTH - 1;
	static constexpr bits_t TWINE_PUBLIC_BIT = bits_t{1} << TWINE_PUBLIC_SHIFT;
	static constexpr bits_t TWINE_NULL_VAL = ~bits_t{0};
	static constexpr int TWINE_SERIAL_SHIFT = TWINE_WIDTH == 64 ? 32 : TWINE_PUBLIC_SHIFT;
	static constexpr bits_t TWINE_INDEX_MASK = (bits_t{1} << TWINE_SERIAL_SHIFT) - 1;
	static constexpr bits_t TWINE_SERIAL_MASK = bits_t(~(TWINE_INDEX_MASK | TWINE_PUBLIC_BIT));

public:
	static constexpr NullIdString Null{};

	static constexpr size_t MAX_INDEX = TWINE_INDEX_MASK;
	static constexpr size_t MAX_SERIAL = TWINE_SERIAL_MASK >> TWINE_SERIAL_SHIFT;

	constexpr size_t raw() const {
		return value == TWINE_NULL_VAL ? value : (value & ~TWINE_SERIAL_MASK);
	}

	// raw() with the pool serial kept
	constexpr size_t bits() const { return value; }

	constexpr size_t order_key() const { return std::rotl((bits_t) eq_key(), 1); }

	constexpr size_t serial() const {
		return value == TWINE_NULL_VAL ? 0 : ((value & TWINE_SERIAL_MASK) >> TWINE_SERIAL_SHIFT);
	}

	constexpr IdString stamped(size_t pool_serial) const {
		return value == TWINE_NULL_VAL ? *this
			: IdString((value & ~TWINE_SERIAL_MASK)
					| (bits_t(pool_serial << TWINE_SERIAL_SHIFT) & TWINE_SERIAL_MASK));
	}

	constexpr IdString() : value(TWINE_NULL_VAL) {}
	explicit constexpr IdString(size_t val) : value((bits_t) val) {}

	constexpr size_t eq_key() const { return value & ~TWINE_SERIAL_MASK; }

	constexpr bool operator==(const IdString &rhs) const { return eq_key() == rhs.eq_key(); }
	constexpr bool operator!=(const IdString &rhs) const { return eq_key() != rhs.eq_key(); }
	constexpr std::strong_ordering operator<=>(const IdString &rhs) const {
		return order_key() <=> rhs.order_key();
	}

	template <typename... Args>
	constexpr bool in(const Args&... args) const {
		return ((*this == args) || ...);
	}

	// Instead of for example std::set<Cell*>
	// use std::set<Cell*, IdString::compare_ptr_by_name<Cell>> if the order of cells in the
	// set has an influence on the algorithm.
	template<typename T> struct compare_ptr_by_name {
		bool operator()(const T *a, const T *b) const {
			return (a == nullptr || b == nullptr) ? (a < b) : (a->name < b->name);
		}
	};

	// A ref is "empty" when it names nothing at all.
	constexpr bool empty() const { return value == TWINE_NULL_VAL; }
	constexpr bool isPublic() const { return value != TWINE_NULL_VAL && (value & TWINE_PUBLIC_BIT); }

	constexpr IdString untag() const {
		return value == TWINE_NULL_VAL ? *this : IdString(value & ~TWINE_PUBLIC_BIT);
	}
	constexpr IdString tag(bool pub) const {
		return value == TWINE_NULL_VAL ? *this : IdString(pub ? (value | TWINE_PUBLIC_BIT) : (value & ~TWINE_PUBLIC_BIT));
	}

	Hasher hash_into(Hasher h) const;

	std::string handle_token() const;
	static size_t handle_token_prefix(std::string_view token, bool &is_public);
};

constexpr NullIdString::operator IdString() const { return IdString(); }
constexpr bool NullIdString::operator==(IdString ref) const { return ref.empty(); }

namespace hashlib {
	template<>
	struct hash_ops<IdString> {
		static inline bool cmp(IdString a, IdString b) { return a == b; }
		[[nodiscard]] static inline Hasher hash(IdString id) {
			Hasher h;
			h.force((Hasher::hash_t) id.bits());
			return h;
		}
		[[nodiscard]] static inline Hasher hash_into(IdString id, Hasher h) {
			h.hash64(id.eq_key());
			return h;
		}
	};
}


enum : short {
	// STATIC_TWINE_BEGIN = 0,
#define X(N) IDX_##N,
#include "kernel/constids.inc"
#undef X
	STATIC_TWINE_END
};

struct ID {
// Static ids are name handles: non-'$' constids were '\'-escaped publics,
// so their handles carry the publicity bit baked in at compile time.
#define X(N) static constexpr IdString N = IdString(IDX_##N).tag((#N)[0] != '$');
#include "kernel/constids.inc"
#undef X

	static constexpr const char* static_names[] = {
#define X(N) #N,
#include "kernel/constids.inc"
#undef X
	};

	static constexpr IdString lookup(std::string_view name)
	{
		int low = 0, high = STATIC_TWINE_END;
		while (high - low >= 2) {
			int mid = (low + high) / 2;
			if (name < static_names[mid])
				high = mid;
			else
				low = mid;
		}

		if (name != static_names[low])
			throw "unknown twine id";

		return IdString(low).tag(name[0] != '$');
	}

	static constexpr bool is_static(IdString ref) {
		return ref.untag().raw() < STATIC_TWINE_END;
	}

	// Static IdString can be constructed without a design pointer
	static std::string str(IdString ref);
	static std::string unescaped_str(IdString ref);
};

template<size_t Raw> inline constexpr IdString constid = IdString(Raw);

#define ID(id) (YOSYS_NAMESPACE_PREFIX constid<YOSYS_NAMESPACE_PREFIX ID::lookup(#id).raw()>)

// TwineSpec is the object that lives in the TwinePool,
// while IdString points to a TwineSpec and carries publicity information
struct TwineSpec {
	// deduplicates shared prefixes
	struct Suffix {
		IdString prefix;
		std::string tail;
		auto operator<=>(const Suffix&) const = default;
	};

	// transient suffix constructed with NEW_ID and NEW_ID_SUFFIX
	// turned into a regular Suffix when added to a TwinePool
	struct AutoSuffix {
		const std::string *prefix;
		std::string tail;
		auto operator<=>(const AutoSuffix&) const = default;
	};

	// "leaf", regular deduplicated string
	struct Leaf {
		std::string s;
		auto operator<=>(const Leaf&) const = default;
	};

	std::variant<Leaf, Suffix, AutoSuffix> data;

	TwineSpec(Leaf v);
	TwineSpec(Suffix v);
	TwineSpec(AutoSuffix v);

	bool holds_leaf() const;
	bool holds_suffix() const;
	// Only for the pool-free variants, Leaf and AutoSuffix
	std::string content_str() const;
};

struct SmallString {
	static constexpr uint32_t INLINE_CAP = 8;
	static constexpr size_t MAX_LEN = std::numeric_limits<uint32_t>::max();

	SmallString() = default;
	explicit SmallString(std::string_view content);
	SmallString(const SmallString &other);
	SmallString(SmallString &&other) noexcept;
	SmallString &operator=(const SmallString &other);
	SmallString &operator=(SmallString &&other) noexcept;
	~SmallString();

	std::string_view view() const { return {len_ <= INLINE_CAP ? inl_ : ptr_, len_}; }

private:
	void store(std::string_view content);
	void release();

	union {
		char inl_[INLINE_CAP];
		char *ptr_;
	};
	uint32_t len_ = 0;
};

// TwineNode is the in-memory version of TwineSpec
struct TwineNode {
	static constexpr uint32_t NO_PREFIX = ~uint32_t{0};
	static constexpr uint32_t DEAD = NO_PREFIX - 1;

	struct Key {
		uint32_t prefix;
		std::string_view text;
	};

	TwineNode() = default;
	explicit TwineNode(std::string_view content) : text_(content), prefix_(NO_PREFIX) {}
	TwineNode(uint32_t prefix, std::string_view tail) : text_(tail), prefix_(prefix) {}
	TwineNode(const TwineNode &other) = default;
	TwineNode(TwineNode &&other) noexcept;
	TwineNode &operator=(const TwineNode &other) = default;
	TwineNode &operator=(TwineNode &&other) noexcept;
	~TwineNode() = default;

	enum class Kind { Dead, Leaf, Suffix };

	constexpr bool is_dead() const { return prefix_ == DEAD; }
	constexpr bool is_leaf() const { return prefix_ == NO_PREFIX; }
	constexpr bool is_suffix() const { return prefix_ < DEAD; }

	constexpr Kind kind() const {
		return prefix_ == DEAD ? Kind::Dead
			: prefix_ == NO_PREFIX ? Kind::Leaf
			: Kind::Suffix;
	}

	std::string_view text() const { return text_.view(); }
	IdString prefix() const { return IdString(prefix_); }
	Key key() const { return {prefix_, text()}; }

	bool operator==(const TwineNode &other) const
		{ return prefix_ == other.prefix_ && text() == other.text(); }
	bool operator==(const Key &other) const
		{ return prefix_ == other.prefix && text() == other.text; }

private:
	YS_NO_UNIQUE_ADDRESS SmallString text_;
	uint32_t prefix_ = DEAD;
};

static_assert(sizeof(TwineNode) == 16);

struct StaticTwines {
	static constexpr size_t count = STATIC_TWINE_END;

	static void init();
	static const TwineNode &node(size_t idx);
	static bool ready();

private:
	static std::vector<TwineNode> nodes_;
};

extern int64_t twine_gc_ns;
extern int twine_gc_count;

std::pair<std::string, bool> twine_unescape(std::string s);

struct TwinePool : HashConsPool<TwinePool, TwineNode, IdString> {
	static constexpr size_t STATIC_COUNT = StaticTwines::count;

	TwinePool();
	TwinePool(const TwinePool& other);
	TwinePool(TwinePool&& other);
	TwinePool& operator=(const TwinePool& other);
	TwinePool& operator=(TwinePool&& other);

	size_t serial() const;
	bool owns(IdString ref) const;
	IdString stamp(IdString ref) const;
	void check_owned(IdString ref) const;
	const TwineNode& operator[](IdString ref) const;

	static const TwineNode& static_node(size_t idx);
	// static IdString untag(IdString ref);

	static void check_ready();
	static void canonicalize(TwineNode& t);
	static size_t hash_node(const TwineNode& t);
	static size_t hash_key(const TwineNode::Key& k);

	template<typename F>
	static void for_each_child(const TwineNode& t, F&& f) {
		if (t.is_suffix())
			f(t.prefix());
	}

	template<typename Roots>
	size_t gc(Roots& roots) {
		for (auto &it : auto_prefixes)
			roots.insert(it.second);
		return HashConsPool::gc(roots);
	}

	void dump(IdString ref, std::ostream& os = std::cout) const;
	void print(IdString ref, std::ostream& os = std::cout) const;
	void append_str(IdString ref, std::string& out) const;

	// Publicity bit provides escaping
	std::string str(IdString ref) const;
	// Publicity bit ignored
	std::string unescaped_str(IdString ref) const;

	size_t str_size(IdString ref) const;
	bool begins_with(IdString ref, std::string_view prefix) const;
	// Publicity bit provides escaping, as in str()
	bool name_equal(IdString ref, std::string_view name) const;
	bool content_equal(IdString a, IdString b) const;
	int compare_by_name(IdString a, IdString b) const;
	IdString prefix_of(IdString ref) const;

	// Only finds leaves. For compatibility only
	IdString find(const std::string &name) const;
	IdString find(TwineSpec t) const;
	// Doesn't infer publicity
	IdString add(TwineSpec t);
	IdString add(IdString prefix, std::string_view tail);
	IdString auto_prefix(const std::string *prefix);
	// Infers publicity from first character
	IdString add(std::string s);
	IdString copy_from(const TwinePool& src, IdString ref);
	// Non-mutating counterpart of copy_from
	IdString find_from(const TwinePool& src, IdString ref) const;
	// Opaque handle for files that never leave one run of yosys.
	// Only valid until garbage collection reuses the slot.
	std::string ref_token(IdString ref) const;
	// Null unless the token names a live twine stamped by this pool
	IdString ref_from_token(std::string_view token) const;
	void dump(std::ostream& os = std::cout) const;
	using HashConsPool::gc;

private:
	IdString add_inner(TwineNode t);
	IdString intern(uint32_t prefix, std::string_view text);
	IdString find_content(uint32_t prefix, std::string_view text) const;
	static size_t next_serial();
	dict<const std::string *, IdString> auto_prefixes;
	size_t serial_;
};

/**
 * DeepTwine
 * Compare and hash IdString a and b equal iff their .str() are equal
 * without really constructing those strings.
 */

struct DeepTwineHash {
	// Transparent hashing allows us to compare diverse types, so that
	// we don't have to get a temporary string out of an IdString
	// just to hash it
	using is_transparent = void;
	const TwinePool* pool = nullptr;

	// Hashes 8 characters as a time
	struct Stream {
		Hasher h;
		uint64_t buf = 0;
		int fill = 0;
		void push(std::string_view sv);
		size_t finish();
	};
	void combine(Stream& s, IdString t) const;
	size_t operator()(std::string_view sv) const;
	size_t operator()(IdString t) const;
};

// see DeepTwineHash explanation above
struct DeepTwineEq {
	using is_transparent = void;
	const TwinePool* pool = nullptr;
	bool consume(IdString t, std::string_view& sv) const noexcept;
	bool operator()(IdString t, std::string_view sv) const noexcept;
	bool operator()(std::string_view sv, IdString t) const noexcept;
	bool operator()(IdString a, IdString b) const;
};

// EXPENSIVE ephemeral search for string_view -> IdString
// No automatic tracking abilities,
// so you won't find things you created after you created the search.
// Best used only for cases where you're searching for a lot of strings
// with a single TwineSearch
struct TwineSearch {
	const TwinePool* pool;
	std::unordered_set<IdString, DeepTwineHash, DeepTwineEq> index;
	TwineSearch(const TwinePool* pool);
	void insert(IdString ref);
	// Infers publicity from first character
	IdString find(std::string_view sv) const;
};

YOSYS_NAMESPACE_END

#endif
