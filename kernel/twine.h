#ifndef YOSYS_TWINE_H
#define YOSYS_TWINE_H

#include "kernel/hashcons.h"
#include "kernel/yosys_common.h"

#include <algorithm>
#include <cstring>
#include <deque>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>
#include <variant>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct Twine;
struct TwinePool;
struct IdString;

// An IdString now references a Twine in a per-Design TwinePool.
// Twines are designed to deduplicate prefixes if appropriately constructed.
// Statically, compile-time allocated indices defined in kernel/constids.inc
// are handled with a global read-only pool.
// A general IdString can't be constructed, converted to a string, or printed
// without a pointer to the pool.
// Two IdStrings that resolve to the same string won't generally compare
// equal with operator== but alternate mechanisms are provided for cases
// where that is absolutely necessary but it should be avoided for performance,
// see DeepTwine and TwineSearch.
// Twines are deduplicated within a TwinePool in a "shallow" way, similar to FRAIGing.
// Lookup from a string to IdString is expensive and provided by TwineSearch.
// Instead of backslash escaping, identifier "publicity" is implemented
// with a publicity bit on the IdString reference integer.
// TwinePool is backed by an std::deque and a free list
// and provides stable indices outside of garbage collection.
// "Content" refers to the untagged backing.

struct NullIdString {
	constexpr operator IdString() const;
	constexpr bool operator==(IdString ref) const;
};

struct IdString {
private:
	size_t value;

	static constexpr size_t TWINE_PUBLIC_BIT = 1ULL << 63;
	static constexpr size_t TWINE_NULL_VAL = ~size_t{0};

public:
	static constexpr NullIdString Null{};

	constexpr size_t raw() const { return value; }

	constexpr IdString() : value(TWINE_NULL_VAL) {}
	explicit constexpr IdString(size_t val) : value(val) {}

	constexpr bool operator==(const IdString&) const = default;
	constexpr std::strong_ordering operator<=>(const IdString &rhs) const {
		if (auto cmp = (value & ~TWINE_PUBLIC_BIT) <=> (rhs.value & ~TWINE_PUBLIC_BIT); cmp != 0)
			return cmp;
		return (value & TWINE_PUBLIC_BIT) <=> (rhs.value & TWINE_PUBLIC_BIT);
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
};

constexpr NullIdString::operator IdString() const { return IdString(); }
constexpr bool NullIdString::operator==(IdString ref) const { return ref.empty(); }


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

// Twine is the object that lives in the TwinePool,
// while IdString points to a Twine and carries publicity information
struct Twine {
	// deduplicates shared prefixes
	struct Suffix {
		IdString prefix;
		std::string tail;
		auto operator<=>(const Suffix&) const = default;
	};

	// transient suffix constructed with NEW_ID and NEW_ID_SUFFIX
	// turned into a regular Suffix when added to a TwinePool
	struct AutoSuffix {
		std::string_view prefix;
		std::string tail;
		auto operator<=>(const AutoSuffix&) const = default;
	};

	// "leaf", regular deduplicated string
	struct Leaf {
		std::string s;
		auto operator<=>(const Leaf&) const = default;
	};

	std::variant<Leaf, Suffix, AutoSuffix> data;

	Twine(Leaf v) : data(std::move(v)) {}
	Twine(Suffix v) : data(std::move(v)) {}
	Twine(AutoSuffix v) : data(std::move(v)) {}

	bool is_leaf() const;
	bool is_suffix() const;
	// Only for the pool-free variants, Leaf and AutoSuffix
	std::string content_str() const;
};

struct TwineNode {
	std::variant<std::monostate, Twine::Leaf, Twine::Suffix> data;

	TwineNode() = default;
	TwineNode(Twine::Leaf v) : data(std::move(v)) {}
	TwineNode(Twine::Suffix v) : data(std::move(v)) {}

	bool is_dead() const;
	bool is_leaf() const;
	bool is_suffix() const;
	const std::string &leaf() const;
	const Twine::Suffix &suffix() const;
};

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

	static const TwineNode& static_node(size_t idx);
	// static IdString untag(IdString ref);

	static void check_ready();
	static void canonicalize(TwineNode& t);
	static size_t hash_node(const TwineNode& t);

	template<typename F>
	static void for_each_child(const TwineNode& t, F&& f) {
		if (t.is_suffix())
			f(t.suffix().prefix);
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

	// Only finds leaves. For compatibility only
	IdString find(const std::string &name) const;
	IdString find(Twine t) const;
	// Doesn't infer publicity
	IdString add(Twine t);
	// Infers publicity from first character
	IdString add(std::string s);
	IdString copy_from(const TwinePool& src, IdString ref);
	// Non-mutating counterpart of copy_from
	IdString find_from(const TwinePool& src, IdString ref) const;
	void dump(std::ostream& os = std::cout) const;
	using HashConsPool::gc;

private:
	static bool inherits_publicity(const Twine &t);
	static TwineNode to_node(Twine t);
	using HashConsPool::add_inner;
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
