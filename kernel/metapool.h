#ifndef YOSYS_METAPOOL_H
#define YOSYS_METAPOOL_H

#include "kernel/hashcons.h"
#include "kernel/twine.h"

#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct MetaRef {
	static const MetaRef Null;

	constexpr MetaRef() : value(NULL_VAL) {}

	constexpr bool operator==(const MetaRef &rhs) const { return value == rhs.value; }

	constexpr bool has_hdlname() const { return value != NULL_VAL && (value & HDLNAME_BIT); }
	constexpr bool has_scopename() const { return value != NULL_VAL && (value & SCOPENAME_BIT); }

private:
	template<typename, typename, typename> friend struct HashConsPool;
	friend struct MetaPool;

	explicit constexpr MetaRef(size_t val) : value((uint32_t) val) {}
	constexpr size_t raw() const { return value; }
	constexpr MetaRef untag() const { return value == NULL_VAL ? *this : MetaRef(value & ~TAG_MASK); }

	static constexpr uint32_t NULL_VAL = ~uint32_t{0};
	static constexpr uint32_t HDLNAME_BIT = uint32_t{1} << 31;
	static constexpr uint32_t SCOPENAME_BIT = uint32_t{1} << 30;
	static constexpr uint32_t TAG_MASK = HDLNAME_BIT | SCOPENAME_BIT;
	uint32_t value;
};

inline constexpr MetaRef MetaRef::Null{};

namespace hashlib {
template<> struct hash_ops<MetaRef> {
	static Hasher hash_into(const MetaRef &, Hasher) = delete;
};
}

// scope and name form the identity: scope is a path rooted at the pool's
// root twine, name is a suffix of scope holding only the last name.
// names and scopes hold what was absorbed from other objects.
struct MetaBlock {
	IdString scope;
	IdString name;
	std::vector<IdString> names;
	std::vector<IdString> scopes;

	bool is_dead() const { return scope.empty() && names.empty() && scopes.empty(); }

	bool operator==(const MetaBlock &other) const {
		return scope == other.scope && name == other.name && names == other.names && scopes == other.scopes;
	}
};

struct MetaPool : HashConsPool<MetaPool, MetaBlock, MetaRef> {
	static constexpr size_t STATIC_COUNT = 0;

	explicit MetaPool(TwinePool &twines) : twines(twines) {}

	MetaPool(const MetaPool &) = delete;
	MetaPool(MetaPool &&) = delete;
	MetaPool &operator=(const MetaPool &) = delete;
	MetaPool &operator=(MetaPool &&) = delete;

	const MetaBlock &operator[](MetaRef ref) const { return HashConsPool::operator[](ref); }

	void clone_from(const MetaPool &other);

	static uint64_t hash_node(const MetaBlock &n);

	template<typename F>
	static void for_each_child(const MetaBlock&, F&&) {}

	using HashConsPool::size;
	void clear();

	std::string hdlname(MetaRef ref) const;
	std::string scopename(MetaRef ref) const;
	MetaRef with_hdlname(MetaRef ref, std::string_view path);
	MetaRef with_scopename(MetaRef ref, std::string_view path);
	// keeps the scope of an object's hdlname as its scopename
	MetaRef without_name(MetaRef ref);

	MetaRef transfer(MetaRef target, MetaRef source);
	MetaRef absorb(MetaRef target, MetaRef source);
	MetaRef copy_from(const MetaPool &other, MetaRef ref);

	void root_members(const std::vector<MetaRef> &live_metas, pool<IdString> &live_twines) const;
	size_t gc(const std::vector<MetaRef> &live_metas);

	void dump(MetaRef ref, std::ostream &os = std::cout) const;

private:
	TwinePool &twines;

	IdString root();
	IdString extend(IdString scope, std::string_view name);
	MetaRef intern(MetaBlock block);
};

YOSYS_NAMESPACE_END

#endif
