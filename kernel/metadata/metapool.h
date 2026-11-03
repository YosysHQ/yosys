#ifndef YOSYS_METAPOOL_H
#define YOSYS_METAPOOL_H

#include "kernel/metadata/twineset.h"

#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct MetaRef : PoolRef<MetaRef> {
	static const MetaRef Null;

	constexpr MetaRef() = default;

	constexpr bool operator==(const MetaRef &rhs) const { return value == rhs.value; }

	constexpr bool has_hdlname() const { return value != NULL_VAL && (value & HDLNAME_BIT); }
	constexpr bool has_scopename() const { return value != NULL_VAL && (value & SCOPENAME_BIT); }

private:
	template<typename> friend struct PoolRef;
	template<typename, typename, typename> friend struct HashConsPool;
	template<typename, typename, typename> friend struct TwineBackedPool;
	friend struct MetaPool;

	using PoolRef::PoolRef;
	constexpr MetaRef untag() const { return value == NULL_VAL ? *this : MetaRef(value & ~TAG_MASK); }

	static constexpr uint32_t HDLNAME_BIT = uint32_t{1} << 31;
	static constexpr uint32_t SCOPENAME_BIT = uint32_t{1} << 30;
	static constexpr uint32_t TAG_MASK = HDLNAME_BIT | SCOPENAME_BIT;
};

inline constexpr MetaRef MetaRef::Null{};

namespace hashlib {
template<> struct hash_ops<MetaRef> {
	static Hasher hash_into(const MetaRef &, Hasher) = delete;
};
}

struct MetaBlock {
	IdString scope;
	IdString hdlname;
	NameSetRef absorbed_hdlnames;
	NameSetRef absorbed_scopes;

	bool is_dead() const {
		return scope.empty() && absorbed_hdlnames == NameSetRef::Null && absorbed_scopes == NameSetRef::Null;
	}

	bool operator==(const MetaBlock &other) const {
		return scope == other.scope && hdlname == other.hdlname
			&& absorbed_hdlnames == other.absorbed_hdlnames && absorbed_scopes == other.absorbed_scopes;
	}
};

struct MetaPool : TwineBackedPool<MetaPool, MetaBlock, MetaRef> {
	explicit MetaPool(TwinePool &twines) : TwineBackedPool(twines), sets_(twines) {}

	static uint64_t hash_node(const MetaBlock &n);

	NameSetPool &sets() { return sets_; }
	const NameSetPool &sets() const { return sets_; }

	void clone_from(const MetaPool &other);
	void clear();
	size_t gc(const Marks &live_metas);

	std::string hdlname(MetaRef ref) const;
	std::string scopename(MetaRef ref) const;
	MetaRef with_hdlname(MetaRef ref, std::string_view path);
	MetaRef with_scopename(MetaRef ref, std::string_view path);
	MetaRef without_hdlname(MetaRef ref);

	MetaRef transfer(MetaRef target, MetaRef source);
	MetaRef absorb(MetaRef target, MetaRef source);
	MetaRef copy_from(const MetaPool &other, MetaRef ref);
	MetaRef adopt(MetaBlock block);
	MetaRef place(size_t idx, MetaBlock block);
	using HashConsPool<MetaPool, MetaBlock, MetaRef>::finish_placement;
	MetaRef find(MetaBlock block) const;
	std::string serial(MetaRef ref) const;

	void root_members(const Marks &live_metas, pool<IdString> &live_twines) const;

	void dump(MetaRef ref, std::ostream &os = std::cout) const;

private:
	NameSetPool sets_;

	NameSetPool::Marks absorbed_sets(const Marks &live_metas) const;
	void absorb_identity(MetaBlock &into, const MetaBlock &from);
	void absorb_sets(MetaBlock &into, const MetaBlock &from);
	IdString root();
	IdString extend(IdString root, IdString path, std::string_view name);
	IdString add_path(IdString root, std::span<const std::string> names);
	MetaRef intern(MetaBlock block);
	static MetaRef tagged(MetaRef ref, const MetaBlock &block);
};

YOSYS_NAMESPACE_END

#endif
