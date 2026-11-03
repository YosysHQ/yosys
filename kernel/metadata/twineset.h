#ifndef YOSYS_TWINESET_H
#define YOSYS_TWINESET_H

#include "kernel/metadata/twinebacked.h"

#include <span>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct TwineSet {
	TwineSet() = default;
	explicit TwineSet(std::vector<IdString> members) : members_(std::move(members)) {}

	bool is_dead() const { return members_.empty(); }
	const std::vector<IdString> &members() const { return members_; }

	bool operator==(const TwineSet &other) const { return members_ == other.members_; }

private:
	std::vector<IdString> members_;
};

template<typename Derived, typename Ref>
struct TwineSetPool : TwineBackedPool<Derived, TwineSet, Ref> {
	using Base = TwineBackedPool<Derived, TwineSet, Ref>;
	using Base::Base;
	using typename Base::Marks;

	static uint64_t hash_node(const TwineSet &n);

	Ref adopt(std::span<const IdString> members);
	Ref merge(std::span<const Ref> refs);
	Ref merge(Ref a, Ref b);
	Ref with_member(Ref ref, IdString member);
	Ref without_member(Ref ref, IdString member);
	Ref place(size_t idx, std::span<const IdString> members);
	using HashConsPool<Derived, TwineSet, Ref>::finish_placement;
	Ref find(std::span<const IdString> members) const;
	Ref copy_from(const Derived &other, Ref ref);
	std::string serial(Ref ref) const;

	void root_members(const Marks &live, pool<IdString> &live_twines) const;

	void dump(Ref ref, std::ostream &os = std::cout) const;
	void dump(std::ostream &os = std::cout) const;

protected:
	static std::vector<IdString> canonical(std::span<const IdString> members);
	Ref intern(std::vector<IdString> members);
};

struct NameSetRef : PoolRef<NameSetRef> {
	static const NameSetRef Null;

	constexpr NameSetRef() = default;

	constexpr bool operator==(const NameSetRef &rhs) const { return value == rhs.value; }

private:
	template<typename> friend struct PoolRef;
	template<typename, typename, typename> friend struct HashConsPool;
	template<typename, typename, typename> friend struct TwineBackedPool;
	template<typename, typename> friend struct TwineSetPool;
	friend struct MetaPool;

	using PoolRef::PoolRef;
	constexpr NameSetRef untag() const { return *this; }
};

inline constexpr NameSetRef NameSetRef::Null{};

namespace hashlib {
template<> struct hash_ops<NameSetRef> {
	static Hasher hash_into(const NameSetRef &, Hasher) = delete;
};
}

struct NameSetPool : TwineSetPool<NameSetPool, NameSetRef> {
	using TwineSetPool::TwineSetPool;
};

YOSYS_NAMESPACE_END

#endif
