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
	Ref find_members(std::span<const IdString> members) const;
	Ref copy_from(const Derived &other, Ref ref);

	void root_members(const Marks &live, pool<IdString> &live_twines) const;

	void dump(Ref ref, std::ostream &os = std::cout) const;
	void dump(std::ostream &os = std::cout) const;

protected:
	static std::vector<IdString> canonical(std::span<const IdString> members);
	Ref intern(std::vector<IdString> members);
};

struct NameSetRef {
	static const NameSetRef Null;

	constexpr NameSetRef() : value(NULL_VAL) {}

	constexpr bool operator==(const NameSetRef &rhs) const { return value == rhs.value; }

	constexpr NameSetRef unstamped() const {
		NameSetRef ref = *this;
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
		ref.serial = 0;
#endif
		return ref;
	}

private:
	template<typename, typename, typename> friend struct HashConsPool;
	template<typename, typename, typename> friend struct TwineBackedPool;
	template<typename, typename> friend struct TwineSetPool;
	friend struct MetaPool;

	explicit constexpr NameSetRef(size_t val) : value((uint32_t) val) {}
	constexpr size_t raw() const { return value; }
	constexpr NameSetRef untag() const { return *this; }

	static constexpr uint32_t NULL_VAL = ~uint32_t{0};
	uint32_t value;
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	uint32_t serial = 0;
#endif
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
