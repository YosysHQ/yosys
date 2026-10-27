#ifndef YOSYS_SRCPOOL_H
#define YOSYS_SRCPOOL_H

#include "kernel/metadata/twinebacked.h"

#include <span>
#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct SrcRef {
	static const SrcRef Null;

	constexpr SrcRef() : value(NULL_VAL) {}

	constexpr bool operator==(const SrcRef &rhs) const { return value == rhs.value; }

private:
	template<typename, typename, typename> friend struct HashConsPool;
	template<typename, typename, typename> friend struct TwineBackedPool;
	friend struct SrcPool;

	explicit constexpr SrcRef(size_t val) : value((uint32_t) val) {}
	constexpr size_t raw() const { return value; }
	constexpr SrcRef untag() const { return *this; }

	static constexpr uint32_t NULL_VAL = ~uint32_t{0};
	uint32_t value;
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	uint32_t serial = 0;
#endif
};

inline constexpr SrcRef SrcRef::Null{};

namespace hashlib {
template<> struct hash_ops<SrcRef> {
	static Hasher hash_into(const SrcRef &, Hasher) = delete;
};
}

struct SrcSet {
	SrcSet() = default;
	explicit SrcSet(std::vector<IdString> members) : members_(std::move(members)) {}

	bool is_dead() const { return members_.empty(); }
	const std::vector<IdString> &members() const { return members_; }

	bool operator==(const SrcSet &other) const { return members_ == other.members_; }

private:
	std::vector<IdString> members_;
};

struct SrcPool : TwineBackedPool<SrcPool, SrcSet, SrcRef> {
	using TwineBackedPool::TwineBackedPool;

	static uint64_t hash_node(const SrcSet &n);

	SrcRef add(std::string_view text);
	SrcRef add(const std::string &file, const std::string &tail);
	SrcRef merge(std::span<const SrcRef> refs);
	SrcRef merge(SrcRef a, SrcRef b);
	SrcRef adopt(std::span<const IdString> members);
	SrcRef place(size_t idx, std::span<const IdString> members);
	using HashConsPool::finish_placement;
	SrcRef find_members(std::span<const IdString> members) const;
	SrcRef copy_from(const SrcPool &other, SrcRef ref);

	std::string str(SrcRef ref) const;
	std::string serial(SrcRef ref) const;
	pool<std::string> leaves(SrcRef ref) const;

	void root_members(const Marks &live_srcs, pool<IdString> &live_twines) const;

	void dump(SrcRef ref, std::ostream &os = std::cout) const;
	void dump(std::ostream &os = std::cout) const;

private:
	IdString add_location(std::string_view location);
	static void canonicalize_members(std::vector<IdString> &members);
	SrcRef intern(std::vector<IdString> members);
};

YOSYS_NAMESPACE_END

#endif
