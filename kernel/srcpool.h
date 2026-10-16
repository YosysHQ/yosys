#ifndef YOSYS_SRCPOOL_H
#define YOSYS_SRCPOOL_H

#include "kernel/hashcons.h"
#include "kernel/twine.h"

#include <span>
#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct SrcRef;

struct NullSrcRef {
	constexpr operator SrcRef() const;
	constexpr bool operator==(SrcRef ref) const;
};

struct SrcRef {
	static constexpr NullSrcRef Null{};

	constexpr SrcRef() : value(NULL_VAL) {}
	explicit constexpr SrcRef(size_t val) : value((uint32_t) val) {}

	constexpr bool operator==(const SrcRef&) const = default;
	constexpr auto operator<=>(const SrcRef&) const = default;

	constexpr size_t raw() const { return value; }
	constexpr SrcRef untag() const { return *this; }

	Hasher hash_into(Hasher h) const { h.hash32(value); return h; }

private:
	static constexpr uint32_t NULL_VAL = ~uint32_t{0};
	uint32_t value;
};

constexpr NullSrcRef::operator SrcRef() const { return SrcRef(); }
constexpr bool NullSrcRef::operator==(SrcRef ref) const { return ref == SrcRef(); }

struct SrcSet {
	SrcSet() = default;
	explicit SrcSet(std::vector<IdString> members) : members_(std::move(members)) {}

	bool is_dead() const { return members_.empty(); }
	const std::vector<IdString> &members() const { return members_; }

	bool operator==(const SrcSet &other) const { return members_ == other.members_; }

private:
	std::vector<IdString> members_;
};

struct SrcPool : HashConsPool<SrcPool, SrcSet, SrcRef> {
	static constexpr size_t STATIC_COUNT = 0;

	explicit SrcPool(TwinePool &twines) : twines(twines) {}

	SrcPool(const SrcPool &) = delete;
	SrcPool(SrcPool &&) = delete;
	SrcPool &operator=(const SrcPool &) = delete;
	SrcPool &operator=(SrcPool &&) = delete;

	const SrcSet &operator[](SrcRef ref) const { return HashConsPool::operator[](ref); }

	void clone_from(const SrcPool &other);

	static uint64_t hash_node(const SrcSet &n);

	template<typename F>
	static void for_each_child(const SrcSet&, F&&) {}

	using HashConsPool::size;
	void clear();

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
	pool<std::string> leaves(SrcRef ref) const;

	void root_members(const pool<SrcRef> &live_srcs, pool<IdString> &live_twines) const;
	size_t gc(const pool<SrcRef> &live_srcs);

	void dump(SrcRef ref, std::ostream &os = std::cout) const;
	void dump(std::ostream &os = std::cout) const;

private:
	TwinePool &twines;

	IdString add_location(std::string_view location);
	static void canonicalize_members(std::vector<IdString> &members);
	SrcRef intern(std::vector<IdString> members);
};

YOSYS_NAMESPACE_END

#endif
