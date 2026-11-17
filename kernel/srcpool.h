#ifndef YOSYS_SRCPOOL_H
#define YOSYS_SRCPOOL_H

#include "kernel/hashcons.h"
#include "kernel/twine.h"

#include <span>
#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct SrcRef {
	static const SrcRef Null;

	constexpr SrcRef() : value(NULL_VAL) {}

	constexpr bool operator==(const SrcRef&) const = default;

private:
	template<typename, typename, typename> friend struct HashConsPool;
	friend struct SrcPool;
	friend struct SrcPoolIo;

	explicit constexpr SrcRef(size_t val) : value((uint32_t) val) {}
	constexpr size_t raw() const { return value; }
	constexpr SrcRef untag() const { return *this; }

	static constexpr uint32_t NULL_VAL = ~uint32_t{0};
	uint32_t value;
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

struct SrcPool : HashConsPool<SrcPool, SrcSet, SrcRef> {
	static constexpr size_t STATIC_COUNT = 0;

	struct Marks {
		bool insert(SrcRef ref);
		bool empty() const { return refs.empty(); }
		std::vector<SrcRef>::const_iterator begin() const { return refs.begin(); }
		std::vector<SrcRef>::const_iterator end() const { return refs.end(); }

	private:
		std::vector<SrcRef> refs;
		std::vector<bool> seen;
	};

	explicit SrcPool(TwinePool &twines) : twines(twines) {}

	TwinePool &twines;

	SrcPool(const SrcPool &) = delete;
	SrcPool(SrcPool &&) = delete;
	SrcPool &operator=(const SrcPool &) = delete;
	SrcPool &operator=(SrcPool &&) = delete;

	static uint64_t hash_node(const SrcSet &n);

	template<typename F>
	static void for_each_child(const SrcSet&, F&&) {}

	using HashConsPool::size;

	IdString file(std::string_view name);
	IdString location(IdString file, int line);
	IdString location(IdString file, int line, int col);
	IdString location(IdString file, int line1, int col1, int line2, int col2);
	SrcRef add(IdString location);
	SrcRef add(std::span<const IdString> locations);
	SrcRef add_parsed(std::string_view text);
	SrcRef merge(std::span<const SrcRef> refs);
	SrcRef merge(SrcRef a, SrcRef b);
	SrcRef copy_from(const SrcPool &other, SrcRef ref);

	std::string str(SrcRef ref) const;
	const std::vector<IdString> &locations(SrcRef ref) const;

	void dump(SrcRef ref, std::ostream &os = std::cout) const;
	void dump(std::ostream &os = std::cout) const;

private:
	friend struct RTLIL::Design;
	friend struct SrcPoolIo;
	friend struct SrcEq;

	const SrcSet &operator[](SrcRef ref) const { return HashConsPool::operator[](ref); }

	void clone_from(const SrcPool &other);
	void clear();
	void root_members(const Marks &live_srcs, pool<IdString> &live_twines) const;
	size_t gc(const Marks &live_srcs);

	SrcRef place(size_t idx, std::span<const IdString> members);
	SrcRef find_members(std::span<const IdString> members) const;

	IdString parse_location(std::string_view location);
	static void canonicalize_members(std::vector<IdString> &members);
	SrcRef intern(std::vector<IdString> members);
};

struct SrcPoolIo {
	static size_t index(const SrcPool &pool, SrcRef ref);
	static SrcRef place(SrcPool &pool, size_t idx, std::span<const IdString> members);
	static SrcRef find(const SrcPool &pool, std::span<const IdString> members);
	static void finish_placement(SrcPool &pool);
};

YOSYS_NAMESPACE_END

#endif
