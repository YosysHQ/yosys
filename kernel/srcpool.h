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

	constexpr bool operator==(const SrcRef &rhs) const { return value == rhs.value; }

private:
	template<typename, typename, typename, typename> friend struct HashConsPool;
	friend struct SrcPool;
	friend struct SrcPoolIo;

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
	SrcSet(std::vector<IdString> members, Hasher::hash_t hash) : members_(std::move(members)), hash_(hash) {}

	bool is_dead() const { return members_.empty(); }
	const std::vector<IdString> &members() const { return members_; }
	uint64_t hash() const { return hash_; }

	static Hasher::hash_t hash_members(std::span<const IdString> members);

private:
	std::vector<IdString> members_;
	Hasher::hash_t hash_ = 0;
};

struct SrcPool : HashConsPool<SrcPool, SrcSet, SrcRef, Hasher::hash_t> {
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

	static Hasher::hash_t hash_node(const SrcSet &n) { return n.hash(); }

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

	const SrcSet &operator[](SrcRef ref) const {
		check_owned(ref);
		return HashConsPool::operator[](ref);
	}

	void clone_from(const SrcPool &other);
	void clear();
	void root_members(const Marks &live_srcs, pool<IdString> &live_twines) const;
	size_t gc(const Marks &live_srcs);

	SrcRef place(size_t idx, std::span<const IdString> members);
	SrcRef find_members(std::span<const IdString> members) const;

	SrcRef stamp(SrcRef ref) const;
	void check_owned(SrcRef ref) const;

	IdString parse_location(std::string_view location);
	static void canonicalize_members(std::vector<IdString> &members);
	SrcRef intern(std::vector<IdString> members);
	SrcRef intern_unchecked(std::vector<IdString> members);
	SrcRef merge_unchecked(SrcRef a, SrcRef b);
};

struct SrcPoolIo {
	static size_t index(const SrcPool &pool, SrcRef ref);
	static SrcRef place(SrcPool &pool, size_t idx, std::span<const IdString> members);
	static SrcRef find(const SrcPool &pool, std::span<const IdString> members);
	static void finish_placement(SrcPool &pool);
};

YOSYS_NAMESPACE_END

#endif
