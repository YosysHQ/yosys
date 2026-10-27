#ifndef YOSYS_SRCPOOL_H
#define YOSYS_SRCPOOL_H

#include "kernel/metadata/twineset.h"

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
	template<typename, typename> friend struct TwineSetPool;
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

struct SrcPool : TwineSetPool<SrcPool, SrcRef> {
	using TwineSetPool::TwineSetPool;

	SrcRef add(std::string_view text);
	SrcRef add(const std::string &file, const std::string &tail);

	std::string str(SrcRef ref) const;
	pool<std::string> leaves(SrcRef ref) const;

private:
	IdString add_location(std::string_view location);
};

YOSYS_NAMESPACE_END

#endif
