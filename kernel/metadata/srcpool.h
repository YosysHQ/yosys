#ifndef YOSYS_SRCPOOL_H
#define YOSYS_SRCPOOL_H

#include "kernel/metadata/twineset.h"

#include <span>
#include <string>
#include <string_view>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct SrcRef : PoolRef<SrcRef> {
	static const SrcRef Null;

	constexpr SrcRef() = default;

	constexpr bool operator==(const SrcRef &rhs) const { return value == rhs.value; }

private:
	template<typename> friend struct PoolRef;
	template<typename, typename, typename> friend struct HashConsPool;
	template<typename, typename, typename> friend struct TwineBackedPool;
	template<typename, typename> friend struct TwineSetPool;
	friend struct SrcPool;

	using PoolRef::PoolRef;
	constexpr SrcRef untag() const { return *this; }
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
