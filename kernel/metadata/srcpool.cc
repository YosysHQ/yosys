#include "kernel/metadata/srcpool.h"
#include "kernel/metadata/twineset_impl.h"

YOSYS_NAMESPACE_BEGIN

template struct HashConsPool<SrcPool, TwineSet, SrcRef>;
template struct TwineBackedPool<SrcPool, TwineSet, SrcRef>;
template struct TwineSetPool<SrcPool, SrcRef>;

template<typename T> concept Ordered = requires(T a) { a < a; };
template<typename T> concept Indexable = requires(T a) { a.raw(); };
static_assert(!Ordered<SrcRef> && !Indexable<SrcRef>);
static_assert(Ordered<IdString> && Indexable<IdString>);

IdString SrcPool::add_location(std::string_view location) {
	size_t colon = location.rfind(':');
	if (colon == std::string_view::npos || colon == 0)
		return twines.add(TwineSpec{TwineSpec::Root{std::string(location)}});
	IdString prefix = twines.add(TwineSpec{TwineSpec::Root{std::string(location.substr(0, colon))}});
	return twines.add(prefix, location.substr(colon));
}

SrcRef SrcPool::add(std::string_view text) {
	std::vector<IdString> members;
	while (!text.empty()) {
		size_t bar = text.find('|');
		std::string_view location = text.substr(0, bar);
		if (!location.empty())
			members.push_back(add_location(location));
		if (bar == std::string_view::npos)
			break;
		text.remove_prefix(bar + 1);
	}
	return intern(std::move(members));
}

SrcRef SrcPool::add(const std::string &file, const std::string &tail) {
	IdString prefix = twines.add(TwineSpec{TwineSpec::Root{file}});
	return intern({twines.add(prefix, tail)});
}

std::string SrcPool::str(SrcRef ref) const {
	std::string out;
	if (ref == SrcRef::Null)
		return out;
	bool first = true;
	for (IdString member : (*this)[ref].members()) {
		if (!first)
			out += '|';
		first = false;
		out += twines.str(member);
	}
	return out;
}

pool<std::string> SrcPool::leaves(SrcRef ref) const {
	pool<std::string> out;
	if (ref == SrcRef::Null)
		return out;
	for (IdString member : (*this)[ref].members())
		out.insert(twines.str(member));
	return out;
}

YOSYS_NAMESPACE_END
