#include "kernel/srcpool.h"
#include "kernel/hashcons_impl.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

template struct HashConsPool<SrcPool, SrcSet, SrcRef>;

struct SrcEq {
	const SrcPool &pool;
	const SrcSet &node;
	bool operator()(SrcRef ref) const { return pool[ref] == node; }
};

void SrcPool::clone_from(const SrcPool &other) {
	log_assert(twines.shares_index_space_with(other.twines));
	HashConsPool::operator=(static_cast<const HashConsPool &>(other));
}

void SrcPool::clear() {
	backing.clear();
	free_list.clear();
	std::fill(table.begin(), table.end(), SrcRef());
}

uint64_t SrcPool::hash_node(const SrcSet &n) {
	Hasher h;
	for (IdString member : n.members())
		h.eat(member);
	return h.yield();
}

IdString SrcPool::add_location(std::string_view location) {
	size_t colon = location.rfind(':');
	if (colon == std::string_view::npos || colon == 0)
		return twines.add(TwineSpec{TwineSpec::Leaf{std::string(location)}});
	IdString prefix = twines.add(TwineSpec{TwineSpec::Leaf{std::string(location.substr(0, colon))}});
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
	IdString prefix = twines.add(TwineSpec{TwineSpec::Leaf{file}});
	return intern({twines.add(prefix, tail)});
}

SrcRef SrcPool::merge(std::span<const SrcRef> refs) {
	std::vector<IdString> members;
	for (SrcRef ref : refs)
		if (ref != SrcRef::Null)
			members.insert(members.end(), (*this)[ref].members().begin(), (*this)[ref].members().end());
	return intern(std::move(members));
}

SrcRef SrcPool::merge(SrcRef a, SrcRef b) {
	SrcRef both[] = {a, b};
	return merge(std::span<const SrcRef>{both});
}

SrcRef SrcPool::adopt(std::span<const IdString> members) {
	return intern(std::vector<IdString>(members.begin(), members.end()));
}

SrcRef SrcPool::place(size_t idx, std::span<const IdString> members) {
	std::vector<IdString> canon(members.begin(), members.end());
	canonicalize_members(canon);
	if (canon.empty())
		return SrcRef::Null;
	return HashConsPool::place(idx, SrcSet{std::move(canon)});
}

SrcRef SrcPool::find_members(std::span<const IdString> members) const {
	std::vector<IdString> canon(members.begin(), members.end());
	canonicalize_members(canon);
	if (canon.empty())
		return SrcRef::Null;
	SrcSet node{std::move(canon)};
	return find_hashed(hash_node(node), SrcEq{*this, node});
}

SrcRef SrcPool::copy_from(const SrcPool &other, SrcRef ref) {
	if (ref == SrcRef::Null)
		return ref;
	std::vector<IdString> members;
	members.reserve(other[ref].members().size());
	for (IdString member : other[ref].members())
		members.push_back(twines.copy_from(other.twines, member));
	return intern(std::move(members));
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

void SrcPool::root_members(const pool<SrcRef> &live_srcs, pool<IdString> &live_twines) const {
	for (SrcRef ref : live_srcs)
		for (IdString member : (*this)[ref].members())
			live_twines.insert(member);
}

size_t SrcPool::gc(const pool<SrcRef> &live_srcs) {
	return HashConsPool::gc(live_srcs);
}

void SrcPool::dump(SrcRef ref, std::ostream &os) const {
	os << "Set[";
	bool first = true;
	for (IdString member : (*this)[ref].members()) {
		if (!first)
			os << ", ";
		first = false;
		os << "@" << member.raw();
	}
	os << "]";
}

void SrcPool::dump(std::ostream &os) const {
	os << "--- SrcPool Dump (" << size() << " nodes) ---\n";
	for (size_t idx = 0; idx < backing.size(); ++idx) {
		if (backing[idx].is_dead())
			continue;
		os << idx << " -> ";
		dump(SrcRef(idx), os);
		os << '\n';
	}
	os << "--------------------------------\n";
}

void SrcPool::canonicalize_members(std::vector<IdString> &members) {
	for (IdString &member : members)
		member = member.untag().stamped(0);
	std::sort(members.begin(), members.end());
	members.erase(std::unique(members.begin(), members.end()), members.end());
}

SrcRef SrcPool::intern(std::vector<IdString> members) {
	canonicalize_members(members);
	if (members.empty())
		return SrcRef::Null;
	SrcSet node{std::move(members)};
	SrcRef found = find_hashed(hash_node(node), SrcEq{*this, node});
	if (found != SrcRef::Null)
		return found;
	return add_inner(std::move(node));
}

YOSYS_NAMESPACE_END
