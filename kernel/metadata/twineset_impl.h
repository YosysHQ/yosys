#ifndef YOSYS_TWINESET_IMPL_H
#define YOSYS_TWINESET_IMPL_H

#include "kernel/metadata/twineset.h"
#include "kernel/metadata/twinebacked_impl.h"

#include <algorithm>

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Ref>
uint64_t TwineSetPool<Derived, Ref>::hash_node(const TwineSet &n) {
	Hasher h;
	for (IdString member : n.members())
		h.eat(member);
	return h.yield();
}

template<typename Derived, typename Ref>
std::vector<IdString> TwineSetPool<Derived, Ref>::canonical(std::span<const IdString> members) {
	std::vector<IdString> out;
	out.reserve(members.size());
	for (IdString member : members)
		out.push_back(member.untag().stamped(0));
	std::sort(out.begin(), out.end());
	out.erase(std::unique(out.begin(), out.end()), out.end());
	return out;
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::intern(std::vector<IdString> members) {
	members = canonical(members);
	if (members.empty())
		return Ref();
	return this->intern_node(TwineSet{std::move(members)});
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::adopt(std::span<const IdString> members) {
	return intern(std::vector<IdString>(members.begin(), members.end()));
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::merge(std::span<const Ref> refs) {
	std::vector<IdString> members;
	for (Ref ref : refs)
		if (ref != Ref())
			members.insert(members.end(), (*this)[ref].members().begin(), (*this)[ref].members().end());
	return intern(std::move(members));
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::merge(Ref a, Ref b) {
	Ref both[] = {a, b};
	return merge(std::span<const Ref>{both});
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::with_member(Ref ref, IdString member) {
	std::vector<IdString> members{member};
	if (ref != Ref())
		members.insert(members.end(), (*this)[ref].members().begin(), (*this)[ref].members().end());
	return intern(std::move(members));
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::without_member(Ref ref, IdString member) {
	if (ref == Ref())
		return ref;
	std::vector<IdString> members = (*this)[ref].members();
	std::erase(members, member.untag().stamped(0));
	return intern(std::move(members));
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::place(size_t idx, std::span<const IdString> members) {
	std::vector<IdString> canon = canonical(members);
	if (canon.empty())
		return Ref();
	return this->stamp(HashConsPool<Derived, TwineSet, Ref>::place(idx, TwineSet{std::move(canon)}));
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::find_members(std::span<const IdString> members) const {
	std::vector<IdString> canon = canonical(members);
	if (canon.empty())
		return Ref();
	return this->find_node(TwineSet{std::move(canon)});
}

template<typename Derived, typename Ref>
Ref TwineSetPool<Derived, Ref>::copy_from(const Derived &other, Ref ref) {
	if (ref == Ref())
		return ref;
	std::vector<IdString> members;
	members.reserve(other[ref].members().size());
	for (IdString member : other[ref].members())
		members.push_back(this->twines.copy_from(other.twines, member));
	return intern(std::move(members));
}

template<typename Derived, typename Ref>
std::string TwineSetPool<Derived, Ref>::serial(Ref ref) const {
	this->check_owned(ref);
	return std::to_string(ref.raw());
}

template<typename Derived, typename Ref>
void TwineSetPool<Derived, Ref>::root_members(const Marks &live, pool<IdString> &live_twines) const {
	for (Ref ref : live)
		for (IdString member : (*this)[ref].members())
			live_twines.insert(member);
}

template<typename Derived, typename Ref>
void TwineSetPool<Derived, Ref>::dump(Ref ref, std::ostream &os) const {
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

template<typename Derived, typename Ref>
void TwineSetPool<Derived, Ref>::dump(std::ostream &os) const {
	os << "--- Twine set pool dump (" << this->size() << " nodes) ---\n";
	for (size_t idx = 0; idx < this->backing.size(); ++idx) {
		if (this->backing[idx].is_dead())
			continue;
		os << idx << " -> ";
		dump(Ref(idx), os);
		os << '\n';
	}
	os << "--------------------------------\n";
}

YOSYS_NAMESPACE_END

#endif
