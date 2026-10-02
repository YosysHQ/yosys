#ifndef YOSYS_HASHCONS_IMPL_H
#define YOSYS_HASHCONS_IMPL_H

#include "kernel/hashcons.h"

#include <algorithm>

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
HashConsPool<Derived, Node, Ref>::HashConsPool() { rebuild_index(); }

template<typename Derived, typename Node, typename Ref>
HashConsPool<Derived, Node, Ref>::HashConsPool(HashConsPool&& other)
	: backing(std::move(other.backing)), table(std::move(other.table)), free_list(std::move(other.free_list)) {
	other.reset();
}

template<typename Derived, typename Node, typename Ref>
HashConsPool<Derived, Node, Ref>& HashConsPool<Derived, Node, Ref>::operator=(HashConsPool&& other) {
	if (this != &other) {
		backing = std::move(other.backing);
		table = std::move(other.table);
		free_list = std::move(other.free_list);
		other.reset();
	}
	return *this;
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::reset() {
	backing.clear();
	free_list.clear();
	rebuild_index();
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::rebuild_index() {
	Derived::check_ready();
	free_list.clear();
	for (size_t idx = 0; idx < backing.size(); ++idx)
		if (backing[idx].is_dead())
			free_list.push_back(idx);
	std::sort(free_list.begin(), free_list.end(), std::greater<size_t>());
	table.assign(std::bit_ceil((Derived::STATIC_COUNT + size()) * 2 + 2), Ref());
	for (Ref ref : refs())
		index_insert(ref);
}

template<typename Derived, typename Node, typename Ref>
template<typename Eq>
Ref HashConsPool<Derived, Node, Ref>::find_hashed(uint64_t hash, Eq&& eq) const {
	for (size_t slot = home_slot(hash); table[slot] != Ref(); slot = next_slot(slot)) {
		Ref ref = table[slot];
		if (Derived::hash_node((*this)[ref]) == hash && eq(ref))
			return ref;
	}
	return Ref();
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::index_insert(Ref ref) {
	size_t slot = home_slot(Derived::hash_node((*this)[ref]));
	while (table[slot] != Ref())
		slot = next_slot(slot);
	table[slot] = ref;
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::index_erase(Ref ref) {
	size_t hole = home_slot(Derived::hash_node((*this)[ref]));
	while (table[hole] != ref)
		hole = next_slot(hole);
	size_t mask = table.size() - 1;
	for (size_t slot = next_slot(hole); table[slot] != Ref(); slot = next_slot(slot)) {
		size_t home = home_slot(Derived::hash_node((*this)[table[slot]]));
		if (((slot - home) & mask) >= ((slot - hole) & mask)) {
			table[hole] = table[slot];
			hole = slot;
		}
	}
	table[hole] = Ref();
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::grow_index() {
	std::vector<Ref> old(table.size() * 2, Ref());
	std::swap(old, table);
	for (Ref ref : old)
		if (ref != Ref())
			index_insert(ref);
}

template<typename Derived, typename Node, typename Ref>
Ref HashConsPool<Derived, Node, Ref>::add_inner(Node t) {
	Ref ref;
	if (!free_list.empty()) {
		size_t idx = free_list.back();
		free_list.pop_back();
		backing[idx] = std::move(t);
		ref = Ref(Derived::STATIC_COUNT + idx);
	} else {
		ref = Ref(Derived::STATIC_COUNT + backing.size());
		backing.push_back(std::move(t));
	}
	if ((Derived::STATIC_COUNT + size()) * 3 > table.size() * 2)
		grow_index();
	index_insert(ref);
	if (yosys_xtrace) {
		std::cout << "#X# add_inner added ";
		self()->dump(ref);
		std::cout << "\n";
		std::cout << "#X# as integer " << ref.raw() << "\n";
	}
	return ref;
}

template<typename Derived, typename Node, typename Ref>
template<typename Roots>
size_t HashConsPool<Derived, Node, Ref>::gc(const Roots& roots) {
	pool<Ref> live;
	for (Ref ref : roots)
		mark_live(ref, live);
	size_t erased = 0;
	for (size_t idx = 0; idx < backing.size(); ++idx) {
		if (backing[idx].is_dead())
			continue;
		if (!live.count(Ref(Derived::STATIC_COUNT + idx))) {
			index_erase(Ref(Derived::STATIC_COUNT + idx));
			free_list.push_back(idx);
			backing[idx] = Node{};
			erased++;
		}
	}
	// TODO something like YOSYS_SORT_ID_FREE_LIST to make it optional?
	std::sort(free_list.begin(), free_list.end(), std::greater<size_t>());
	return erased;
}

template<typename Derived, typename Node, typename Ref>
void HashConsPool<Derived, Node, Ref>::mark_live(Ref ref, pool<Ref>& live) const {
	ref = ref.untag();
	if (ref == Ref() || is_static(ref) || !live.insert(ref).second)
		return;
	Derived::for_each_child((*this)[ref], [&](Ref child) { mark_live(child, live); });
}

YOSYS_NAMESPACE_END

#endif
