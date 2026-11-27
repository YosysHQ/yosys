#ifndef YOSYS_HASHCONS_IMPL_H
#define YOSYS_HASHCONS_IMPL_H

#include "kernel/hashcons.h"

#include <algorithm>

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref, typename HashType>
bool HashConsPool<Derived, Node, Ref, HashType>::is_live(Ref ref) const {
	Ref idx = ref.untag();
	if (is_static(idx))
		return true;
	size_t slot = idx.raw() - Derived::STATIC_COUNT;
	return slot < backing.size() && !backing[slot].is_dead();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::check_ready() {}

template<typename Derived, typename Node, typename Ref, typename HashType>
const Node& HashConsPool<Derived, Node, Ref, HashType>::operator[] (Ref ref) const {
	Ref idx = ref.untag();
	if constexpr (Derived::STATIC_COUNT != 0) {
		if (is_static(idx))
			return Derived::static_node(idx.raw());
	}
	return backing[idx.raw() - Derived::STATIC_COUNT];
}

template<typename Derived, typename Node, typename Ref, typename HashType>
Derived* HashConsPool<Derived, Node, Ref, HashType>::self() { return static_cast<Derived*>(this); }

template<typename Derived, typename Node, typename Ref, typename HashType>
const Derived* HashConsPool<Derived, Node, Ref, HashType>::self() const { return static_cast<const Derived*>(this); }

template<typename Derived, typename Node, typename Ref, typename HashType>
bool HashConsPool<Derived, Node, Ref, HashType>::is_static(Ref ref) {
	if constexpr (Derived::STATIC_COUNT == 0)
		return false;
	else
		return ref.raw() < Derived::STATIC_COUNT;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::RefIterator::settle() {
	while (skip_dead && idx < stop && !pool->slot_live(idx))
		idx++;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
Ref HashConsPool<Derived, Node, Ref, HashType>::RefIterator::operator*() const { return Ref(idx); }

template<typename Derived, typename Node, typename Ref, typename HashType>
auto HashConsPool<Derived, Node, Ref, HashType>::RefIterator::operator++() -> RefIterator& { idx++; settle(); return *this; }

template<typename Derived, typename Node, typename Ref, typename HashType>
bool HashConsPool<Derived, Node, Ref, HashType>::RefIterator::operator!=(const RefIterator& other) const { return idx != other.idx; }

template<typename Derived, typename Node, typename Ref, typename HashType>
auto HashConsPool<Derived, Node, Ref, HashType>::RefRange::begin() const -> RefIterator {
	RefIterator it{pool, first, stop, skip_dead};
	it.settle();
	return it;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
auto HashConsPool<Derived, Node, Ref, HashType>::RefRange::end() const -> RefIterator { return RefIterator{pool, stop, stop, skip_dead}; }

template<typename Derived, typename Node, typename Ref, typename HashType>
auto HashConsPool<Derived, Node, Ref, HashType>::refs(bool include_statics) const -> RefRange {
	return RefRange{this, include_statics ? 0 : Derived::STATIC_COUNT,
			Derived::STATIC_COUNT + backing.size(), true};
}

template<typename Derived, typename Node, typename Ref, typename HashType>
auto HashConsPool<Derived, Node, Ref, HashType>::slots() const -> RefRange {
	return RefRange{this, Derived::STATIC_COUNT,
			Derived::STATIC_COUNT + backing.size(), false};
}

template<typename Derived, typename Node, typename Ref, typename HashType>
size_t HashConsPool<Derived, Node, Ref, HashType>::home_slot(uint64_t hash) const {
	// Knuth's Fibonacci hashing saves us from how bad DJB2 is
	return (hash * 0x9e3779b97f4a7c15ull) >> (64 - std::countr_zero(table.size()));
}

template<typename Derived, typename Node, typename Ref, typename HashType>
size_t HashConsPool<Derived, Node, Ref, HashType>::next_slot(size_t slot) const { return (slot + 1) & (table.size() - 1); }

template<typename Derived, typename Node, typename Ref, typename HashType>
size_t HashConsPool<Derived, Node, Ref, HashType>::size() const { return backing.size() - free_list.size(); }

template<typename Derived, typename Node, typename Ref, typename HashType>
bool HashConsPool<Derived, Node, Ref, HashType>::slot_live(size_t abs) const {
	if (abs < Derived::STATIC_COUNT)
		return true;
	return !backing[abs - Derived::STATIC_COUNT].is_dead();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
HashConsPool<Derived, Node, Ref, HashType>::HashConsPool() { rebuild_index(); }

template<typename Derived, typename Node, typename Ref, typename HashType>
HashConsPool<Derived, Node, Ref, HashType>::HashConsPool(HashConsPool&& other)
	: backing(std::move(other.backing)), table(std::move(other.table)), free_list(std::move(other.free_list)), index_entries(other.index_entries) {
	other.reset();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
HashConsPool<Derived, Node, Ref, HashType>& HashConsPool<Derived, Node, Ref, HashType>::operator=(HashConsPool&& other) {
	if (this != &other) {
		backing = std::move(other.backing);
		table = std::move(other.table);
		free_list = std::move(other.free_list);
		index_entries = other.index_entries;
		other.reset();
	}
	return *this;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::reset() {
	backing.clear();
	free_list.clear();
	rebuild_index();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::rebuild_index() {
	Derived::check_ready();
	free_list.clear();
	for (size_t idx = 0; idx < backing.size(); ++idx)
		if (backing[idx].is_dead())
			free_list.push_back(idx);
	std::sort(free_list.begin(), free_list.end(), std::greater<size_t>());
	table.assign(std::bit_ceil((Derived::STATIC_COUNT + size()) * 2 + 2), Ref());
	index_entries = 0;
	for (Ref ref : refs())
		index_insert(ref);
}

template<typename Derived, typename Node, typename Ref, typename HashType>
template<typename Eq>
Ref HashConsPool<Derived, Node, Ref, HashType>::find_hashed(HashType hash, Eq&& eq) const {
	for (size_t slot = home_slot(hash); table[slot] != Ref(); slot = next_slot(slot)) {
		Ref ref = table[slot];
		if (Derived::hash_node((*this)[ref]) == hash && eq(ref))
			return ref;
	}
	return Ref();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::index_insert(Ref ref) {
	if ((index_entries + 1) * 3 > table.size() * 2)
		grow_index();
	size_t slot = home_slot(Derived::hash_node((*this)[ref]));
	while (table[slot] != Ref())
		slot = next_slot(slot);
	table[slot] = ref;
	index_entries++;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::index_erase(Ref ref) {
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
	index_entries--;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::grow_index() {
	std::vector<Ref> old(table.size() * 2, Ref());
	std::swap(old, table);
	index_entries = 0;
	for (Ref ref : old)
		if (ref != Ref())
			index_insert(ref);
}

template<typename Derived, typename Node, typename Ref, typename HashType>
Ref HashConsPool<Derived, Node, Ref, HashType>::add_inner(Node t) {
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
	index_insert(ref);
	if (yosys_xtrace) {
		std::cout << "#X# add_inner added ";
		self()->dump(ref);
		std::cout << "\n";
		std::cout << "#X# as integer " << ref.raw() << "\n";
	}
	return ref;
}

template<typename Derived, typename Node, typename Ref, typename HashType>
Ref HashConsPool<Derived, Node, Ref, HashType>::place(size_t abs, Node t) {
	log_assert(abs >= Derived::STATIC_COUNT);
	size_t slot = abs - Derived::STATIC_COUNT;
	free_list.clear();
	while (backing.size() <= slot)
		backing.push_back(Node{});
	log_assert(backing[slot].is_dead());
	backing[slot] = std::move(t);
	index_insert(Ref(abs));
	return Ref(abs);
}

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::finish_placement() {
	rebuild_index();
}

template<typename Derived, typename Node, typename Ref, typename HashType>
template<typename Roots>
size_t HashConsPool<Derived, Node, Ref, HashType>::gc(const Roots& roots) {
	std::vector<bool> live(backing.size());
	for (Ref ref : roots)
		mark_live(ref, live);
	size_t erased = 0;
	for (size_t idx = 0; idx < backing.size(); ++idx) {
		if (backing[idx].is_dead())
			continue;
		if (!live[idx]) {
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

template<typename Derived, typename Node, typename Ref, typename HashType>
void HashConsPool<Derived, Node, Ref, HashType>::mark_live(Ref ref, std::vector<bool>& live) const {
	ref = ref.untag();
	if (ref == Ref() || is_static(ref))
		return;
	size_t slot = ref.raw() - Derived::STATIC_COUNT;
	if (live[slot])
		return;
	live[slot] = true;
	Derived::for_each_child((*this)[ref], [&](Ref child) { mark_live(child, live); });
}

YOSYS_NAMESPACE_END

#endif
