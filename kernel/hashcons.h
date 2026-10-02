#ifndef YOSYS_HASHCONS_H
#define YOSYS_HASHCONS_H

#include "kernel/yosys_common.h"

#include <algorithm>
#include <bit>
#include <deque>
#include <vector>

/**
 * Implements deduplicating backing storage indexed by content hash
 */

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
struct HashConsPool {
protected:
	std::deque<Node> backing;
	std::vector<Ref> table;
	std::vector<size_t> free_list;

public:
	Derived* self() { return static_cast<Derived*>(this); }
	const Derived* self() const { return static_cast<const Derived*>(this); }

	HashConsPool() { rebuild_index(); }
	HashConsPool(const HashConsPool& other) = default;
	HashConsPool(HashConsPool&& other)
		: backing(std::move(other.backing)), table(std::move(other.table)), free_list(std::move(other.free_list)) {
		other.reset();
	}
	HashConsPool& operator=(const HashConsPool& other) = default;
	HashConsPool& operator=(HashConsPool&& other) {
		if (this != &other) {
			backing = std::move(other.backing);
			table = std::move(other.table);
			free_list = std::move(other.free_list);
			other.reset();
		}
		return *this;
	}

	void reset() {
		backing.clear();
		free_list.clear();
		rebuild_index();
	}

	static bool is_static(Ref ref) {
		if constexpr (Derived::STATIC_COUNT == 0)
			return false;
		else
			return ref.raw() < Derived::STATIC_COUNT;
	}

	const Node& operator[] (Ref ref) const {
		Ref idx = ref.untag();
		if constexpr (Derived::STATIC_COUNT != 0) {
			if (is_static(idx))
				return Derived::static_node(idx.raw());
		}
		return backing[idx.raw() - Derived::STATIC_COUNT];
	}

	bool is_live(Ref ref) const {
		Ref idx = ref.untag();
		if (is_static(idx))
			return true;
		size_t slot = idx.raw() - Derived::STATIC_COUNT;
		return slot < backing.size() && !backing[slot].is_dead();
	}

	struct RefIterator {
		const HashConsPool* pool;
		size_t idx;
		size_t stop;
		bool skip_dead;

		void settle() {
			while (skip_dead && idx < stop && !pool->slot_live(idx))
				idx++;
		}

		Ref operator*() const { return Ref(idx); }
		RefIterator& operator++() { idx++; settle(); return *this; }
		bool operator!=(const RefIterator& other) const { return idx != other.idx; }
	};

	struct RefRange {
		const HashConsPool* pool;
		size_t first;
		size_t stop;
		bool skip_dead;

		RefIterator begin() const {
			RefIterator it{pool, first, stop, skip_dead};
			it.settle();
			return it;
		}
		RefIterator end() const { return RefIterator{pool, stop, stop, skip_dead}; }
	};

	RefRange refs(bool include_statics = true) const {
		return RefRange{this, include_statics ? 0 : Derived::STATIC_COUNT,
				Derived::STATIC_COUNT + backing.size(), true};
	}

	// Includes the dead
	RefRange slots() const {
		return RefRange{this, Derived::STATIC_COUNT,
				Derived::STATIC_COUNT + backing.size(), false};
	}

	static void check_ready() {}

	void rebuild_index() {
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

	size_t home_slot(uint64_t hash) const {
		// Knuth's Fibonacci hashing saves us from how bad DJB2 is
		return (hash * 0x9e3779b97f4a7c15ull) >> (64 - std::countr_zero(table.size()));
	}

	size_t next_slot(size_t slot) const { return (slot + 1) & (table.size() - 1); }

	template<typename Eq>
	Ref find_hashed(uint64_t hash, Eq&& eq) const {
		for (size_t slot = home_slot(hash); table[slot] != Ref(); slot = next_slot(slot)) {
			Ref ref = table[slot];
			if (Derived::hash_node((*this)[ref]) == hash && eq(ref))
				return ref;
		}
		return Ref();
	}

	void index_insert(Ref ref) {
		size_t slot = home_slot(Derived::hash_node((*this)[ref]));
		while (table[slot] != Ref())
			slot = next_slot(slot);
		table[slot] = ref;
	}

	void index_erase(Ref ref) {
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

	void grow_index() {
		std::vector<Ref> old(table.size() * 2, Ref());
		std::swap(old, table);
		for (Ref ref : old)
			if (ref != Ref())
				index_insert(ref);
	}

	Ref add_inner(Node t) {
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

	size_t size() const { return backing.size() - free_list.size(); }

	bool slot_live(size_t abs) const {
		if (abs < Derived::STATIC_COUNT)
			return true;
		return !backing[abs - Derived::STATIC_COUNT].is_dead();
	}

	template<typename Roots>
	size_t gc(const Roots& roots) {
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

	void mark_live(Ref ref, pool<Ref>& live) const {
		ref = ref.untag();
		if (ref == Ref() || is_static(ref) || !live.insert(ref).second)
			return;
		Derived::for_each_child((*this)[ref], [&](Ref child) { mark_live(child, live); });
	}
};

YOSYS_NAMESPACE_END

#endif
