#ifndef YOSYS_HASHCONS_H
#define YOSYS_HASHCONS_H

#include "kernel/yosys_common.h"

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

	HashConsPool();
	HashConsPool(const HashConsPool& other) = default;
	HashConsPool(HashConsPool&& other);
	HashConsPool& operator=(const HashConsPool& other) = default;
	HashConsPool& operator=(HashConsPool&& other);

	void reset();

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

	void rebuild_index();

	size_t home_slot(uint64_t hash) const {
		// Knuth's Fibonacci hashing saves us from how bad DJB2 is
		return (hash * 0x9e3779b97f4a7c15ull) >> (64 - std::countr_zero(table.size()));
	}

	size_t next_slot(size_t slot) const { return (slot + 1) & (table.size() - 1); }

	template<typename Eq>
	Ref find_hashed(uint64_t hash, Eq&& eq) const;
	void index_insert(Ref ref);
	void index_erase(Ref ref);
	void grow_index();
	Ref add_inner(Node t);

	size_t size() const { return backing.size() - free_list.size(); }

	bool slot_live(size_t abs) const {
		if (abs < Derived::STATIC_COUNT)
			return true;
		return !backing[abs - Derived::STATIC_COUNT].is_dead();
	}

	template<typename Roots>
	size_t gc(const Roots& roots);
	void mark_live(Ref ref, pool<Ref>& live) const;
};

YOSYS_NAMESPACE_END

#endif
