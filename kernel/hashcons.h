#ifndef YOSYS_HASHCONS_H
#define YOSYS_HASHCONS_H

#include "kernel/yosys_common.h"

#include <algorithm>
#include <deque>
#include <unordered_set>
#include <vector>

/** 
 * Implements TwinePool shallow deduplicating backing storage
 */

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
struct HashConsNodeHash {
	using is_transparent = void;

	const Derived* pool = nullptr;

	size_t operator()(const Node& n) const noexcept { return Derived::hash_node(n); }
	size_t operator()(Ref ref) const noexcept { return Derived::hash_node((*pool)[ref]); }
};

YOSYS_NAMESPACE_END

// Turn on caching in the standard library for performance
#ifdef __GLIBCXX__
namespace std {
	template<typename Derived, typename Node, typename Ref>
	struct __is_fast_hash<YOSYS_NAMESPACE::HashConsNodeHash<Derived, Node, Ref>>
		: std::false_type {};
}
#endif

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
struct HashConsPool {
	using NodeHash = HashConsNodeHash<Derived, Node, Ref>;

	struct NodeEq {
		using is_transparent = void;
		const Derived* pool = nullptr;
		bool operator()(Ref a, Ref b) const noexcept { return (*pool)[a].data == (*pool)[b].data; }
		bool operator()(Ref a, const Node& b) const noexcept { return (*pool)[a].data == b.data; }
		bool operator()(const Node& a, Ref b) const noexcept { return a.data == (*pool)[b].data; }
	};

	using Index = std::unordered_set<Ref, NodeHash, NodeEq>;

protected:
	std::deque<Node> backing;
	Index index;
	// Indices of monostate, kept sorted
	std::vector<size_t> free_list;

public:
	Derived* self() { return static_cast<Derived*>(this); }
	const Derived* self() const { return static_cast<const Derived*>(this); }

	Index fresh_index() { return Index(0, NodeHash{self()}, NodeEq{self()}); }

	HashConsPool() : index(fresh_index()) { rebuild_index(); }
	HashConsPool(const HashConsPool& other) : backing(other.backing), index(fresh_index()) {
		rebuild_index();
	}
	HashConsPool(HashConsPool&& other) : backing(std::move(other.backing)), index(fresh_index()) {
		other.reset();
		rebuild_index();
	}
	HashConsPool& operator=(const HashConsPool& other) {
		if (this != &other) {
			backing = other.backing;
			index = fresh_index();
			rebuild_index();
		}
		return *this;
	}
	HashConsPool& operator=(HashConsPool&& other) {
		if (this != &other) {
			backing = std::move(other.backing);
			other.reset();
			index = fresh_index();
			rebuild_index();
		}
		return *this;
	}

	void reset() {
		backing.clear();
		free_list.clear();
		index = fresh_index();
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
		for (size_t idx = 0; idx < Derived::STATIC_COUNT; idx++)
			index.insert(Ref(idx));
		free_list.clear();
		for (size_t idx = 0; idx < backing.size(); ++idx) {
			if (backing[idx].is_dead())
				free_list.push_back(idx);
			else
				index.insert(Ref(Derived::STATIC_COUNT + idx));
		}
		std::sort(free_list.begin(), free_list.end(), std::greater<size_t>());
	}

	Ref find(Node t) const {
		Derived::canonicalize(t);
		if (auto it = index.find(t); it != index.end())
			return *it;
		return Ref();
	}

	Ref add_inner(Node t) {
		Derived::canonicalize(t);

		if (auto it = index.find(t); it != index.end()) {
			if (yosys_xtrace) {
				std::cout << "#X# add_inner found ";
				self()->dump(*it);
				std::cout << "\n";
				std::cout << "#X# as integer " << it->raw() << "\n";
			}
			return *it;
		}

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
		index.insert(ref);
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
				index.erase(Ref(Derived::STATIC_COUNT + idx));
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
