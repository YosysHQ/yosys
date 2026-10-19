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
public:
	bool is_live(Ref ref) const;

protected:
	std::deque<Node> backing;
	std::vector<Ref> table;
	std::vector<size_t> free_list;

	HashConsPool();
	HashConsPool(const HashConsPool& other) = default;
	HashConsPool(HashConsPool&& other);
	HashConsPool& operator=(const HashConsPool& other) = default;
	HashConsPool& operator=(HashConsPool&& other);

	static void check_ready();

	const Node& operator[] (Ref ref) const;

	template<typename Eq>
	Ref find_hashed(uint64_t hash, Eq&& eq) const;
	Ref add_inner(Node t);

	template<typename Roots>
	size_t gc(const Roots& roots);

private:
	Derived* self();
	const Derived* self() const;

	void reset();

	static bool is_static(Ref ref);

	struct RefIterator {
		const HashConsPool* pool;
		size_t idx;
		size_t stop;
		bool skip_dead;

		void settle();
		Ref operator*() const;
		RefIterator& operator++();
		bool operator!=(const RefIterator& other) const;
	};

	struct RefRange {
		const HashConsPool* pool;
		size_t first;
		size_t stop;
		bool skip_dead;

		RefIterator begin() const;
		RefIterator end() const;
	};

	RefRange refs(bool include_statics = true) const;
	// Includes the dead
	RefRange slots() const;

	void rebuild_index();
	size_t home_slot(uint64_t hash) const;
	size_t next_slot(size_t slot) const;
	void index_insert(Ref ref);
	void index_erase(Ref ref);
	void grow_index();

	size_t size() const;
	bool slot_live(size_t abs) const;
	void mark_live(Ref ref, pool<Ref>& live) const;
};

YOSYS_NAMESPACE_END

#endif
