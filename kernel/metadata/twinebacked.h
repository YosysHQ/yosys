#ifndef YOSYS_TWINEBACKED_H
#define YOSYS_TWINEBACKED_H

#include "kernel/hashcons.h"
#include "kernel/twine.h"

#include <vector>

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
struct TwineBackedPool : HashConsPool<Derived, Node, Ref> {
	static constexpr size_t STATIC_COUNT = 0;

	struct Marks {
		bool insert(Ref ref);
		bool empty() const { return refs.empty(); }
		typename std::vector<Ref>::const_iterator begin() const { return refs.begin(); }
		typename std::vector<Ref>::const_iterator end() const { return refs.end(); }

	private:
		std::vector<Ref> refs;
		std::vector<bool> seen;
	};

	explicit TwineBackedPool(TwinePool &twines) : twines(twines) {}

	TwineBackedPool(const TwineBackedPool &) = delete;
	TwineBackedPool(TwineBackedPool &&) = delete;
	TwineBackedPool &operator=(const TwineBackedPool &) = delete;
	TwineBackedPool &operator=(TwineBackedPool &&) = delete;

	const Node &operator[](Ref ref) const;

	template<typename F>
	static void for_each_child(const Node&, F&&) {}

	using HashConsPool<Derived, Node, Ref>::size;
	void clone_from(const Derived &other);
	void clear();
	size_t gc(const Marks &live);

protected:
	TwinePool &twines;

	Ref stamp(Ref ref) const;
	void check_owned(Ref ref) const;
	Ref intern_node(Node node);
	Ref find_node(const Node &node) const;
};

YOSYS_NAMESPACE_END

#endif
