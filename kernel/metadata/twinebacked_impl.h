#ifndef YOSYS_TWINEBACKED_IMPL_H
#define YOSYS_TWINEBACKED_IMPL_H

#include "kernel/metadata/twinebacked.h"
#include "kernel/hashcons_impl.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

template<typename Derived, typename Node, typename Ref>
bool TwineBackedPool<Derived, Node, Ref>::Marks::insert(Ref ref) {
	size_t idx = ref.untag().raw();
	if (idx >= seen.size())
		seen.resize(idx + 1);
	if (seen[idx])
		return false;
	seen[idx] = true;
	refs.push_back(ref);
	return true;
}

template<typename Derived, typename Node, typename Ref>
const Node &TwineBackedPool<Derived, Node, Ref>::operator[](Ref ref) const {
	check_owned(ref);
	return HashConsPool<Derived, Node, Ref>::operator[](ref);
}

template<typename Derived, typename Node, typename Ref>
void TwineBackedPool<Derived, Node, Ref>::clone_from(const Derived &other) {
	log_assert(twines.shares_index_space_with(other.twines));
	HashConsPool<Derived, Node, Ref>::operator=(static_cast<const HashConsPool<Derived, Node, Ref> &>(other));
}

template<typename Derived, typename Node, typename Ref>
size_t TwineBackedPool<Derived, Node, Ref>::gc(const Marks &live) {
	return HashConsPool<Derived, Node, Ref>::gc(live);
}

template<typename Derived, typename Node, typename Ref>
Ref TwineBackedPool<Derived, Node, Ref>::stamp(Ref ref) const {
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	if (ref != Ref())
		ref.serial = (uint32_t) twines.serial();
#endif
	return ref;
}

template<typename Derived, typename Node, typename Ref>
void TwineBackedPool<Derived, Node, Ref>::check_owned([[maybe_unused]] Ref ref) const {
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	log_assert(ref.serial == 0 || ref.serial == twines.serial());
	log_assert(this->is_live(ref));
#endif
}

template<typename Derived, typename Node, typename Ref>
struct NodeEq {
	const TwineBackedPool<Derived, Node, Ref> &pool;
	const Node &node;
	bool operator()(Ref ref) const { return pool[ref] == node; }
};

template<typename Derived, typename Node, typename Ref>
Ref TwineBackedPool<Derived, Node, Ref>::find_node(const Node &node) const {
	return stamp(this->find_hashed(Derived::hash_node(node), NodeEq<Derived, Node, Ref>{*this, node}));
}

template<typename Derived, typename Node, typename Ref>
Ref TwineBackedPool<Derived, Node, Ref>::intern_node(Node node) {
	Ref found = find_node(node);
	if (found != Ref())
		return found;
	return stamp(this->add_inner(std::move(node)));
}

YOSYS_NAMESPACE_END

#endif
