#include "kernel/twine.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

std::vector<Twine> TwinePool::globals_;

TwineRef twine_populate(std::string name) {
	// Globals store content only: drop the prepended '\'. Publicity lives
	// in TWINE_PUBLIC_BIT on the TW:: handle, not in the stored string.
	log_assert(name[0] == '\\');
	name = name.substr(1);
	TwinePool::globals_.push_back(Twine{std::move(name)});
	return TwinePool::globals_.size() - 1;
}
void twine_prepopulate() {
	TwinePool::globals_.reserve(STATIC_TWINE_END);
#define X(_id) twine_populate("\\" #_id);
#include "kernel/constids.inc"
#undef X
}

// enum : short
// {
//     STATIC_ID_BEGIN = 0,
// #define X(N) IDX_##N,
// #include "kernel/constids.inc"
// #undef X
//     STATIC_ID_END
// };

// #define X(N) const TW TW::N{IDX_##N};
// #include "kernel/constids.inc"
// #undef X

// struct TwinePool {
// 	colony<Twine>
// };

// TwinePool::TwinePool()
//     : index_(0, LeafHash{this}, LeafEq{this})
// {}

// TwinePool::TwinePool(const TwinePool &other)
//     : nodes_(other.nodes_)
//     , refcount_(other.refcount_)
//     , free_list_(other.free_list_)
//     , leaf_index_(0, LeafHash{this}, LeafEq{this})
//     , suffix_index_(0, SuffixHash{this}, SuffixEq{this})
//     , concat_index_(0, ConcatHash{this}, ConcatEq{this})
// {
// 	rebuild_indexes_();
// }

// TwinePool &TwinePool::operator=(const TwinePool &other)
// {
// 	if (this == &other)
// 		return *this;
// 	nodes_ = other.nodes_;
// 	refcount_ = other.refcount_;
// 	free_list_ = other.free_list_;
// 	// Re-create the index sets with functors pointing to *this,
// 	// then rebuild their contents from the (now-copied) nodes_.
// 	leaf_index_ = std::unordered_set<TwineRef, LeafHash, LeafEq>(
// 		0, LeafHash{this}, LeafEq{this});
// 	suffix_index_ = std::unordered_set<TwineRef, SuffixHash, SuffixEq>(
// 		0, SuffixHash{this}, SuffixEq{this});
// 	concat_index_ = std::unordered_set<TwineRef, ConcatHash, ConcatEq>(
// 		0, ConcatHash{this}, ConcatEq{this});
// 	rebuild_indexes_();
// 	return *this;
// }

// void TwinePool::rebuild_indexes_()
// {
// 	for (auto& n : nodes_) {
// 		if (n.is_dead()) continue;
// 		if (n.is_leaf())   leaf_index_.insert(&n);
// 		else if (n.is_suffix()) suffix_index_.insert(&n);
// 		else if (n.is_concat()) concat_index_.insert(&n);
// 	}
// }

// TwineRef TwinePool::alloc_slot_(Twine &&node)
// {
// 	if (!free_list_.empty()) {
// 		// Pop the SMALLEST free id (not the most recent), so reuse order
// 		// matches the original allocation order when an entire pool gets
// 		// freed and rebuilt. That makes write_rtlil emit byte-identical
// 		// "@N" refs across design -push;-pop and similar wholesale-clone
// 		// cycles, even though the in-memory pool got renumbered through
// 		// the free list.
// 		// TODO nevermind, inefficient, solve in RTLIL frontend and backend
// 		// auto it = std::min_element(free_list_.begin(), free_list_.end());
// 		// TwineRef id = *it;
// 		// free_list_.erase(it);
// 		Twine* id = free_list_.back();
// 		*id = std::move(node);
// 		// size_t idx = id - &nodes_.front();
// 		// log_assert(idx > 0 && idx < refcount_.size());
// 		// refcount_[idx] = 0;
// 		refcount(id) = 0;
// 		return id;
// 	}
// 	// TwineRef id = static_cast<TwineRef>(nodes_.size());
// 	nodes_.push_back(std::move(node));
// 	Twine* id = &nodes_.back();
// 	refcount_.push_back(0);
// 	return id;
// }

// TwineRef TwinePool::intern(std::string_view str)
// {
// 	if (str.empty())
// 		return Twine::Null;
// 	// Transparent find: probes with string_view, no string allocation.
// 	// TODO why are they split like this? Is this called on a hot path somewhere?
// 	if (auto it = leaf_index_.find(str); it != leaf_index_.end()) {
// 		retain(*it);
// 		return *it;
// 	}
// 	if (auto it = suffix_index_.find(str); it != suffix_index_.end()) {
// 		retain(*it);
// 		return *it;
// 	}
// 	if (auto it = concat_index_.find(str); it != concat_index_.end()) {
// 		retain(*it);
// 		return *it;
// 	}
// 	TwineRef id = alloc_slot_(Twine{std::string{str}});
// 	leaf_index_.insert(id);

// 	// size_t idx = id - &nodes_.front();
// 	// log_assert(idx > 0 && idx < refcount_.size());
// 	// refcount_[idx] = 1;
// 	refcount(id) = 1;
// 	return id;
// }

// Twine* TwinePool::intern_suffix(Twine* parent, std::string_view tail)
// {
// 	if (parent == Twine::Null)
// 		return intern(tail);
// 	log_assert(parent > &nodes_.front() && parent <= &nodes_.back() && !parent->is_dead());
// 	log_assert(parent->is_flat() && "Suffix parent must be a flat node (Leaf or Suffix)");
// 	if (tail.empty()) {
// 		// No tail means "the same string as parent". Hand back a fresh
// 		// owning ref on parent — semantically equivalent to a degenerate
// 		// suffix node, but we avoid allocating a slot for it.
// 		retain(parent);
// 		return parent;
// 	}

// 	// Transparent find: probes with (parent, string_view), no allocation.
// 	SuffixKey key{parent, tail};
// 	if (auto it = suffix_index_.find(key); it != suffix_index_.end()) {
// 		retain(*it);
// 		return *it;
// 	}

// 	// Internal child ref: the suffix node owns one ref on its parent.
// 	retain(parent);
// 	TwineRef id = alloc_slot_(Twine{Twine::Suffix{parent, std::string{tail}}});
// 	suffix_index_.insert(id);
// 	refcount(id) = 1;
// 	return id;
// }

// TwineRef TwinePool::concat(std::span<const TwineRef> parts)
// {
// 	// Flat invariant: a Concat node only ever holds flat children (Leaf
// 	// or Suffix), never another Concat. Splice in concats' children
// 	// directly so identical sets map to byte-equal child vectors
// 	// regardless of how callers nested concats.
// 	std::vector<TwineRef> children;
// 	children.reserve(parts.size());
// 	pool<TwineRef> seen;
// 	auto push_flat = [&](TwineRef flat_id) {
// 		if (seen.insert(flat_id).second)
// 			children.push_back(flat_id);
// 	};
// 	for (TwineRef p : parts) {
// 		if (p == Twine::Null)
// 			continue;
// 		// log_assert(p < nodes_.size() && !nodes_[p].is_dead());
// 		const Twine &n = *p;
// 		if (n.is_flat()) {
// 			push_flat(p);
// 		} else {
// 			for (TwineRef grandchild : n.children())
// 				push_flat(grandchild);
// 		}
// 	}

// 	if (children.empty())
// 		return Twine::Null;
// 	if (children.size() == 1) {
// 		retain(children.front());
// 		return children.front();
// 	}

// 	// Transparent find: probes with span, no vector allocation.
// 	std::span<const TwineRef> child_span{children};
// 	if (auto it = concat_index_.find(child_span); it != concat_index_.end()) {
// 		retain(*it);
// 		return *it;
// 	}

// 	// Internal child refs: the concat node owns one ref on each child.
// 	for (TwineRef c : children)
// 		retain(c);
// 	TwineRef id = alloc_slot_(Twine{std::move(children)});
// 	concat_index_.insert(id);
// 	refcount(id) = 1;
// 	return id;
// }

// TwineRef TwinePool::concat(TwineRef a, TwineRef b)
// {
// 	std::array<TwineRef, 2> pair{a, b};
// 	return concat(std::span<const TwineRef>{pair});
// }

// void TwinePool::retain(TwineRef id)
// {
// 	if (id == Twine::Null)
// 		return;
// 	refcount(id)++;
// }

// void TwinePool::release(TwineRef id)
// {
// 	if (id == Twine::Null)
// 		return;
// 	// log_assert(id < nodes_.size() && !nodes_[id].is_dead());
// 	log_assert(refcount(id) > 0);
// 	if (--refcount(id) == 0)
// 		destroy_slot_(id);
// }

// size_t TwinePool::index(TwineRef p) const
// {
// 	return p - &nodes_.front();
// }

// uint32_t& TwinePool::refcount(TwineRef id)
// {
// 	log_assert(id != Twine::Null);
// 	size_t idx = index(id);
// 	log_assert(idx > 0 && idx < refcount_.size());
// 	return refcount_[idx];
// }

// uint32_t TwinePool::refcount(TwineRef id) const
// {
// 	log_assert(id != Twine::Null);
// 	size_t idx = id - &nodes_.front();
// 	log_assert(idx > 0 && idx < refcount_.size());
// 	return refcount_[idx];
// }

// bool TwinePool::is_alive(TwineRef id) const
// {
// 	if (id == Twine::Null)
// 		return false;
// 	return id >= &nodes_.front() && id <= &nodes_.back() && !id->is_dead();
// }

// void TwinePool::destroy_slot_(TwineRef id)
// {
// 	Twine &n = *id;
// 	if (n.is_leaf()) {
// 		// Erase by id: functor reads nodes_[id].leaf() before we tombstone.
// 		leaf_index_.erase(id);
// 	} else if (n.is_concat()) {
// 		// Erase by id first (while data is still readable), then capture
// 		// children by move so iteration is stable across recursive release.
// 		concat_index_.erase(id);
// 		std::vector<TwineRef> children =
// 			std::move(std::get<std::vector<TwineRef>>(n.data));
// 		n.data = std::monostate{};
// 		free_list_.push_back(id);
// 		for (TwineRef c : children)
// 			release(c);
// 		return;
// 	} else if (n.is_suffix()) {
// 		// Same pattern: erase first, then move data for deferred release.
// 		suffix_index_.erase(id);
// 		Twine::Suffix s = std::move(std::get<Twine::Suffix>(n.data));
// 		n.data = std::monostate{};
// 		free_list_.push_back(id);
// 		release(s.parent);
// 		return;
// 	}
// 	n.data = std::monostate{};
// 	free_list_.push_back(id);
// }

// TwineRef TwinePool::lookup(std::string_view sv) const
// {
// 	if (sv.empty())
// 		return Twine::Null;
// 	auto it = leaf_index_.find(sv);
// 	return (it != leaf_index_.end()) ? *it : Twine::Null;
// }

// char TwinePool::first_char(TwineRef id) const
// {
// 	log_assert(id != Twine::Null && id > &nodes_.front() && id <= &nodes_.back() && !id->is_dead());
// 	// Walk suffix parents to reach the root leaf, then return its first char.
// 	while (id->is_suffix())
// 		id = id->suffix().parent;
// 	const std::string &s = id->leaf();
// 	// TODO seems wrong for concate
// 	return s.empty() ? '\0' : s.front();
// }

// void TwinePool::collect_leaves(TwineRef id, pool<std::string> &out) const
// {
// 	if (id == Twine::Null)
// 		return;
// 	const Twine &n = *id;
// 	if (n.is_dead())
// 		return;
// 	if (n.is_leaf()) {
// 		out.insert(n.leaf());
// 		return;
// 	}
// 	if (n.is_suffix()) {
// 		// A suffix is semantically a single flat string. Materialize it
// 		// and insert into the set just like a leaf.
// 		out.insert(flat_string_(id));
// 		return;
// 	}
// 	for (TwineRef c : n.children())
// 		collect_leaves(c, out);
// }

// std::string TwinePool::flat_string_(TwineRef id) const
// {
// 	// Walk the parent chain iteratively to avoid recursion depth concerns
// 	// on deep suffix trees. Collect tails (and the root leaf) then stitch
// 	// in root-to-tail order.
// 	log_assert(id != Twine::Null);
// 	std::vector<std::string_view> parts;
// 	while (true) {
// 		const Twine &n = *id;
// 		if (n.is_leaf()) {
// 			parts.push_back(n.leaf());
// 			break;
// 		}
// 		log_assert(n.is_suffix());
// 		parts.push_back(n.suffix().tail);
// 		id = n.suffix().parent;
// 	}
// 	size_t total = 0;
// 	for (auto p : parts)
// 		total += p.size();
// 	std::string out;
// 	out.reserve(total);
// 	for (auto it = parts.rbegin(); it != parts.rend(); ++it)
// 		out.append(*it);
// 	return out;
// }

// std::string TwinePool::flatten(TwineRef id, char sep) const
// {
// 	if (id == Twine::Null)
// 		return {};
// 	pool<std::string> leaves;
// 	collect_leaves(id, leaves);
// 	std::string out;
// 	for (const auto &s : leaves) {
// 		if (s.empty())
// 			continue;
// 		if (!out.empty())
// 			out += sep;
// 		out += s;
// 	}
// 	return out;
// }

// std::string TwinePool::format_ref(TwineRef id) const
// {
// 	if (id == Twine::Null)
// 		return {};
// 	size_t i = index(id);
// 	return "@" + std::to_string(i);
// }

// std::optional<size_t> TwinePool::parse_ref(std::string_view s)
// {
// 	if (s.size() < 2 || s[0] != '@')
// 		return std::nullopt;
// 	uint64_t v = 0;
// 	for (size_t i = 1; i < s.size(); i++) {
// 		char c = s[i];
// 		if (c < '0' || c > '9')
// 			return std::nullopt;
// 		v = v * 10 + static_cast<uint64_t>(c - '0');
// 	}
// 	return v;
// }
// TwineRef TwinePool::get_ref(std::string_view s)
// {
// 	if (auto idx = parse_ref(s))
// 		return &nodes_.front() + *idx;
// 	return nullptr;
// }

// void TwinePool::dump(const char *banner) const
// {
// 	if (banner)
// 		log("%s (%zu live nodes: %zu leaves, %zu suffixes, %zu concats, %zu free slots)\n",
// 				banner, nodes_.size() - free_list_.size(),
// 				leaf_index_.size(), suffix_index_.size(),
// 				concat_index_.size(), free_list_.size());
// 	for_each_live([&](TwineRef id, const Twine &n) {
// 		if (n.is_leaf()) {
// 			log("  @%u leaf rc=%u %s\n", id, refcount(id), n.leaf().c_str());
// 		} else if (n.is_suffix()) {
// 			log("  @%u suffix rc=%u @%u + %s\n", id, refcount(id),
// 					n.suffix().parent, n.suffix().tail.c_str());
// 		} else {
// 			std::string children;
// 			for (TwineRef c : n.children()) {
// 				if (!children.empty())
// 					children += ", ";
// 				children += format_ref(c);
// 			}
// 			log("  @%u concat rc=%u [%s]\n", id, refcount(id), children.c_str());
// 		}
// 	});
// }

// dict<TwineRef, TwineRef> TwinePool::gc(const pool<TwineRef> &live)
// {
// 	// Closure: mark every node reachable from `live`. Concat children
// 	// (Leaf or Suffix) and Suffix parents (Leaf or Suffix) are both
// 	// followed. With Suffix nodes chains can be more than one step deep,
// 	// so use a worklist rather than a single BFS step.
// 	pool<TwineRef> reachable;
// 	std::vector<TwineRef> work;
// 	for (TwineRef id : live) {
// 		if (!id || id->is_dead())
// 			continue;
// 		if (reachable.insert(id).second)
// 			work.push_back(id);
// 	}
// 	while (!work.empty()) {
// 		TwineRef id = work.back();
// 		work.pop_back();
// 		const Twine &n = *id;
// 		if (n.is_concat()) {
// 			for (TwineRef c : n.children())
// 				if (reachable.insert(c).second)
// 					work.push_back(c);
// 		} else if (n.is_suffix()) {
// 			TwineRef p = n.suffix().parent;
// 			if (reachable.insert(p).second)
// 				work.push_back(p);
// 		}
// 	}

// 	// Rebuild the pool from scratch using temporary storage; process flats
// 	// before concats so child lookups can resolve.
// 	std::vector<Twine> new_nodes;
// 	std::vector<uint32_t> new_refcount;
// 	dict<TwineRef, TwineRef> remap;

// 	// Helper: insert a leaf into new_nodes, dedup by string.
// 	// dict<std::string, TwineRef> new_leaf_map;
// 	for (TwineRef old_id : reachable) {
// 		const Twine &n = *old_id;
// 		if (n.is_leaf())
// 			remap[old_id] = intern(n.leaf());
// 	}

// 	std::function<TwineRef(TwineRef)> remap_flat = [&](TwineRef old_id) -> TwineRef {
// 		if (auto it = remap.find(old_id); it != remap.end())
// 			return it->second;
// 		const Twine &n = *old_id;
// 		log_assert(n.is_suffix());
// 		TwineRef new_parent = remap_flat(n.suffix().parent);
// 		// Dedup suffix nodes in the new pool.
// 		for (auto& i : new_nodes) {
// 			if (i.is_suffix()) {
// 				const auto &s = i.suffix();
// 				if (s.parent == new_parent && s.tail == n.suffix().tail) {
// 					remap[old_id] = &i;
// 					return &i;
// 				}
// 			}
// 		}
// 		// TwineRef new_id = static_cast<TwineRef>(new_nodes.size());
// 		new_nodes.push_back(Twine{Twine::Suffix{new_parent, n.suffix().tail}});
// 		TwineRef new_id = &new_nodes.back();
// 		new_refcount.push_back(0);
// 		remap[old_id] = new_id;
// 		return new_id;
// 	};

// 	for (TwineRef old_id : reachable) {
// 		const Twine &n = *old_id;
// 		if (n.is_suffix() && remap.find(old_id) == remap.end())
// 			remap_flat(old_id);
// 	}

// 	// Dedup concat nodes by child vector.
// 	dict<std::vector<TwineRef>, TwineRef> new_concat_map;
// 	for (TwineRef old_id : reachable) {
// 		const Twine &n = *old_id;
// 		if (!n.is_concat())
// 			continue;
// 		std::vector<TwineRef> children;
// 		children.reserve(n.children().size());
// 		for (TwineRef c : n.children())
// 			children.push_back(remap.at(c));
// 		if (auto it = new_concat_map.find(children); it != new_concat_map.end()) {
// 			remap[old_id] = it->second;
// 		} else {
// 			// TwineRef new_id = static_cast<TwineRef>(new_nodes.size());
// 			new_nodes.push_back(Twine{children});
// 			TwineRef new_id = &new_nodes.back();
// 			new_refcount.push_back(0);
// 			new_concat_map[std::get<std::vector<TwineRef>>(new_nodes.back().data)] = new_id;
// 			remap[old_id] = new_id;
// 		}
// 	}



// 	// Swap in the new storage and rebuild the intrusive indexes.
// 	nodes_ = std::move(new_nodes);
// 	refcount_ = std::move(new_refcount);

// 	// Refcounts in the rebuilt pool.
// 	for (TwineRef old_id : live) {
// 		auto it = remap.find(old_id);
// 		if (it != remap.end())
// 			refcount(it->second)++;
// 	}
// 	for (size_t i = 0; i < nodes_.size(); i++) {
// 		if (nodes_[i].is_concat()) {
// 			for (TwineRef c : nodes_[i].children())
// 				refcount(c)++;
// 		} else if (nodes_[i].is_suffix()) {
// 			refcount(nodes_[i].suffix().parent)++;
// 		}
// 	}

// 	free_list_.clear();
// 	leaf_index_ = std::unordered_set<TwineRef, LeafHash, LeafEq>(
// 		0, LeafHash{this}, LeafEq{this});
// 	suffix_index_ = std::unordered_set<TwineRef, SuffixHash, SuffixEq>(
// 		0, SuffixHash{this}, SuffixEq{this});
// 	concat_index_ = std::unordered_set<TwineRef, ConcatHash, ConcatEq>(
// 		0, ConcatHash{this}, ConcatEq{this});
// 	rebuild_indexes_();
// 	return remap;
// }

// TwineRef TwinePool::copy_from(const TwinePool &src, TwineRef src_id)
// {
// 	if (src_id == Twine::Null)
// 		return Twine::Null;
// 	// log_assert(src_id < src.nodes_.size() && !src.nodes_[src_id].is_dead());
// 	const Twine &n = *src_id;
// 	if (n.is_leaf())
// 		return intern(n.leaf());
// 	if (n.is_suffix()) {
// 		TwineRef new_parent = copy_from(src, n.suffix().parent);
// 		TwineRef result = intern_suffix(new_parent, n.suffix().tail);
// 		// intern_suffix retained the parent internally; the caller-side
// 		// +1 ref from copy_from(parent) is surplus.
// 		release(new_parent);
// 		return result;
// 	}
// 	std::vector<TwineRef> children;
// 	children.reserve(n.children().size());
// 	for (TwineRef c : n.children())
// 		children.push_back(copy_from(src, c));
// 	TwineRef result = concat(std::span<const TwineRef>{children});
// 	// concat retained each child internally; the caller-side +1 refs from
// 	// copy_from(child) are surplus.
// 	for (TwineRef c : children)
// 		release(c);
// 	return result;
// }

YOSYS_NAMESPACE_END
