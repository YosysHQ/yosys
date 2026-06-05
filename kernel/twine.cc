#include "kernel/twine.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

Twine::Id TwinePool::alloc_slot_(Twine &&node)
{
	if (!free_list_.empty()) {
		// Pop the SMALLEST free id (not the most recent), so reuse order
		// matches the original allocation order when an entire pool gets
		// freed and rebuilt. That makes write_rtlil emit byte-identical
		// "@N" refs across design -push;-pop and similar wholesale-clone
		// cycles, even though the in-memory pool got renumbered through
		// the free list.
		auto it = std::min_element(free_list_.begin(), free_list_.end());
		Twine::Id id = *it;
		free_list_.erase(it);
		nodes_[id] = std::move(node);
		refcount_[id] = 0;
		return id;
	}
	Twine::Id id = static_cast<Twine::Id>(nodes_.size());
	nodes_.push_back(std::move(node));
	refcount_.push_back(0);
	return id;
}

Twine::Id TwinePool::intern(std::string_view leaf)
{
	if (leaf.empty())
		return Twine::Null;
	std::string key{leaf};
	if (auto it = leaf_index_.find(key); it != leaf_index_.end()) {
		retain(it->second);
		return it->second;
	}
	Twine::Id id = alloc_slot_(Twine{std::move(key)});
	leaf_index_[std::get<std::string>(nodes_[id].data)] = id;
	refcount_[id] = 1;
	return id;
}

Twine::Id TwinePool::intern_suffix(Twine::Id parent, std::string_view tail)
{
	if (parent == Twine::Null)
		return intern(tail);
	log_assert(parent < nodes_.size() && !nodes_[parent].is_dead());
	log_assert(nodes_[parent].is_flat() && "Suffix parent must be a flat node (Leaf or Suffix)");
	if (tail.empty()) {
		// No tail means "the same string as parent". Hand back a fresh
		// owning ref on parent — semantically equivalent to a degenerate
		// suffix node, but we avoid allocating a slot for it.
		retain(parent);
		return parent;
	}

	std::pair<Twine::Id, std::string> key{parent, std::string{tail}};
	if (auto it = suffix_index_.find(key); it != suffix_index_.end()) {
		retain(it->second);
		return it->second;
	}

	// Internal child ref: the suffix node owns one ref on its parent.
	retain(parent);
	Twine::Id id = alloc_slot_(Twine{Twine::Suffix{parent, std::string{tail}}});
	const auto &stored = std::get<Twine::Suffix>(nodes_[id].data);
	suffix_index_[std::make_pair(stored.parent, stored.tail)] = id;
	refcount_[id] = 1;
	return id;
}

Twine::Id TwinePool::concat(std::span<const Twine::Id> parts)
{
	// Flat invariant: a Concat node only ever holds flat children (Leaf
	// or Suffix), never another Concat. Splice in concats' children
	// directly so identical sets map to byte-equal child vectors
	// regardless of how callers nested concats.
	std::vector<Twine::Id> children;
	children.reserve(parts.size());
	pool<Twine::Id> seen;
	auto push_flat = [&](Twine::Id flat_id) {
		if (seen.insert(flat_id).second)
			children.push_back(flat_id);
	};
	for (Twine::Id p : parts) {
		if (p == Twine::Null)
			continue;
		log_assert(p < nodes_.size() && !nodes_[p].is_dead());
		const Twine &n = nodes_[p];
		if (n.is_flat()) {
			push_flat(p);
		} else {
			for (Twine::Id grandchild : n.children())
				push_flat(grandchild);
		}
	}

	if (children.empty())
		return Twine::Null;
	if (children.size() == 1) {
		retain(children.front());
		return children.front();
	}

	if (auto it = concat_index_.find(children); it != concat_index_.end()) {
		retain(it->second);
		return it->second;
	}

	// Internal child refs: the concat node owns one ref on each child.
	for (Twine::Id c : children)
		retain(c);
	Twine::Id id = alloc_slot_(Twine{std::move(children)});
	concat_index_[std::get<std::vector<Twine::Id>>(nodes_[id].data)] = id;
	refcount_[id] = 1;
	return id;
}

Twine::Id TwinePool::concat(Twine::Id a, Twine::Id b)
{
	std::array<Twine::Id, 2> pair{a, b};
	return concat(std::span<const Twine::Id>{pair});
}

void TwinePool::retain(Twine::Id id)
{
	if (id == Twine::Null)
		return;
	log_assert(id < nodes_.size() && !nodes_[id].is_dead());
	refcount_[id]++;
}

void TwinePool::release(Twine::Id id)
{
	if (id == Twine::Null)
		return;
	log_assert(id < nodes_.size() && !nodes_[id].is_dead());
	log_assert(refcount_[id] > 0);
	if (--refcount_[id] == 0)
		destroy_slot_(id);
}

uint32_t TwinePool::refcount(Twine::Id id) const
{
	if (id == Twine::Null)
		return 0;
	return refcount_.at(id);
}

bool TwinePool::is_alive(Twine::Id id) const
{
	if (id == Twine::Null)
		return false;
	return id < nodes_.size() && !nodes_[id].is_dead();
}

void TwinePool::destroy_slot_(Twine::Id id)
{
	Twine &n = nodes_[id];
	if (n.is_leaf()) {
		leaf_index_.erase(n.leaf());
	} else if (n.is_concat()) {
		// Release internal child refs. Capture by move so iteration is
		// stable across child destroy_slot_ side effects.
		std::vector<Twine::Id> children = std::move(std::get<std::vector<Twine::Id>>(n.data));
		concat_index_.erase(children);
		n.data = std::monostate{};
		free_list_.push_back(id);
		for (Twine::Id c : children)
			release(c);
		return;
	} else if (n.is_suffix()) {
		// Capture parent by move and release after dropping the slot,
		// since releasing may recursively destroy the parent and we
		// want this slot's tombstone to be visible by then.
		Twine::Suffix s = std::move(std::get<Twine::Suffix>(n.data));
		suffix_index_.erase(std::make_pair(s.parent, s.tail));
		n.data = std::monostate{};
		free_list_.push_back(id);
		release(s.parent);
		return;
	}
	n.data = std::monostate{};
	free_list_.push_back(id);
}

void TwinePool::collect_leaves(Twine::Id id, pool<std::string> &out) const
{
	if (id == Twine::Null)
		return;
	const Twine &n = nodes_.at(id);
	if (n.is_dead())
		return;
	if (n.is_leaf()) {
		out.insert(n.leaf());
		return;
	}
	if (n.is_suffix()) {
		// A suffix is semantically a single flat string. Materialize it
		// and insert into the set just like a leaf.
		out.insert(flat_string_(id));
		return;
	}
	for (Twine::Id c : n.children())
		collect_leaves(c, out);
}

std::string TwinePool::flat_string_(Twine::Id id) const
{
	// Walk the parent chain iteratively to avoid recursion depth concerns
	// on deep suffix trees. Collect tails (and the root leaf) then stitch
	// in root-to-tail order.
	log_assert(id != Twine::Null);
	std::vector<std::string_view> parts;
	while (true) {
		const Twine &n = nodes_.at(id);
		if (n.is_leaf()) {
			parts.push_back(n.leaf());
			break;
		}
		log_assert(n.is_suffix());
		parts.push_back(n.suffix().tail);
		id = n.suffix().parent;
	}
	size_t total = 0;
	for (auto p : parts)
		total += p.size();
	std::string out;
	out.reserve(total);
	for (auto it = parts.rbegin(); it != parts.rend(); ++it)
		out.append(*it);
	return out;
}

std::string TwinePool::flatten(Twine::Id id, char sep) const
{
	if (id == Twine::Null)
		return {};
	pool<std::string> leaves;
	collect_leaves(id, leaves);
	std::string out;
	for (const auto &s : leaves) {
		if (s.empty())
			continue;
		if (!out.empty())
			out += sep;
		out += s;
	}
	return out;
}

std::string TwinePool::format_ref(Twine::Id id)
{
	if (id == Twine::Null)
		return {};
	return "@" + std::to_string(id);
}

Twine::Id TwinePool::parse_ref(std::string_view s)
{
	if (s.size() < 2 || s[0] != '@')
		return Twine::Null;
	uint64_t v = 0;
	for (size_t i = 1; i < s.size(); i++) {
		char c = s[i];
		if (c < '0' || c > '9')
			return Twine::Null;
		v = v * 10 + static_cast<uint64_t>(c - '0');
		if (v >= std::numeric_limits<Twine::Id>::max())
			return Twine::Null;
	}
	return static_cast<Twine::Id>(v);
}

void TwinePool::dump(const char *banner) const
{
	if (banner)
		log("%s (%zu live nodes: %zu leaves, %zu suffixes, %zu concats, %zu free slots)\n",
				banner, nodes_.size() - free_list_.size(),
				leaf_index_.size(), suffix_index_.size(),
				concat_index_.size(), free_list_.size());
	for_each_live([&](Twine::Id id, const Twine &n) {
		if (n.is_leaf()) {
			log("  @%u leaf rc=%u %s\n", id, refcount_[id], n.leaf().c_str());
		} else if (n.is_suffix()) {
			log("  @%u suffix rc=%u @%u + %s\n", id, refcount_[id],
					n.suffix().parent, n.suffix().tail.c_str());
		} else {
			std::string children;
			for (Twine::Id c : n.children()) {
				if (!children.empty())
					children += ", ";
				children += "@" + std::to_string(c);
			}
			log("  @%u concat rc=%u [%s]\n", id, refcount_[id], children.c_str());
		}
	});
}

dict<Twine::Id, Twine::Id> TwinePool::gc(const pool<Twine::Id> &live)
{
	// Closure: mark every node reachable from `live`. Concat children
	// (Leaf or Suffix) and Suffix parents (Leaf or Suffix) are both
	// followed. With Suffix nodes chains can be more than one step deep,
	// so use a worklist rather than a single BFS step.
	pool<Twine::Id> reachable;
	std::vector<Twine::Id> work;
	for (Twine::Id id : live) {
		if (id == Twine::Null || id >= nodes_.size() || nodes_[id].is_dead())
			continue;
		if (reachable.insert(id).second)
			work.push_back(id);
	}
	while (!work.empty()) {
		Twine::Id id = work.back();
		work.pop_back();
		const Twine &n = nodes_[id];
		if (n.is_concat()) {
			for (Twine::Id c : n.children())
				if (reachable.insert(c).second)
					work.push_back(c);
		} else if (n.is_suffix()) {
			Twine::Id p = n.suffix().parent;
			if (reachable.insert(p).second)
				work.push_back(p);
		}
	}

	// Rebuild the pool from scratch. Process flats (Leaf, then Suffix)
	// before Concats so concat-child lookups can resolve, and process
	// suffixes parent-before-child via a recursive helper that memoizes
	// into `remap`.
	std::vector<Twine> new_nodes;
	std::vector<uint32_t> new_refcount;
	dict<std::string, Twine::Id> new_leaf_index;
	dict<std::vector<Twine::Id>, Twine::Id> new_concat_index;
	dict<std::pair<Twine::Id, std::string>, Twine::Id> new_suffix_index;
	dict<Twine::Id, Twine::Id> remap;

	auto intern_leaf = [&](const std::string &text) -> Twine::Id {
		if (auto it = new_leaf_index.find(text); it != new_leaf_index.end())
			return it->second;
		Twine::Id id = static_cast<Twine::Id>(new_nodes.size());
		new_nodes.push_back(Twine{text});
		new_refcount.push_back(0);
		new_leaf_index[std::get<std::string>(new_nodes.back().data)] = id;
		return id;
	};

	for (Twine::Id old_id : reachable) {
		const Twine &n = nodes_[old_id];
		if (n.is_leaf())
			remap[old_id] = intern_leaf(n.leaf());
	}

	std::function<Twine::Id(Twine::Id)> remap_flat = [&](Twine::Id old_id) -> Twine::Id {
		if (auto it = remap.find(old_id); it != remap.end())
			return it->second;
		const Twine &n = nodes_[old_id];
		log_assert(n.is_suffix());
		Twine::Id new_parent = remap_flat(n.suffix().parent);
		std::pair<Twine::Id, std::string> key{new_parent, n.suffix().tail};
		if (auto sit = new_suffix_index.find(key); sit != new_suffix_index.end()) {
			remap[old_id] = sit->second;
			return sit->second;
		}
		Twine::Id new_id = static_cast<Twine::Id>(new_nodes.size());
		new_nodes.push_back(Twine{Twine::Suffix{new_parent, n.suffix().tail}});
		new_refcount.push_back(0);
		const auto &stored = std::get<Twine::Suffix>(new_nodes.back().data);
		new_suffix_index[std::make_pair(stored.parent, stored.tail)] = new_id;
		remap[old_id] = new_id;
		return new_id;
	};

	for (Twine::Id old_id : reachable) {
		const Twine &n = nodes_[old_id];
		if (n.is_suffix() && remap.find(old_id) == remap.end())
			remap_flat(old_id);
	}

	for (Twine::Id old_id : reachable) {
		const Twine &n = nodes_[old_id];
		if (!n.is_concat())
			continue;
		std::vector<Twine::Id> children;
		children.reserve(n.children().size());
		for (Twine::Id c : n.children())
			children.push_back(remap.at(c));
		if (auto it = new_concat_index.find(children); it != new_concat_index.end()) {
			remap[old_id] = it->second;
		} else {
			Twine::Id new_id = static_cast<Twine::Id>(new_nodes.size());
			new_nodes.push_back(Twine{std::move(children)});
			new_refcount.push_back(0);
			new_concat_index[std::get<std::vector<Twine::Id>>(new_nodes.back().data)] = new_id;
			remap[old_id] = new_id;
		}
	}

	// Refcounts in the rebuilt pool: every external "live" id passed in by
	// the caller corresponds to one external owner reference; concats
	// hold one ref per stored child; suffixes hold one ref on their parent.
	for (Twine::Id old_id : live) {
		auto it = remap.find(old_id);
		if (it != remap.end())
			new_refcount[it->second]++;
	}
	for (size_t i = 0; i < new_nodes.size(); i++) {
		if (new_nodes[i].is_concat()) {
			for (Twine::Id c : new_nodes[i].children())
				new_refcount[c]++;
		} else if (new_nodes[i].is_suffix()) {
			new_refcount[new_nodes[i].suffix().parent]++;
		}
	}

	nodes_ = std::move(new_nodes);
	refcount_ = std::move(new_refcount);
	free_list_.clear();
	leaf_index_ = std::move(new_leaf_index);
	concat_index_ = std::move(new_concat_index);
	suffix_index_ = std::move(new_suffix_index);
	return remap;
}

Twine::Id TwinePool::copy_from(const TwinePool &src, Twine::Id src_id)
{
	if (src_id == Twine::Null)
		return Twine::Null;
	log_assert(src_id < src.nodes_.size() && !src.nodes_[src_id].is_dead());
	const Twine &n = src.nodes_[src_id];
	if (n.is_leaf())
		return intern(n.leaf());
	if (n.is_suffix()) {
		Twine::Id new_parent = copy_from(src, n.suffix().parent);
		Twine::Id result = intern_suffix(new_parent, n.suffix().tail);
		// intern_suffix retained the parent internally; the caller-side
		// +1 ref from copy_from(parent) is surplus.
		release(new_parent);
		return result;
	}
	std::vector<Twine::Id> children;
	children.reserve(n.children().size());
	for (Twine::Id c : n.children())
		children.push_back(copy_from(src, c));
	Twine::Id result = concat(std::span<const Twine::Id>{children});
	// concat retained each child internally; the caller-side +1 refs from
	// copy_from(child) are surplus.
	for (Twine::Id c : children)
		release(c);
	return result;
}

YOSYS_NAMESPACE_END
