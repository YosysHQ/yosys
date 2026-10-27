#include "kernel/metapool.h"
#include "kernel/hashcons_impl.h"
#include "kernel/log.h"

#include <algorithm>

YOSYS_NAMESPACE_BEGIN

template struct HashConsPool<MetaPool, MetaBlock, MetaRef>;

struct MetaEq {
	const MetaPool &pool;
	const MetaBlock &node;
	bool operator()(MetaRef ref) const { return pool[ref] == node; }
};

static IdString canonical(IdString ref) {
	return ref.untag().stamped(0);
}

static void canonicalize(std::vector<IdString> &members) {
	for (IdString &member : members)
		member = canonical(member);
	std::sort(members.begin(), members.end());
	members.erase(std::unique(members.begin(), members.end()), members.end());
}

static void insert_all(std::vector<IdString> &into, const std::vector<IdString> &from) {
	into.insert(into.end(), from.begin(), from.end());
}

void MetaPool::clone_from(const MetaPool &other) {
	log_assert(twines.shares_index_space_with(other.twines));
	HashConsPool::operator=(static_cast<const HashConsPool &>(other));
}

void MetaPool::clear() {
	backing.clear();
	free_list.clear();
	std::fill(table.begin(), table.end(), MetaRef());
	index_entries = 0;
}

uint64_t MetaPool::hash_node(const MetaBlock &n) {
	Hasher h;
	h.eat(n.scope);
	h.eat(n.name);
	for (IdString member : n.names)
		h.eat(member);
	h.eat(IdString());
	for (IdString member : n.scopes)
		h.eat(member);
	return h.yield();
}

IdString MetaPool::root() {
	return twines.add(TwineSpec{TwineSpec::Leaf{std::string()}});
}

IdString MetaPool::extend(IdString scope, std::string_view name) {
	if (scope == root())
		return twines.add(scope, name);
	return twines.add(scope, " " + std::string(name));
}

MetaRef MetaPool::intern(MetaBlock block) {
	block.scope = canonical(block.scope);
	block.name = canonical(block.name);
	canonicalize(block.names);
	canonicalize(block.scopes);
	if (!block.name.empty())
		std::erase(block.names, block.name);
	else if (!block.scope.empty())
		std::erase(block.scopes, block.scope);
	if (block.is_dead())
		return MetaRef::Null;
	uint32_t tag = !block.name.empty() ? MetaRef::HDLNAME_BIT
		: !block.scope.empty() ? MetaRef::SCOPENAME_BIT : 0;
	MetaRef found = find_hashed(hash_node(block), MetaEq{*this, block});
	if (found == MetaRef::Null)
		found = add_inner(std::move(block));
	return MetaRef(found.raw() | tag);
}

std::string MetaPool::hdlname(MetaRef ref) const {
	if (!ref.has_hdlname())
		return {};
	return twines.str((*this)[ref].name);
}

std::string MetaPool::scopename(MetaRef ref) const {
	if (!ref.has_scopename())
		return {};
	return twines.str((*this)[ref].scope);
}

MetaRef MetaPool::with_hdlname(MetaRef ref, std::string_view path) {
	MetaBlock block = ref == MetaRef::Null ? MetaBlock{} : (*this)[ref];
	std::vector<std::string> elems = split_tokens(std::string(path), " ");
	if (elems.empty()) {
		if (!block.name.empty())
			block.scope = block.name = IdString();
		return intern(std::move(block));
	}
	IdString scope = root();
	for (size_t i = 0; i + 1 < elems.size(); i++)
		scope = extend(scope, elems[i]);
	block.scope = scope;
	block.name = extend(scope, elems.back());
	return intern(std::move(block));
}

MetaRef MetaPool::with_scopename(MetaRef ref, std::string_view path) {
	MetaBlock block = ref == MetaRef::Null ? MetaBlock{} : (*this)[ref];
	if (!block.name.empty())
		return ref;
	std::vector<std::string> elems = split_tokens(std::string(path), " ");
	IdString scope;
	if (!elems.empty()) {
		scope = root();
		for (auto &elem : elems)
			scope = extend(scope, elem);
	}
	block.scope = scope;
	return intern(std::move(block));
}

MetaRef MetaPool::without_name(MetaRef ref) {
	if (!ref.has_hdlname())
		return ref;
	MetaBlock block = (*this)[ref];
	block.name = IdString();
	if (block.scope == root())
		block.scope = IdString();
	return intern(std::move(block));
}

MetaRef MetaPool::transfer(MetaRef target, MetaRef source) {
	if (target == MetaRef::Null || target == source)
		return source;
	MetaBlock block = (*this)[target];
	if (!block.name.empty())
		block.names.push_back(block.name);
	else if (!block.scope.empty())
		block.scopes.push_back(block.scope);
	block.scope = block.name = IdString();
	if (source != MetaRef::Null) {
		const MetaBlock &from = (*this)[source];
		block.scope = from.scope;
		block.name = from.name;
		insert_all(block.names, from.names);
		insert_all(block.scopes, from.scopes);
	}
	return intern(std::move(block));
}

MetaRef MetaPool::absorb(MetaRef target, MetaRef source) {
	if (source == MetaRef::Null || target == source)
		return target;
	MetaBlock block = target == MetaRef::Null ? MetaBlock{} : (*this)[target];
	const MetaBlock &from = (*this)[source];
	if (!from.name.empty())
		block.names.push_back(from.name);
	else if (!from.scope.empty())
		block.scopes.push_back(from.scope);
	insert_all(block.names, from.names);
	insert_all(block.scopes, from.scopes);
	return intern(std::move(block));
}

MetaRef MetaPool::copy_from(const MetaPool &other, MetaRef ref) {
	if (ref == MetaRef::Null)
		return ref;
	const MetaBlock &from = other[ref];
	MetaBlock block;
	block.scope = twines.copy_from(other.twines, from.scope);
	block.name = twines.copy_from(other.twines, from.name);
	for (IdString member : from.names)
		block.names.push_back(twines.copy_from(other.twines, member));
	for (IdString member : from.scopes)
		block.scopes.push_back(twines.copy_from(other.twines, member));
	return intern(std::move(block));
}

void MetaPool::root_members(const std::vector<MetaRef> &live_metas, pool<IdString> &live_twines) const {
	for (MetaRef ref : live_metas) {
		const MetaBlock &block = (*this)[ref];
		if (!block.scope.empty())
			live_twines.insert(block.scope);
		if (!block.name.empty())
			live_twines.insert(block.name);
		for (IdString member : block.names)
			live_twines.insert(member);
		for (IdString member : block.scopes)
			live_twines.insert(member);
	}
}

size_t MetaPool::gc(const std::vector<MetaRef> &live_metas) {
	return HashConsPool::gc(live_metas);
}

void MetaPool::dump(MetaRef ref, std::ostream &os) const {
	const MetaBlock &block = (*this)[ref];
	os << "Meta[scope @" << block.scope.raw() << ", name @" << block.name.raw();
	for (IdString member : block.names)
		os << ", absorbed @" << member.raw();
	for (IdString member : block.scopes)
		os << ", absorbed scope @" << member.raw();
	os << "]";
}

YOSYS_NAMESPACE_END
