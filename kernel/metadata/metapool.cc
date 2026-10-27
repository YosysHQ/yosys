#include "kernel/metadata/metapool.h"
#include "kernel/metadata/twineset_impl.h"

YOSYS_NAMESPACE_BEGIN

template struct HashConsPool<MetaPool, MetaBlock, MetaRef>;
template struct TwineBackedPool<MetaPool, MetaBlock, MetaRef>;
template struct HashConsPool<NameSetPool, TwineSet, NameSetRef>;
template struct TwineBackedPool<NameSetPool, TwineSet, NameSetRef>;
template struct TwineSetPool<NameSetPool, NameSetRef>;

static IdString canonical(IdString ref) {
	return ref.untag().stamped(0);
}

static void canonicalize(MetaBlock &block) {
	block.scope = canonical(block.scope);
	block.hdlname = canonical(block.hdlname);
	block.absorbed_hdlnames = block.absorbed_hdlnames.unstamped();
	block.absorbed_scopes = block.absorbed_scopes.unstamped();
}

uint64_t MetaPool::hash_node(const MetaBlock &n) {
	Hasher h;
	h.eat(n.scope);
	h.eat(n.hdlname);
	h.eat(n.absorbed_hdlnames.raw());
	h.eat(n.absorbed_scopes.raw());
	return h.yield();
}

void MetaPool::clone_from(const MetaPool &other) {
	TwineBackedPool::clone_from(other);
	sets_.clone_from(other.sets_);
}

void MetaPool::clear() {
	TwineBackedPool::clear();
	sets_.clear();
}

NameSetPool::Marks MetaPool::absorbed_sets(const Marks &live_metas) const {
	NameSetPool::Marks sets;
	for (MetaRef ref : live_metas) {
		const MetaBlock &block = (*this)[ref];
		if (block.absorbed_hdlnames != NameSetRef::Null)
			sets.insert(block.absorbed_hdlnames);
		if (block.absorbed_scopes != NameSetRef::Null)
			sets.insert(block.absorbed_scopes);
	}
	return sets;
}

size_t MetaPool::gc(const Marks &live_metas) {
	NameSetPool::Marks live_sets = absorbed_sets(live_metas);
	size_t erased = TwineBackedPool::gc(live_metas);
	return erased + sets_.gc(live_sets);
}

void MetaPool::absorb_identity(MetaBlock &into, const MetaBlock &from) {
	if (!from.hdlname.empty())
		into.absorbed_hdlnames = sets_.with_member(into.absorbed_hdlnames, from.hdlname);
	else if (!from.scope.empty())
		into.absorbed_scopes = sets_.with_member(into.absorbed_scopes, from.scope);
}

void MetaPool::absorb_sets(MetaBlock &into, const MetaBlock &from) {
	into.absorbed_hdlnames = sets_.merge(into.absorbed_hdlnames, from.absorbed_hdlnames);
	into.absorbed_scopes = sets_.merge(into.absorbed_scopes, from.absorbed_scopes);
}

IdString MetaPool::root() {
	return twines.add(TwineSpec{TwineSpec::Root{std::string()}});
}

IdString MetaPool::extend(IdString root, IdString path, std::string_view name) {
	if (path == root)
		return twines.add(path, name);
	return twines.add(path, " " + std::string(name));
}

IdString MetaPool::add_path(IdString root, std::span<const std::string> names) {
	IdString path = root;
	for (auto &name : names)
		path = extend(root, path, name);
	return path;
}

MetaRef MetaPool::intern(MetaBlock block) {
	canonicalize(block);
	if (!block.hdlname.empty())
		block.absorbed_hdlnames = sets_.without_member(block.absorbed_hdlnames, block.hdlname);
	else if (!block.scope.empty())
		block.absorbed_scopes = sets_.without_member(block.absorbed_scopes, block.scope);
	canonicalize(block);
	if (block.is_dead())
		return MetaRef::Null;
	uint32_t tag = !block.hdlname.empty() ? MetaRef::HDLNAME_BIT
		: !block.scope.empty() ? MetaRef::SCOPENAME_BIT : 0;
	MetaRef ref = intern_node(std::move(block));
	ref.value |= tag;
	return ref;
}

std::string MetaPool::hdlname(MetaRef ref) const {
	if (!ref.has_hdlname())
		return {};
	return twines.str((*this)[ref].hdlname);
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
		if (!block.hdlname.empty())
			block.scope = block.hdlname = IdString();
		return intern(std::move(block));
	}
	IdString root = this->root();
	block.scope = add_path(root, std::span(elems).first(elems.size() - 1));
	block.hdlname = extend(root, block.scope, elems.back());
	return intern(std::move(block));
}

MetaRef MetaPool::with_scopename(MetaRef ref, std::string_view path) {
	MetaBlock block = ref == MetaRef::Null ? MetaBlock{} : (*this)[ref];
	if (!block.hdlname.empty())
		return ref;
	std::vector<std::string> elems = split_tokens(std::string(path), " ");
	block.scope = elems.empty() ? IdString() : add_path(root(), elems);
	return intern(std::move(block));
}

MetaRef MetaPool::without_hdlname(MetaRef ref) {
	if (!ref.has_hdlname())
		return ref;
	MetaBlock block = (*this)[ref];
	block.hdlname = IdString();
	if (block.scope == root())
		block.scope = IdString();
	return intern(std::move(block));
}

MetaRef MetaPool::transfer(MetaRef target, MetaRef source) {
	if (target == MetaRef::Null || target == source)
		return source;
	MetaBlock block = (*this)[target];
	absorb_identity(block, block);
	block.scope = block.hdlname = IdString();
	if (source != MetaRef::Null) {
		const MetaBlock &from = (*this)[source];
		block.scope = from.scope;
		block.hdlname = from.hdlname;
		absorb_sets(block, from);
	}
	return intern(std::move(block));
}

MetaRef MetaPool::absorb(MetaRef target, MetaRef source) {
	if (source == MetaRef::Null || target == source)
		return target;
	MetaBlock block = target == MetaRef::Null ? MetaBlock{} : (*this)[target];
	const MetaBlock &from = (*this)[source];
	absorb_identity(block, from);
	absorb_sets(block, from);
	return intern(std::move(block));
}

MetaRef MetaPool::copy_from(const MetaPool &other, MetaRef ref) {
	if (ref == MetaRef::Null)
		return ref;
	const MetaBlock &from = other[ref];
	MetaBlock block;
	block.scope = twines.copy_from(other.twines, from.scope);
	block.hdlname = twines.copy_from(other.twines, from.hdlname);
	block.absorbed_hdlnames = sets_.copy_from(other.sets_, from.absorbed_hdlnames);
	block.absorbed_scopes = sets_.copy_from(other.sets_, from.absorbed_scopes);
	return intern(std::move(block));
}

void MetaPool::root_members(const Marks &live_metas, pool<IdString> &live_twines) const {
	for (MetaRef ref : live_metas) {
		const MetaBlock &block = (*this)[ref];
		if (!block.scope.empty())
			live_twines.insert(block.scope);
		if (!block.hdlname.empty())
			live_twines.insert(block.hdlname);
	}
	sets_.root_members(absorbed_sets(live_metas), live_twines);
}

void MetaPool::dump(MetaRef ref, std::ostream &os) const {
	const MetaBlock &block = (*this)[ref];
	os << "Meta[scope @" << block.scope.raw() << ", hdlname @" << block.hdlname.raw()
		<< ", absorbed hdlnames $" << block.absorbed_hdlnames.raw()
		<< ", absorbed scopes $" << block.absorbed_scopes.raw() << "]";
}

YOSYS_NAMESPACE_END
