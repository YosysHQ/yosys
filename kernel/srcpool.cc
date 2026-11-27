#include "kernel/srcpool.h"
#include "kernel/hashcons_impl.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

template struct HashConsPool<SrcPool, SrcSet, SrcRef>;

template<typename T> concept Ordered = requires(T a) { a < a; };
template<typename T> concept Indexable = requires(T a) { a.raw(); };
static_assert(!Ordered<SrcRef> && !Indexable<SrcRef>);
static_assert(Ordered<IdString> && Indexable<IdString>);

bool SrcPool::Marks::insert(SrcRef ref) {
	size_t idx = ref.raw();
	if (idx >= seen.size())
		seen.resize(idx + 1);
	if (seen[idx])
		return false;
	seen[idx] = true;
	refs.push_back(ref);
	return true;
}

SrcRef SrcPool::stamp(SrcRef ref) const {
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	if (ref != SrcRef::Null)
		ref.serial = (uint32_t) twines.serial_;
#endif
	return ref;
}

void SrcPool::check_owned([[maybe_unused]] SrcRef ref) const {
#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
	log_assert(ref.serial == 0 || ref.serial == twines.serial_);
	log_assert(is_live(ref));
#endif
}

struct SrcEq {
	const SrcPool &pool;
	std::span<const IdString> members;
	bool operator()(SrcRef ref) const {
		const std::vector<IdString> &stored = pool[ref].members();
		return std::equal(stored.begin(), stored.end(), members.begin(), members.end());
	}
};

void SrcPool::clone_from(const SrcPool &other) {
	log_assert(twines.shares_index_space_with(other.twines));
	HashConsPool::operator=(static_cast<const HashConsPool &>(other));
}

void SrcPool::clear() {
	backing.clear();
	free_list.clear();
	std::fill(table.begin(), table.end(), SrcRef());
	index_entries = 0;
}

uint64_t SrcSet::hash_members(std::span<const IdString> members) {
	Hasher h;
	for (IdString member : members)
		h.eat(member);
	return h.yield();
}

IdString SrcPool::file(std::string_view name) {
	return twines.add(TwineSpec{TwineSpec::Root{std::string(name)}});
}

IdString SrcPool::location(IdString file, int line) {
	return twines.add(file, stringf(":%d", line));
}

IdString SrcPool::location(IdString file, int line, int col) {
	return twines.add(file, stringf(":%d.%d", line, col));
}

IdString SrcPool::location(IdString file, int line1, int col1, int line2, int col2) {
	return twines.add(file, stringf(":%d.%d-%d.%d", line1, col1, line2, col2));
}

SrcRef SrcPool::add(IdString location) {
	return intern({location});
}

SrcRef SrcPool::add(std::span<const IdString> locations) {
	return intern(std::vector<IdString>(locations.begin(), locations.end()));
}

IdString SrcPool::parse_location(std::string_view location) {
	size_t colon = location.rfind(':');
	if (colon == std::string_view::npos)
		return file(location);
	return twines.add(file(location.substr(0, colon)), location.substr(colon));
}

SrcRef SrcPool::add_parsed(std::string_view text) {
	std::vector<IdString> members;
	while (!text.empty()) {
		size_t bar = text.find('|');
		std::string_view location = text.substr(0, bar);
		if (!location.empty())
			members.push_back(parse_location(location));
		if (bar == std::string_view::npos)
			break;
		text.remove_prefix(bar + 1);
	}
	return intern(std::move(members));
}

SrcRef SrcPool::merge(std::span<const SrcRef> refs) {
	log_assert(!Multithreading::active());

	struct DistinctRefs {
		SrcRef first = SrcRef::Null;
		SrcRef second = SrcRef::Null;
		bool rest = false;

		void add(SrcRef ref)
		{
			if (ref == SrcRef::Null || ref == first || ref == second)
				return;
			if (first == SrcRef::Null)
				first = ref;
			else if (second == SrcRef::Null)
				second = ref;
			else
				rest = true;
		}

		int size() const {
			if (rest)
				return 3;
			if (second != SrcRef::Null)
				return 2;
			return first != SrcRef::Null ? 1 : 0;
		}
	};

	DistinctRefs distinct = {};
	for (SrcRef ref : refs) {
		if (ref != SrcRef::Null)
			check_owned(ref);
		distinct.add(ref);
		if (distinct.rest)
			break;
	}

	// Optimized handling for 0, 1, or 2 refs
	if (distinct.size() < 2)
		return distinct.first;
	if (distinct.size() == 2)
		return merge_unchecked(distinct.first, distinct.second);

	// More than 2 distinct refs
	std::vector<IdString> members = {};
	for (SrcRef ref : refs)
		if (ref != SrcRef::Null)
			members.insert(members.end(), (*this)[ref].members().begin(), (*this)[ref].members().end());
	std::sort(members.begin(), members.end());
	members.erase(std::unique(members.begin(), members.end()), members.end());
	return intern_unchecked(std::move(members));
}

SrcRef SrcPool::merge(SrcRef a, SrcRef b) {
	log_assert(!Multithreading::active());
	if (a != SrcRef::Null)
		check_owned(a);
	if (b != SrcRef::Null)
		check_owned(b);
	if (a == SrcRef::Null || a == b)
		return b;
	if (b == SrcRef::Null)
		return a;
	return merge_unchecked(a, b);
}

SrcRef SrcPool::merge_unchecked(SrcRef a, SrcRef b) {
	const std::vector<IdString> &ma = (*this)[a].members();
	const std::vector<IdString> &mb = (*this)[b].members();
	std::vector<IdString> scratch;
	size_t only_a = 0;
	size_t only_b = 0;
	auto ia = ma.begin();
	auto ib = mb.begin();
	while (ia != ma.end() && ib != mb.end()) {
		if (*ia < *ib) {
			scratch.push_back(*ia++);
			only_a++;
		} else if (*ib < *ia) {
			scratch.push_back(*ib++);
			only_b++;
		} else {
			scratch.push_back(*ia++);
			ib++;
		}
	}
	only_a += ma.end() - ia;
	only_b += mb.end() - ib;
	if (only_b == 0)
		return a;
	if (only_a == 0)
		return b;
	scratch.insert(scratch.end(), ia, ma.end());
	scratch.insert(scratch.end(), ib, mb.end());
	return intern_unchecked(std::move(scratch));
}

SrcRef SrcPool::intern_unchecked(std::vector<IdString> scratch) {
	uint64_t hash = SrcSet::hash_members(scratch);
	SrcRef found = find_hashed(hash, SrcEq{*this, scratch});
	if (found != SrcRef::Null)
		return stamp(found);
	return stamp(add_inner(SrcSet{std::move(scratch), hash}));
}

SrcRef SrcPool::place(size_t idx, std::span<const IdString> members) {
	std::vector<IdString> canon(members.begin(), members.end());
	canonicalize_members(canon);
	if (canon.empty())
		return SrcRef::Null;
	uint64_t hash = SrcSet::hash_members(canon);
	return stamp(HashConsPool::place(idx, SrcSet{std::move(canon), hash}));
}

SrcRef SrcPool::find_members(std::span<const IdString> members) const {
	std::vector<IdString> canon(members.begin(), members.end());
	canonicalize_members(canon);
	if (canon.empty())
		return SrcRef::Null;
	return stamp(find_hashed(SrcSet::hash_members(canon), SrcEq{*this, canon}));
}

SrcRef SrcPool::copy_from(const SrcPool &other, SrcRef ref) {
	if (ref == SrcRef::Null)
		return ref;
	std::vector<IdString> members;
	members.reserve(other[ref].members().size());
	for (IdString member : other[ref].members())
		members.push_back(twines.copy_from(other.twines, member));
	return intern(std::move(members));
}

namespace {
struct RenderedLocation {
	std::string text;
	size_t file_size;
	std::vector<long> numbers;

	explicit RenderedLocation(std::string rendered) : text(std::move(rendered)) {
		size_t colon = text.rfind(':');
		file_size = colon == std::string::npos ? text.size() : colon;
		if (colon == std::string::npos)
			return;
		for (size_t i = colon + 1; i < text.size(); i++) {
			if (!isdigit((unsigned char) text[i]))
				continue;
			char *end;
			numbers.push_back(strtol(text.c_str() + i, &end, 10));
			i = end - text.c_str();
		}
	}

	std::string_view file() const { return std::string_view(text).substr(0, file_size); }

	bool operator<(const RenderedLocation &other) const {
		if (file() != other.file())
			return file() < other.file();
		if (numbers != other.numbers)
			return numbers < other.numbers;
		return text < other.text;
	}
};
}

std::string SrcPool::str(SrcRef ref) const {
	std::string out;
	if (ref == SrcRef::Null)
		return out;
	const std::vector<IdString> &members = (*this)[ref].members();
	if (members.size() == 1)
		return twines.str(members[0]);
	std::vector<RenderedLocation> locations;
	for (IdString member : members)
		locations.emplace_back(twines.str(member));
	std::sort(locations.begin(), locations.end());
	for (auto &location : locations) {
		if (!out.empty())
			out += '|';
		out += location.text;
	}
	return out;
}

const std::vector<IdString> &SrcPool::locations(SrcRef ref) const {
	static const std::vector<IdString> none;
	if (ref == SrcRef::Null)
		return none;
	return (*this)[ref].members();
}

void SrcPool::root_members(const Marks &live_srcs, pool<IdString> &live_twines) const {
	for (SrcRef ref : live_srcs)
		for (IdString member : (*this)[ref].members())
			live_twines.insert(member);
}

size_t SrcPool::gc(const Marks &live_srcs) {
	return HashConsPool::gc(live_srcs);
}

void SrcPool::dump(SrcRef ref, std::ostream &os) const {
	os << "Set[";
	bool first = true;
	for (IdString member : (*this)[ref].members()) {
		if (!first)
			os << ", ";
		first = false;
		os << "@" << member.raw();
	}
	os << "]";
}

void SrcPool::dump(std::ostream &os) const {
	os << "--- SrcPool Dump (" << size() << " nodes) ---\n";
	for (size_t idx = 0; idx < backing.size(); ++idx) {
		if (backing[idx].is_dead())
			continue;
		os << idx << " -> ";
		dump(SrcRef(idx), os);
		os << '\n';
	}
	os << "--------------------------------\n";
}

void SrcPool::canonicalize_members(std::vector<IdString> &members) {
	for (IdString &member : members)
		member = member.untag().stamped(0);
	std::sort(members.begin(), members.end());
	members.erase(std::unique(members.begin(), members.end()), members.end());
}

SrcRef SrcPool::intern(std::vector<IdString> members) {
	canonicalize_members(members);
	if (members.empty())
		return SrcRef::Null;
	return intern_unchecked(std::move(members));
}

size_t SrcPoolIo::index(const SrcPool &pool, SrcRef ref) {
	pool.check_owned(ref);
	return ref.raw();
}

SrcRef SrcPoolIo::place(SrcPool &pool, size_t idx, std::span<const IdString> members) {
	return pool.place(idx, members);
}

SrcRef SrcPoolIo::find(const SrcPool &pool, std::span<const IdString> members) {
	return pool.find_members(members);
}

void SrcPoolIo::finish_placement(SrcPool &pool) {
	pool.finish_placement();
}

YOSYS_NAMESPACE_END
