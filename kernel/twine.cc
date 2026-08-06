#include "kernel/twine.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

std::vector<TwineNode> StaticTwines::nodes_;

void StaticTwines::init() {
	if (ready())
		return;
	log_assert(nodes_.empty());
	nodes_.reserve(count);
#define X(_id) nodes_.push_back(Twine::Leaf{#_id});
#include "kernel/constids.inc"
#undef X
}

const TwineNode &StaticTwines::node(size_t idx) { return nodes_[idx]; }
bool StaticTwines::ready() { return nodes_.size() == count; }

int64_t twine_gc_ns;
int twine_gc_count;

Hasher IdString::hash_into(Hasher h) const { h.hash64(value); return h; }

std::string IdString::handle_token() const {
	return stringf("%s@%zu", isPublic() ? "$pub" : "$priv", untag().raw());
}

size_t IdString::handle_token_prefix(std::string_view token, bool &is_public) {
	if (token.substr(0, 5) == "$pub@") {
		is_public = true;
		return 5;
	}
	if (token.substr(0, 6) == "$priv@") {
		is_public = false;
		return 6;
	}
	return 0;
}

std::string ID::str(IdString ref) {
	IdString idx = ref.untag();
	log_assert(idx.raw() < STATIC_TWINE_END);
	std::string result = ref.isPublic() ? "\\" : "";
	result += static_names[idx.raw()];
	return result;
}

std::string ID::unescaped_str(IdString ref) {
	IdString idx = ref.untag();
	log_assert(idx.raw() < STATIC_TWINE_END);
	return static_names[idx.raw()];
}

bool Twine::is_leaf() const { return std::holds_alternative<Leaf>(data); }
bool Twine::is_suffix() const { return std::holds_alternative<Suffix>(data); }

bool TwineNode::is_dead() const { return std::holds_alternative<std::monostate>(data); }
bool TwineNode::is_leaf() const { return std::holds_alternative<Twine::Leaf>(data); }
bool TwineNode::is_suffix() const { return std::holds_alternative<Twine::Suffix>(data); }
const std::string &TwineNode::leaf() const { return std::get<Twine::Leaf>(data).s; }
const Twine::Suffix &TwineNode::suffix() const { return std::get<Twine::Suffix>(data); }

std::string Twine::content_str() const {
	if (auto *leaf = std::get_if<Leaf>(&data))
		return leaf->s;
	auto &autosfx = std::get<AutoSuffix>(data);
	return std::string(autosfx.prefix) + autosfx.tail;
}

std::pair<std::string, bool> twine_unescape(std::string s) {
	bool is_public = !(s.size() > 1 && s[0] == '$');
	if (s.size() > 1 && s[0] == '\\')
		s.erase(0, 1);
	return {std::move(s), is_public};
}

const TwineNode& TwinePool::static_node(size_t idx) { return StaticTwines::node(idx); }
void TwinePool::check_ready() { log_assert(StaticTwines::ready()); }

void TwinePool::canonicalize(TwineNode& t) {
	if (auto *sfx = std::get_if<Twine::Suffix>(&t.data))
		sfx->prefix = sfx->prefix.untag();
}

size_t TwinePool::hash_node(const TwineNode& t) {
	Hasher h;

	std::visit([&h](const auto& val) {
		using T = std::decay_t<decltype(val)>;
		if constexpr (std::is_same_v<T, Twine::Leaf>) {
			h.eat(val.s);
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			h.eat(val.prefix);
			h.eat(val.tail);
		}
	}, t.data);

	return h.yield();
}

void TwinePool::dump(IdString ref, std::ostream& os) const {
	const TwineNode& twine = (*this)[ref];
	std::visit([&](const auto& val) {
		using T = std::decay_t<decltype(val)>;
		if constexpr (std::is_same_v<T, std::monostate>) {
			os << "Dead()";
		} else if constexpr (std::is_same_v<T, Twine::Leaf>) {
			os << "Leaf(\"" << val.s << "\")";
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			os << "Suffix(prefix: ";
			dump(val.prefix, os);
			os << ", tail: \"" << val.tail << "\")";
		}
	}, twine.data);
	if (ref.isPublic())
		os << " pub";
}

void TwinePool::print(IdString ref, std::ostream& os) const {
	if (ref == IdString::Null)
		return;
	if (ref.isPublic())
		os << '\\';
	std::visit([&](const auto& val) {
		using T = std::decay_t<decltype(val)>;
		if constexpr (std::is_same_v<T, std::monostate>) {
		} else if constexpr (std::is_same_v<T, Twine::Leaf>) {
			os << val.s;
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			print(val.prefix, os);
			os << val.tail;
		}
	}, (*this)[ref].data);
}

void TwinePool::append_str(IdString ref, std::string& out) const {
	if (ref == IdString::Null)
		return;
	if (ref.isPublic())
		out += '\\';
	std::visit([&](const auto& val) {
		using T = std::decay_t<decltype(val)>;
		if constexpr (std::is_same_v<T, std::monostate>) {
		} else if constexpr (std::is_same_v<T, Twine::Leaf>) {
			out += val.s;
		} else if constexpr (std::is_same_v<T, Twine::Suffix>) {
			append_str(val.prefix, out);
			out += val.tail;
		}
	}, (*this)[ref].data);
}

std::string TwinePool::str(IdString ref) const {
	std::string out;
	append_str(ref, out);
	return out;
}

std::string TwinePool::unescaped_str(IdString ref) const {
	return str(ref.untag());
}

IdString TwinePool::find(const std::string &name) const {
	bool is_public = !name.empty() && name[0] == '\\';
	return find(Twine::Leaf{is_public ? name.substr(1) : name}).tag(is_public);
}

IdString TwinePool::find(Twine t) const {
	if (auto *ap = std::get_if<Twine::AutoSuffix>(&t.data)) {
		IdString prefix = HashConsPool::find(Twine::Leaf{std::string(ap->prefix)});
		if (prefix == IdString::Null)
			return IdString::Null;
		t = Twine::Suffix{prefix, std::move(ap->tail)};
	}
	bool is_public = inherits_publicity(t);
	return HashConsPool::find(to_node(std::move(t))).tag(is_public);
}

IdString TwinePool::add(Twine t) {
	if (auto *ap = std::get_if<Twine::AutoSuffix>(&t.data)) {
		IdString prefix = add_inner(Twine::Leaf{std::string(ap->prefix)});
		t = Twine::Suffix{prefix, std::move(ap->tail)};
	}
	bool is_public = inherits_publicity(t);
	return add_inner(to_node(std::move(t))).tag(is_public);
}

IdString TwinePool::add(std::string s) {
	if (s.empty())
		return IdString::Null;
	auto [content, is_public] = twine_unescape(std::move(s));
	return add_inner(Twine::Leaf{std::move(content)}).tag(is_public);
}

IdString TwinePool::copy_from(const TwinePool& src, IdString ref) {
	if (ref == IdString::Null)
		return ref;

	bool is_public = ref.isPublic();
	IdString untagged = ref.untag();
	if (ID::is_static(untagged))
		return ref;
	const TwineNode& t = src[untagged];
	if (t.is_leaf())
		return (add(Twine::Leaf{t.leaf()})).tag(is_public);
	if (t.is_suffix())
		return (add(Twine::Suffix{copy_from(src, t.suffix().prefix), t.suffix().tail})).tag(is_public);
	return IdString::Null;
}

IdString TwinePool::find_from(const TwinePool& src, IdString ref) const {
	if (ref == IdString::Null)
		return ref;

	bool is_public = ref.isPublic();
	IdString untagged = ref.untag();
	if (ID::is_static(untagged))
		return ref;
	const TwineNode& t = src[untagged];
	if (t.is_leaf())
		return find(Twine::Leaf{t.leaf()}).tag(is_public);
	if (t.is_suffix()) {
		IdString prefix = find_from(src, t.suffix().prefix);
		if (prefix == IdString::Null)
			return IdString::Null;
		return find(Twine::Suffix{prefix, t.suffix().tail}).tag(is_public);
	}
	return IdString::Null;
}

void TwinePool::dump(std::ostream& os) const {
	os << "--- TwinePool Dump (" << backing.size() << " nodes) ---\n";
	for (size_t idx = 0; idx < backing.size(); ++idx) {
		IdString ref(STATIC_COUNT + idx);
		os << ref.raw() << " -> ";
		dump(ref, os);
		os << '\n';
	}
	os << "--------------------------------\n";
}

bool TwinePool::inherits_publicity(const Twine &t) {
	auto *sfx = std::get_if<Twine::Suffix>(&t.data);
	return sfx != nullptr && sfx->prefix.isPublic();
}

TwineNode TwinePool::to_node(Twine t) {
	if (auto *leaf = std::get_if<Twine::Leaf>(&t.data))
		return TwineNode{std::move(*leaf)};
	return TwineNode{std::move(std::get<Twine::Suffix>(t.data))};
}

/** 
 * TwineSegments holds a sequence of string_views refering to the strings
 * an IdString is composed of. It's used for lightweight comparisons.
 * The sequences is implemented in a "small vector" style,
 * so that IdStrings with few segments fit into the `inline_segs` field,
 * and anything beyond that is in `spill`.
 */
struct TwineSegments {
	static constexpr size_t SEGMENT_INLINE_DEPTH = 8;
	TwineSegments(const TwinePool &pool, IdString ref);
	std::string_view peek();
	void advance(size_t n);
	size_t total_size() const;
private:
	void push(std::string_view seg);
	std::string_view *segs();
	const std::string_view *segs() const;
	std::string_view inline_segs[SEGMENT_INLINE_DEPTH];
	std::vector<std::string_view> spill;
	size_t count = 0;
	size_t pos = 0;
	size_t off = 0;
};

TwineSegments::TwineSegments(const TwinePool &pool, IdString ref)
{
	if (ref == IdString::Null)
		return;
	for (IdString cur = ref.untag(); ;) {
		const TwineNode &t = pool[cur];
		if (t.is_suffix()) {
			push(t.suffix().tail);
			cur = t.suffix().prefix.untag();
			continue;
		}
		if (t.is_leaf())
			push(t.leaf());
		break;
	}
	if (ref.isPublic())
		push("\\");
	std::reverse(segs(), segs() + count);
}

std::string_view TwineSegments::peek()
{
	while (pos < count) {
		std::string_view seg = segs()[pos];
		if (off < seg.size())
			return seg.substr(off);
		pos++;
		off = 0;
	}
	return {};
}

void TwineSegments::advance(size_t n) { off += n; }

size_t TwineSegments::total_size() const
{
	size_t total = 0;
	for (size_t i = 0; i < count; i++)
		total += segs()[i].size();
	return total;
}

void TwineSegments::push(std::string_view seg)
{
	if (spill.empty() && count < SEGMENT_INLINE_DEPTH) {
		inline_segs[count++] = seg;
		return;
	}
	if (spill.empty())
		spill.assign(inline_segs, inline_segs + count);
	spill.push_back(seg);
	count++;
}

std::string_view *TwineSegments::segs() { return spill.empty() ? inline_segs : spill.data(); }
const std::string_view *TwineSegments::segs() const { return spill.empty() ? inline_segs : spill.data(); }

size_t TwinePool::str_size(IdString ref) const
{
	return TwineSegments(*this, ref).total_size();
}

bool TwinePool::begins_with(IdString ref, std::string_view prefix) const
{
	TwineSegments segs(*this, ref);
	while (!prefix.empty()) {
		std::string_view seg = segs.peek();
		if (seg.empty())
			return false;
		size_t n = std::min(seg.size(), prefix.size());
		if (std::memcmp(seg.data(), prefix.data(), n) != 0)
			return false;
		segs.advance(n);
		prefix.remove_prefix(n);
	}
	return true;
}

bool TwinePool::name_equal(IdString ref, std::string_view name) const
{
	return str_size(ref) == name.size() && begins_with(ref, name);
}

static int compare_segments(TwineSegments &sa, TwineSegments &sb)
{
	while (true) {
		std::string_view x = sa.peek(), y = sb.peek();
		if (x.empty() || y.empty())
			return x.empty() ? (y.empty() ? 0 : -1) : 1;
		size_t n = std::min(x.size(), y.size());
		if (int diff = std::memcmp(x.data(), y.data(), n); diff != 0)
			return diff;
		sa.advance(n);
		sb.advance(n);
	}
}

bool TwinePool::content_equal(IdString a, IdString b) const
{
	if (a == b)
		return true;

	TwineSegments sa(*this, a.untag()), sb(*this, b.untag());
	return compare_segments(sa, sb) == 0;
}

int TwinePool::compare_by_name(IdString a, IdString b) const
{
	if (a == b)
		return 0;
	if (a == IdString::Null)
		return -1;
	if (b == IdString::Null)
		return 1;

	if (a.isPublic() == b.isPublic()) {
		const TwineNode &ta = (*this)[a.untag()];
		const TwineNode &tb = (*this)[b.untag()];
		if (ta.is_leaf() && tb.is_leaf())
			return ta.leaf().compare(tb.leaf());
		if (ta.is_suffix() && tb.is_suffix() && ta.suffix().prefix == tb.suffix().prefix)
			return ta.suffix().tail.compare(tb.suffix().tail);
	}

	TwineSegments sa(*this, a), sb(*this, b);
	return compare_segments(sa, sb);
}

void DeepTwineHash::Stream::push(std::string_view sv) {
	for (char c : sv) {
		buf |= uint64_t(static_cast<unsigned char>(c)) << (8 * fill);
		if (++fill == 8) {
			h.hash64(buf);
			buf = 0;
			fill = 0;
		}
	}
}

size_t DeepTwineHash::Stream::finish() {
	h.hash64(buf);
	return h.yield();
}

void DeepTwineHash::combine(Stream& s, IdString t) const {
	if (t == IdString::Null)
		return;
	const TwineNode& n = (*pool)[t];
	if (n.is_dead()) return;

	if (n.is_leaf()) {
		s.push(n.leaf());
	} else if (n.is_suffix()) {
		combine(s, n.suffix().prefix);
		s.push(n.suffix().tail);
	}
}

size_t DeepTwineHash::operator()(std::string_view sv) const {
	Stream s;
	s.push(sv);
	return s.finish();
}

size_t DeepTwineHash::operator()(IdString t) const {
	Stream s;
	combine(s, t);
	return s.finish();
}

bool DeepTwineEq::consume(IdString t, std::string_view& sv) const noexcept {
	if (t == IdString::Null)
		return true;
	const TwineNode& n = (*pool)[t];
	if (n.is_dead()) return true;

	if (n.is_leaf()) {
		if (!sv.starts_with(n.leaf())) return false;
		sv.remove_prefix(n.leaf().size());
		return true;
	} else if (n.is_suffix()) {
		if (!consume(n.suffix().prefix, sv)) return false;
		if (!sv.starts_with(n.suffix().tail)) return false;
		sv.remove_prefix(n.suffix().tail.size());
		return true;
	}
	return false;
}

bool DeepTwineEq::operator()(IdString t, std::string_view sv) const noexcept {
	return consume(t, sv) && sv.empty();
}

bool DeepTwineEq::operator()(std::string_view sv, IdString t) const noexcept {
	return (*this)(t, sv);
}

bool DeepTwineEq::operator()(IdString a, IdString b) const {
	return pool->content_equal(a, b);
}

TwineSearch::TwineSearch(const TwinePool* pool) : pool(pool), index(0, DeepTwineHash{pool}, DeepTwineEq{pool}) {
	for (IdString ref : pool->refs())
		index.insert(ref);
}

void TwineSearch::insert(IdString ref) {
	index.insert(ref.untag());
}

IdString TwineSearch::find(std::string_view sv) const {
	bool is_public = !sv.empty() && sv[0] == '\\';
	if (is_public)
		sv.remove_prefix(1);
	if (auto it = index.find(sv); it != index.end()) {
		return (*it).tag(is_public);
	}
	return IdString::Null;
}

YOSYS_NAMESPACE_END
