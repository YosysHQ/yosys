#include "kernel/twine.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

std::vector<TwineNode> StaticTwines::nodes_;

void StaticTwines::init() {
	if (ready())
		return;
	log_assert(nodes_.empty());
	nodes_.reserve(count);
	for (const char *name : ID::static_names)
		nodes_.emplace_back(std::string_view(name));
}

const TwineNode &StaticTwines::node(size_t idx) { return nodes_[idx]; }
bool StaticTwines::ready() { return nodes_.size() == count; }

int64_t twine_gc_ns;
int twine_gc_count;

Hasher IdString::hash_into(Hasher h) const { h.hash64(eq_key()); return h; }

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

TwineSpec::TwineSpec(Leaf v) : data(std::move(v)) {}
TwineSpec::TwineSpec(Suffix v) : data(std::move(v)) {}
TwineSpec::TwineSpec(AutoSuffix v) : data(std::move(v)) {}

bool TwineSpec::holds_leaf() const { return std::holds_alternative<Leaf>(data); }
bool TwineSpec::holds_suffix() const { return std::holds_alternative<Suffix>(data); }

void SmallString::store(std::string_view content)
{
	log_assert(content.size() <= MAX_LEN);
	release();
	len_ = content.size();
	if (len_ > INLINE_CAP) {
		ptr_ = new char[len_];
		memcpy(ptr_, content.data(), len_);
	} else {
		memcpy(inl_, content.data(), len_);
	}
}

void SmallString::release()
{
	if (len_ > INLINE_CAP)
		delete[] ptr_;
	len_ = 0;
}

SmallString::SmallString(std::string_view content) { store(content); }

SmallString::SmallString(const SmallString &other) { store(other.view()); }

SmallString::SmallString(SmallString &&other) noexcept : len_(other.len_)
{
	memcpy(inl_, other.inl_, INLINE_CAP);
	other.len_ = 0;
}

SmallString &SmallString::operator=(const SmallString &other)
{
	if (this != &other)
		store(other.view());
	return *this;
}

SmallString &SmallString::operator=(SmallString &&other) noexcept
{
	if (this == &other)
		return *this;
	release();
	memcpy(inl_, other.inl_, INLINE_CAP);
	len_ = other.len_;
	other.len_ = 0;
	return *this;
}

SmallString::~SmallString() { release(); }

TwineNode::TwineNode(TwineNode &&other) noexcept
	: text_(std::move(other.text_)), prefix_(other.prefix_)
{
	other.prefix_ = DEAD;
}

TwineNode &TwineNode::operator=(TwineNode &&other) noexcept
{
	if (this == &other)
		return *this;
	text_ = std::move(other.text_);
	prefix_ = other.prefix_;
	other.prefix_ = DEAD;
	return *this;
}

std::string TwineSpec::content_str() const {
	if (auto *leaf = std::get_if<Leaf>(&data))
		return leaf->s;
	log_assert(!holds_suffix());
	auto &autosfx = std::get<AutoSuffix>(data);
	return *autosfx.prefix + autosfx.tail;
}

std::pair<std::string, bool> twine_unescape(std::string s) {
	bool is_public = !(s.size() > 1 && s[0] == '$');
	if (s.size() > 1 && s[0] == '\\')
		s.erase(0, 1);
	return {std::move(s), is_public};
}

TwinePool::TwinePool() : serial_(next_serial()) {}
TwinePool::TwinePool(const TwinePool& other)
	: HashConsPool(other), auto_prefixes(other.auto_prefixes), serial_(next_serial()) {}
TwinePool::TwinePool(TwinePool&& other)
	: HashConsPool(std::move(other)), auto_prefixes(std::move(other.auto_prefixes)), serial_(next_serial()) {}

TwinePool& TwinePool::operator=(const TwinePool& other) {
	if (this == &other)
		return *this;
	HashConsPool::operator=(other);
	auto_prefixes = other.auto_prefixes;
	serial_ = next_serial();
	return *this;
}

TwinePool& TwinePool::operator=(TwinePool&& other) {
	if (this == &other)
		return *this;
	HashConsPool::operator=(std::move(other));
	auto_prefixes = std::move(other.auto_prefixes);
	serial_ = next_serial();
	return *this;
}

size_t TwinePool::serial() const { return serial_; }

bool TwinePool::owns(IdString ref) const {
	return ref == IdString::Null || ref.serial() == 0 || ref.serial() == serial_ || ID::is_static(ref);
}

IdString TwinePool::stamp(IdString ref) const {
	if (ref == IdString::Null || ID::is_static(ref))
		return ref;
	return ref.stamped(serial_);
}

void TwinePool::check_owned(IdString ref) const {
	if constexpr (IdString::MAX_SERIAL != 0)
		log_assert(owns(ref));
}

const TwineNode& TwinePool::operator[](IdString ref) const {
	check_owned(ref);
	return HashConsPool::operator[](ref);
}

const TwineNode& TwinePool::static_node(size_t idx) { return StaticTwines::node(idx); }
void TwinePool::check_ready() { log_assert(StaticTwines::ready()); }

void TwinePool::canonicalize(TwineNode&) {}

size_t TwinePool::next_serial() {
	static size_t counter = 0;
	size_t serial = ++counter;
	if constexpr (IdString::MAX_SERIAL == 0)
		return serial;
	else
		return serial > IdString::MAX_SERIAL ? (serial % IdString::MAX_SERIAL) + 1 : serial;
}

IdString TwinePool::add_inner(TwineNode t) {
	if (free_list.empty() && STATIC_COUNT + backing.size() > IdString::MAX_INDEX)
		log_error("Out of twine handles: a design may name at most %zu distinct twines.\n",
				IdString::MAX_INDEX - STATIC_COUNT);
	return HashConsPool::add_inner(std::move(t));
}

size_t TwinePool::hash_node(const TwineNode& t) {
	return hash_key(t.key());
}

size_t TwinePool::hash_key(const TwineNode::Key& k) {
	Hasher h;
	if (k.prefix < TwineNode::DEAD)
		h.eat(IdString(k.prefix));
	h.eat(k.text);
	return h.yield();
}

void TwinePool::dump(IdString ref, std::ostream& os) const {
	const TwineNode& twine = (*this)[ref];
	switch (twine.kind()) {
	case TwineNode::Kind::Dead:
		os << "Dead()";
		break;
	case TwineNode::Kind::Leaf:
		os << "Leaf(\"" << twine.text() << "\")";
		break;
	case TwineNode::Kind::Suffix:
		os << "Suffix(prefix: ";
		dump(twine.prefix(), os);
		os << ", tail: \"" << twine.text() << "\")";
		break;
	}
	if (ref.isPublic())
		os << " pub";
}

void TwinePool::print(IdString ref, std::ostream& os) const {
	if (ref == IdString::Null)
		return;
	if (ref.isPublic())
		os << '\\';
	const TwineNode& twine = (*this)[ref];
	switch (twine.kind()) {
	case TwineNode::Kind::Dead:
		break;
	case TwineNode::Kind::Suffix:
		print(twine.prefix(), os);
		[[fallthrough]];
	case TwineNode::Kind::Leaf:
		os << twine.text();
		break;
	}
}

void TwinePool::append_str(IdString ref, std::string& out) const {
	if (ref == IdString::Null)
		return;
	if (ref.isPublic())
		out += '\\';
	const TwineNode& twine = (*this)[ref];
	switch (twine.kind()) {
	case TwineNode::Kind::Dead:
		break;
	case TwineNode::Kind::Suffix:
		append_str(twine.prefix(), out);
		[[fallthrough]];
	case TwineNode::Kind::Leaf:
		out += twine.text();
		break;
	}
}

std::string TwinePool::str(IdString ref) const {
	std::string out;
	append_str(ref, out);
	return out;
}

std::string TwinePool::unescaped_str(IdString ref) const {
	return str(ref.untag());
}

IdString TwinePool::find_content(uint32_t prefix, std::string_view text) const {
	return HashConsPool::find_key(TwineNode::Key{prefix, text});
}

IdString TwinePool::intern(uint32_t prefix, std::string_view text) {
	IdString ref = HashConsPool::find_key(TwineNode::Key{prefix, text});
	if (ref != IdString::Null)
		return ref;
	return add_inner(TwineNode{prefix, text});
}

IdString TwinePool::find(const std::string &name) const {
	bool is_public = !name.empty() && name[0] == '\\';
	std::string_view content = name;
	if (is_public)
		content.remove_prefix(1);
	return stamp(find_content(TwineNode::NO_PREFIX, content).tag(is_public));
}

IdString TwinePool::find(TwineSpec t) const {
	if (auto *ap = std::get_if<TwineSpec::AutoSuffix>(&t.data)) {
		IdString prefix = find_content(TwineNode::NO_PREFIX, *ap->prefix);
		if (prefix == IdString::Null)
			return IdString::Null;
		return stamp(find_content((uint32_t)prefix.untag().raw(), ap->tail).tag(prefix.isPublic()));
	}
	if (auto *leaf = std::get_if<TwineSpec::Leaf>(&t.data))
		return stamp(find_content(TwineNode::NO_PREFIX, leaf->s));
	const TwineSpec::Suffix &sfx = std::get<TwineSpec::Suffix>(t.data);
	return stamp(find_content((uint32_t)sfx.prefix.untag().raw(), sfx.tail).tag(sfx.prefix.isPublic()));
}

IdString TwinePool::add(TwineSpec t) {
	if (auto *ap = std::get_if<TwineSpec::AutoSuffix>(&t.data)) {
		IdString prefix = auto_prefix(ap->prefix);
		return stamp(intern((uint32_t)prefix.untag().raw(), ap->tail).tag(prefix.isPublic()));
	}
	if (auto *leaf = std::get_if<TwineSpec::Leaf>(&t.data))
		return stamp(intern(TwineNode::NO_PREFIX, leaf->s));
	const TwineSpec::Suffix &sfx = std::get<TwineSpec::Suffix>(t.data);
	return stamp(intern((uint32_t)sfx.prefix.untag().raw(), sfx.tail).tag(sfx.prefix.isPublic()));
}

IdString TwinePool::auto_prefix(const std::string *prefix) {
	auto it = auto_prefixes.find(prefix);
	if (it != auto_prefixes.end())
		return it->second;
	IdString ref = intern(TwineNode::NO_PREFIX, *prefix);
	auto_prefixes[prefix] = ref;
	return ref;
}

IdString TwinePool::add(IdString prefix, std::string_view tail) {
	return stamp(intern((uint32_t)prefix.untag().raw(), tail).tag(prefix.isPublic()));
}

IdString TwinePool::add(std::string s) {
	if (s.empty())
		return IdString::Null;
	auto [content, is_public] = twine_unescape(std::move(s));
	return stamp(intern(TwineNode::NO_PREFIX, content).tag(is_public));
}

IdString TwinePool::copy_from(const TwinePool& src, IdString ref) {
	if (ref == IdString::Null)
		return ref;

	bool is_public = ref.isPublic();
	IdString untagged = ref.untag();
	if (ID::is_static(untagged))
		return ref;
	const TwineNode& t = src[untagged];
	switch (t.kind()) {
	case TwineNode::Kind::Leaf:
		return stamp(intern(TwineNode::NO_PREFIX, t.text()).tag(is_public));
	case TwineNode::Kind::Suffix: {
		IdString prefix = copy_from(src, t.prefix());
		return stamp(intern((uint32_t)prefix.untag().raw(), t.text()).tag(is_public));
	}
	case TwineNode::Kind::Dead:
		break;
	}
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
	switch (t.kind()) {
	case TwineNode::Kind::Leaf:
		return stamp(find_content(TwineNode::NO_PREFIX, t.text()).tag(is_public));
	case TwineNode::Kind::Suffix: {
		IdString prefix = find_from(src, t.prefix());
		if (prefix == IdString::Null)
			return IdString::Null;
		return stamp(find_content((uint32_t)prefix.untag().raw(), t.text()).tag(is_public));
	}
	case TwineNode::Kind::Dead:
		break;
	}
	return IdString::Null;
}

std::string TwinePool::ref_token(IdString ref) const {
	return "#" + std::to_string((uint64_t)serial_) + ":"
		+ std::to_string((uint64_t)stamp(ref).bits());
}

IdString TwinePool::ref_from_token(std::string_view token) const {
	if (token.size() < 2 || token[0] != '#')
		return IdString::Null;
	size_t sep = token.find(':');
	if (sep == std::string_view::npos)
		return IdString::Null;
	size_t fields[2] = {0, 0};
	std::string_view parts[2] = {token.substr(1, sep - 1), token.substr(sep + 1)};
	for (int i = 0; i < 2; i++) {
		if (parts[i].empty())
			return IdString::Null;
		for (char c : parts[i]) {
			if (c < '0' || c > '9')
				return IdString::Null;
			fields[i] = fields[i] * 10 + (c - '0');
		}
	}
	if (fields[0] != serial_)
		return IdString::Null;
	IdString ref(fields[1]);
	if (ref == IdString::Null)
		return IdString::Null;
	return is_live(ref) ? ref : IdString::Null;
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
		switch (t.kind()) {
		case TwineNode::Kind::Suffix:
			push(t.text());
			cur = t.prefix();
			continue;
		case TwineNode::Kind::Leaf:
			push(t.text());
			break;
		case TwineNode::Kind::Dead:
			break;
		}
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

IdString TwinePool::prefix_of(IdString ref) const {
	const TwineNode &t = (*this)[ref];
	if (!t.is_suffix())
		return IdString::Null;
	return stamp(t.prefix().tag(ref.isPublic()));
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
			return ta.text().compare(tb.text());
		if (ta.is_suffix() && tb.is_suffix() && ta.prefix() == tb.prefix())
			return ta.text().compare(tb.text());
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
	switch (n.kind()) {
	case TwineNode::Kind::Dead:
		break;
	case TwineNode::Kind::Suffix:
		combine(s, n.prefix());
		[[fallthrough]];
	case TwineNode::Kind::Leaf:
		s.push(n.text());
		break;
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
	switch (n.kind()) {
	case TwineNode::Kind::Dead:
		return true;
	case TwineNode::Kind::Suffix:
		if (!consume(n.prefix(), sv)) return false;
		[[fallthrough]];
	case TwineNode::Kind::Leaf:
		if (!sv.starts_with(n.text())) return false;
		sv.remove_prefix(n.text().size());
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
