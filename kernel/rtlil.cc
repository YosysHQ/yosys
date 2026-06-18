/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include "kernel/macc.h"
#include "kernel/newcelltypes.h"
#include "kernel/binding.h"
#include "kernel/sigtools.h"
#include "kernel/unstable/patch.h"
#include "kernel/threading.h"
#include "frontends/verilog/verilog_frontend.h"
#include "frontends/verilog/preproc.h"
#include "backends/rtlil/rtlil_backend.h"

#include <string.h>
#include <algorithm>
#include <charconv>
#include <optional>
#include <string_view>
#include <sstream>

YOSYS_NAMESPACE_BEGIN

bool IdString::destruct_guard_ok = false;
IdString::destruct_guard_t IdString::destruct_guard;
std::vector<IdString::Storage> IdString::global_id_storage_;
std::unordered_map<std::string_view, int> IdString::global_id_index_;
std::unordered_map<int, IdString::AutoidxStorage> IdString::global_autoidx_id_storage_;
std::unordered_map<int, int> IdString::global_refcount_storage_;
std::vector<int> IdString::global_free_idx_list_;

static void populate(std::string_view name)
{
	if (name[1] == '$') {
		// Skip prepended '\'
		name = name.substr(1);
	}
	IdString::global_id_index_.insert({name, GetSize(IdString::global_id_storage_)});
	IdString::global_id_storage_.push_back({const_cast<char*>(name.data()), GetSize(name)});
}

void IdString::prepopulate()
{
	int size = static_cast<short>(RTLIL::StaticId::STATIC_ID_END);
	global_id_storage_.reserve(size);
	global_id_index_.reserve(size);
	IdString::global_id_index_.insert({"", 0});
	IdString::global_id_storage_.push_back({const_cast<char*>(""), 0});
#define X(N) populate("\\" #N);
#include "kernel/constids.inc"
#undef X
}

static std::optional<int> parse_autoidx(std::string_view v)
{
	// autoidx values can never be <= 0, so there can never be a leading 0 digit.
	if (v.empty() || v[0] == '0')
		return std::nullopt;
	for (char ch : v) {
		if (ch < '0' || ch > '9')
			return std::nullopt;
	}
	int p_autoidx;
	if (std::from_chars(v.data(), v.data() + v.size(), p_autoidx).ec != std::errc())
		return std::nullopt;
	return p_autoidx;
}

int IdString::really_insert(std::string_view p, std::unordered_map<std::string_view, int>::iterator &it)
{
	ensure_prepopulated();

	log_assert(p[0] == '$' || p[0] == '\\');
	for (char ch : p)
		if ((unsigned)ch <= (unsigned)' ')
			log_error("Found control character or space (0x%02x) in string '%s' which is not allowed in RTLIL identifiers\n", ch, std::string(p).c_str());

	if (p.substr(0, 6) == "$auto$") {
		size_t autoidx_pos = p.find_last_of('$') + 1;
		std::optional<int> p_autoidx = parse_autoidx(p.substr(autoidx_pos));
		if (p_autoidx.has_value()) {
			auto autoidx_it = global_autoidx_id_storage_.find(-*p_autoidx);
			if (autoidx_it != global_autoidx_id_storage_.end() &&
					p.substr(0, autoidx_pos) == *autoidx_it->second.prefix)
				return -*p_autoidx;
			// Ensure NEW_ID/NEW_ID_SUFFIX will not create collisions with the ID
			// we're about to create.
			autoidx.ensure_at_least(*p_autoidx + 1);
		}
	}

	if (global_free_idx_list_.empty()) {
		log_assert(global_id_storage_.size() < 0x40000000);
		global_free_idx_list_.push_back(global_id_storage_.size());
		global_id_storage_.push_back({nullptr, 0});
	}

	int idx = global_free_idx_list_.back();
	global_free_idx_list_.pop_back();
	char* buf = static_cast<char*>(malloc(p.size() + 1));
	memcpy(buf, p.data(), p.size());
	buf[p.size()] = 0;
	global_id_storage_.at(idx) = {buf, GetSize(p)};
	global_id_index_.insert(it, {std::string_view(buf, p.size()), idx});

	if (yosys_xtrace) {
		log("#X# New IdString '%s' with index %d.\n", global_id_storage_.at(idx).buf, idx);
		log_backtrace("-X- ", yosys_xtrace-1);
	}

#ifdef YOSYS_XTRACE_GET_PUT
	if (yosys_xtrace)
		log("#X# GET-BY-NAME '%s' (index %d, refcount %u)\n", global_id_storage_.at(idx).buf, idx, refcount(idx));
#endif
	return idx;
}

static constexpr bool check_well_known_id_order()
{
	int size = sizeof(IdTable) / sizeof(IdTable[0]);
	for (int i = 1; i < size; ++i)
		if (IdTable[i - 1].name >= IdTable[i].name)
			return false;
	return true;
}

// Ensure the statically allocated IdStrings in kernel/constids.inc are unique
// and in sorted ascii order, as required by the ID macro.
static_assert(check_well_known_id_order());

constexpr int STATIC_ID_END = static_cast<int>(RTLIL::StaticId::STATIC_ID_END);

struct IdStringCollector {
	IdStringCollector(std::vector<MonotonicFlag> &live_ids)
			: live_ids(live_ids) {}

	void trace(TwineRef id) {
		// live_twines.push_back(id );
		// TODO
	}
	void trace(IdString id) {
		if (id.index_ >= STATIC_ID_END)
			live_ids[id.index_ - STATIC_ID_END].set();
		else if (id.index_ < 0)
			live_autoidx_ids.push_back(id.index_);
	}
	template <typename T> void trace(const T* v) {
		trace(*v);
	}
	template <typename V> void trace(const std::vector<V> &v) {
		for (const auto &element : v)
			trace(element);
	}
	template <typename K> void trace(const pool<K> &p) {
		for (const auto &element : p)
			trace(element);
	}
	template <typename K, typename V> void trace(const dict<K, V> &d) {
		for (const auto &[key, value] : d) {
			trace(key);
			trace(value);
		}
	}
	template <typename K, typename V> void trace_keys(const dict<K, V> &d) {
		for (const auto &[key, value] : d) {
			trace(key);
		}
	}
	template <typename K, typename V> void trace_values(const dict<K, V> &d) {
		for (const auto &[key, value] : d) {
			trace(value);
		}
	}
	template <typename K> void trace(const idict<K> &d) {
		for (const auto &element : d)
			trace(element);
	}

	void trace(const RTLIL::Selection &selection_var) {
		trace(selection_var.selected_modules);
		trace(selection_var.selected_members);
	}
	void trace_named(const RTLIL::AttrObject &named) {
		trace_keys(named.attributes);
		if (named.meta_)
			trace(named.meta_->name);
	}
	void trace(const RTLIL::Wire &wire) {
		trace_named(wire);
		if (wire.known_driver())
			trace(wire.driverPort());
	}
	void trace(const RTLIL::Cell &cell) {
		trace_named(cell);
		trace(cell.type_impl);
		trace_keys(cell.connections_);
		trace_keys(cell.parameters);
	}
	void trace(const RTLIL::Memory &mem) {
		trace_named(mem);
	}
	void trace(const RTLIL::Process &proc) {
		trace_named(proc);
		trace(proc.root_case);
		trace(proc.syncs);
	}
	void trace(const RTLIL::CaseRule &rule) {
		trace_keys(rule.attributes);
		trace(rule.switches);
	}
	void trace(const RTLIL::SwitchRule &rule) {
		trace_keys(rule.attributes);
		trace(rule.cases);
	}
	void trace(const RTLIL::SyncRule &rule) {
		trace(rule.mem_write_actions);
	}
	void trace(const RTLIL::MemWriteAction &action) {
		trace_keys(action.attributes);
		trace(action.memid);
	}

	std::vector<MonotonicFlag> &live_ids;
	// std::vector<MonotonicFlag> &live_twines;
	std::vector<int> live_autoidx_ids;
};

int64_t RTLIL::OwningIdString::gc_ns;
int RTLIL::OwningIdString::gc_count;

void RTLIL::OwningIdString::collect_garbage()
{
	int64_t start = PerformanceTimer::query();

	int pool_size = 0;
	for (auto &[idx, design] : *RTLIL::Design::get_all_designs())
		for (RTLIL::Module *module : design->modules())
			pool_size = std::max(pool_size, ThreadPool::work_pool_size(0, module->cells_size(), 1000));
	ParallelDispatchThreadPool thread_pool(pool_size);

	int size = GetSize(global_id_storage_);
	std::vector<MonotonicFlag> live_ids(size - STATIC_ID_END);
	std::vector<IdStringCollector> collectors;
	int num_threads = thread_pool.num_threads();
	collectors.reserve(num_threads);
	for (int i = 0; i < num_threads; ++i)
		collectors.emplace_back(live_ids);

	// TODO
	for (auto &[idx, design] : *RTLIL::Design::get_all_designs()) {
		for (RTLIL::Module *module : design->modules()) {
			collectors[0].trace_keys(module->attributes);
			// collectors[0].trace(TwineRef(module->name));
			// TODO
			ParallelDispatchThreadPool::Subpool subpool(thread_pool, ThreadPool::work_pool_size(0, module->cells_size(), 1000));
			subpool.run([&collectors, module](const ParallelDispatchThreadPool::RunCtx &ctx) {
				for (int i : ctx.item_range(module->cells_size()))
					collectors[ctx.thread_num].trace(module->cell_at(i));
				for (int i : ctx.item_range(module->wires_size()))
					collectors[ctx.thread_num].trace(module->wire_at(i));
			});
			collectors[0].trace(module->avail_parameters);
			collectors[0].trace_keys(module->parameter_default_values);
			collectors[0].trace_values(module->memories);
			collectors[0].trace_values(module->processes);
		}
		collectors[0].trace(design->selection_vars);
	}

	ShardedVector<int> free_ids(thread_pool);
	thread_pool.run([&live_ids, size, &free_ids](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(size - STATIC_ID_END)) {
			int index = i + STATIC_ID_END;
			IdString::Storage &storage = global_id_storage_.at(index);
			if (storage.buf == nullptr)
				continue;
			if (live_ids[i].load())
				continue;
			if (global_refcount_storage_.find(index) != global_refcount_storage_.end())
				continue;
			free_ids.insert(ctx, index);
		}
	});
	for (int i : free_ids) {
		IdString::Storage &storage = global_id_storage_.at(i);
		if (yosys_xtrace) {
			log("#X# Removed IdString '%s' with index %d.\n", storage.buf, i);
			log_backtrace("-X- ", yosys_xtrace-1);
		}

		global_id_index_.erase(std::string_view(storage.buf, storage.size));
		free(storage.buf);
		storage = {nullptr, 0};
		global_free_idx_list_.push_back(i);
	}

	std::unordered_set<int> live_autoidx_ids;
	for (IdStringCollector &collector : collectors)
		for (int id : collector.live_autoidx_ids)
			live_autoidx_ids.insert(id);

	for (auto it = global_autoidx_id_storage_.begin(); it != global_autoidx_id_storage_.end();) {
		if (live_autoidx_ids.find(it->first) != live_autoidx_ids.end()) {
			++it;
			continue;
		}
		if (global_refcount_storage_.find(it->first) != global_refcount_storage_.end()) {
			++it;
			continue;
		}
		it = global_autoidx_id_storage_.erase(it);
	}

	int64_t time_ns = PerformanceTimer::query() - start;
	Pass::subtract_from_current_runtime_ns(time_ns);
	gc_ns += time_ns;
	++gc_count;
}

dict<std::string, std::string> RTLIL::constpad;

const pool<TwineRef> &RTLIL::builtin_ff_cell_types() {
	static const pool<TwineRef> res = []() {
		pool<TwineRef> r;
		for (size_t i = 0; i < StaticCellTypes::builder.count; i++) {
			auto &cell = StaticCellTypes::builder.cells[i];
			if (cell.features.is_ff)
				r.insert(cell.type);
		}
		return r;
	}();
	return res;
}

#define check(condition) log_assert(condition && "malformed Const union")

const Const::bitvectype& Const::get_bits() const {
	check(is_bits());
	return *get_if_bits();
}

const std::string& Const::get_str() const {
	check(is_str());
	return *get_if_str();
}

Const::bitvectype& Const::get_bits() {
	check(is_bits());
	return *get_if_bits();
}

std::string& Const::get_str() {
	check(is_str());
	return *get_if_str();
}

RTLIL::Const::Const(std::string str)
{
	flags = RTLIL::CONST_FLAG_STRING;
	new ((void*)&str_) std::string(std::move(str));
	tag = backing_tag::string;
}

RTLIL::Const::Const(long long val) // default width 32
{
	flags = RTLIL::CONST_FLAG_NONE;
	char bytes[] = {
		(char)(val >> 24), (char)(val >> 16), (char)(val >> 8), (char)val
	};
	new ((void*)&str_) std::string(bytes, 4);
	tag = backing_tag::string;
}

RTLIL::Const::Const(long long val, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	if ((width & 7) == 0) {
		new ((void*)&str_) std::string();
		tag = backing_tag::string;
		std::string& str = get_str();
		int bytes = width >> 3;
		signed char sign_byte = val < 0 ? -1 : 0;
		str.resize(bytes, sign_byte);
		bytes = std::min<int>(bytes, sizeof(val));
		for (int i = 0; i < bytes; i++) {
			str[str.size() - 1 - i] = val;
			val = val >> 8;
		}
		return;
	}

	new ((void*)&bits_) bitvectype();
	tag = backing_tag::bits;
	bitvectype& bv = get_bits();
	bv.reserve(width);
	for (int i = 0; i < width; i++) {
		bv.push_back((val & 1) != 0 ? State::S1 : State::S0);
		val = val >> 1;
	}
}

RTLIL::Const::Const(RTLIL::State bit, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	new ((void*)&bits_) bitvectype();
	tag = backing_tag::bits;
	bitvectype& bv = get_bits();
	bv.reserve(width);
	for (int i = 0; i < width; i++)
		bv.push_back(bit);
}

RTLIL::Const::Const(const std::vector<bool> &bits)
{
	flags = RTLIL::CONST_FLAG_NONE;
	new ((void*)&bits_) bitvectype();
	tag = backing_tag::bits;
	bitvectype& bv = get_bits();
	bv.reserve(bits.size());
	for (const auto &b : bits)
		bv.emplace_back(b ? State::S1 : State::S0);
}

RTLIL::Const::Const(const RTLIL::Const &other) {
	tag = other.tag;
	flags = other.flags;
	if (is_str())
		new ((void*)&str_) std::string(other.get_str());
	else if (is_bits())
		new ((void*)&bits_) bitvectype(other.get_bits());
	else
		check(false);
}

RTLIL::Const::Const(RTLIL::Const &&other) {
	tag = other.tag;
	flags = other.flags;
	if (is_str())
		new ((void*)&str_) std::string(std::move(other.get_str()));
	else if (is_bits())
		new ((void*)&bits_) bitvectype(std::move(other.get_bits()));
	else
		check(false);
}

RTLIL::Const &RTLIL::Const::operator =(const RTLIL::Const &other) {
	flags = other.flags;
	if (other.is_str()) {
		if (!is_str()) {
			// sketchy zone
			check(is_bits());
			bits_.~bitvectype();
			(void)new ((void*)&str_) std::string();
		}
		tag = other.tag;
		get_str() = other.get_str();
	} else if (other.is_bits()) {
		if (!is_bits()) {
			// sketchy zone
			check(is_str());
			str_.~string();
			(void)new ((void*)&bits_) bitvectype();
		}
		tag = other.tag;
		get_bits() = other.get_bits();
	} else {
		check(false);
	}
	return *this;
}

RTLIL::Const::~Const() {
	if (is_bits())
		bits_.~bitvectype();
	else if (is_str())
		str_.~string();
	else
		check(false);
}

bool RTLIL::Const::operator<(const RTLIL::Const &other) const
{
	if (size() != other.size())
		return size() < other.size();

	for (int i = 0; i < size(); i++)
		if ((*this)[i] != other[i])
			return (*this)[i] < other[i];

	return false;
}

bool RTLIL::Const::operator ==(const RTLIL::Const &other) const
{
	if (is_str() && other.is_str())
		return get_str() == other.get_str();
	if (is_bits() && other.is_bits())
		return get_bits() == other.get_bits();

	if (size() != other.size())
		return false;

	for (int i = 0; i < size(); i++)
	if ((*this)[i] != other[i])
		return false;

	return true;
}

bool RTLIL::Const::operator !=(const RTLIL::Const &other) const
{
	return !(*this == other);
}

std::vector<RTLIL::State>& RTLIL::Const::bits_internal()
{
	bitvectorize_internal();
	return get_bits();
}

std::vector<RTLIL::State> RTLIL::Const::to_bits() const
{
	std::vector<State> v;
	for (auto bit : *this)
		v.push_back(bit);
	return v;
}

bool RTLIL::Const::as_bool() const
{
	if (is_str()) {
		for (char ch : get_str())
			if (ch != 0)
				return true;
		return false;
	}

	const bitvectype& bv = get_bits();
	for (size_t i = 0; i < bv.size(); i++)
		if (bv[i] == State::S1)
			return true;
	return false;
}

int RTLIL::Const::as_int(bool is_signed) const
{
	int32_t ret = 0;
	if (const std::string *s = get_if_str()) {
		int size = GetSize(*s);
		// Ignore any bytes after the first 4 since bits beyond 32 are truncated.
		for (int i = std::min(4, size); i > 0; i--)
			ret |= static_cast<unsigned char>((*s)[size - i]) << ((i - 1) * 8);
		// If is_signed and the string is shorter than 4 bytes then apply sign extension.
		if (is_signed && size > 0 && size < 4 && ((*s)[0] & 0x80))
			ret |= UINT32_MAX << size*8;
		return ret;
	}

	const bitvectype& bv = get_bits();
	int significant_bits = std::min(GetSize(bv), 32);
	for (int i = 0; i < significant_bits; i++)
		if (bv[i] == State::S1)
			ret |= 1 << i;
	if (is_signed && significant_bits > 0 && significant_bits < 32 && bv.back() == State::S1 )
		ret |= UINT32_MAX << significant_bits;
	return ret;
}

bool RTLIL::Const::convertible_to_int(bool is_signed) const
{
	auto size = get_min_size(is_signed);

	if (size < 0)
		return false;

	// If it fits in 31 bits it is definitely convertible
	if (size <= 31)
		return true;

	// If it fits in 32 bits, it is convertible if signed or if unsigned and the
	// leading bit is not 1
	if (size == 32) {
		if (is_signed)
			return true;
		return back() != State::S1;
	}

	return false;
}

std::optional<int> RTLIL::Const::try_as_int(bool is_signed) const
{
	if (!convertible_to_int(is_signed))
		return std::nullopt;
	return as_int(is_signed);
}

int RTLIL::Const::as_int_saturating(bool is_signed) const
{
	if (!convertible_to_int(is_signed)) {
		if (!is_signed)
			return std::numeric_limits<int>::max();

		const auto min_size = get_min_size(is_signed);
		log_assert(min_size > 0);
		const auto neg = (*this)[min_size - 1];
		return neg ? std::numeric_limits<int>::min() : std::numeric_limits<int>::max();
	}
	return as_int(is_signed);
}

int RTLIL::Const::get_min_size(bool is_signed) const
{
	if (empty()) return 0;

	// back to front (MSB to LSB)
	RTLIL::State leading_bit;
	if (is_signed)
		leading_bit = (back() == RTLIL::State::Sx) ? RTLIL::State::S0 : back();
	else
		leading_bit = RTLIL::State::S0;

	auto idx = size();
	while (idx > 0 && (*this)[idx -1] == leading_bit) {
		idx--;
	}

	// signed needs one leading bit
	if (is_signed && idx < size()) {
		idx++;
	}
	// must be at least one bit
	return (idx == 0) ? 1 : idx;
}

void RTLIL::Const::compress(bool is_signed)
{
	auto idx = get_min_size(is_signed);
	resize(idx, RTLIL::State::S0);
}

std::optional<int> RTLIL::Const::as_int_compress(bool is_signed) const
{
	return try_as_int(is_signed);
}

std::string RTLIL::Const::as_string(const char* any) const
{
	int sz = size();
	std::string ret;
	ret.reserve(sz);
	for (int i = sz - 1; i >= 0; --i)
		switch ((*this)[i]) {
			case S0: ret.push_back('0'); break;
			case S1: ret.push_back('1'); break;
			case Sx: ret.push_back('x'); break;
			case Sz: ret.push_back('z'); break;
			case Sa: ret += any; break;
			case Sm: ret.push_back('m'); break;
		}
	return ret;
}

RTLIL::Const RTLIL::Const::from_string(const std::string &str)
{
	Const c;
	bitvectype& bv = c.get_bits();
	bv.reserve(str.size());
	for (auto it = str.rbegin(); it != str.rend(); it++)
		switch (*it) {
			case '0': bv.push_back(State::S0); break;
			case '1': bv.push_back(State::S1); break;
			case 'x': bv.push_back(State::Sx); break;
			case 'z': bv.push_back(State::Sz); break;
			case 'm': bv.push_back(State::Sm); break;
			default: bv.push_back(State::Sa);
		}
	return c;
}

std::string RTLIL::Const::decode_string() const
{
	if (auto str = get_if_str())
		return *str;

	const bitvectype& bv = get_bits();
	const int n = GetSize(bv);
	const int n_over_8 = n / 8;
	std::string s;
	s.reserve(n_over_8);
	int i = n_over_8 * 8;
	if (i < n) {
		char ch = 0;
		for (int j = 0; j < (n - i); j++) {
			if (bv[i + j] == RTLIL::State::S1) {
				ch |= 1 << j;
			}
		}
		if (ch != 0)
			s.append({ch});
	}
	i -= 8;
	for (; i >= 0; i -= 8) {
		char ch = 0;
		for (int j = 0; j < 8; j++) {
			if (bv[i + j] == RTLIL::State::S1) {
				ch |= 1 << j;
			}
		}
		if (ch != 0)
			s.append({ch});
	}
	return s;
}

int RTLIL::Const::size() const {
	if (is_str())
		return 8 * str_.size();
	else {
		check(is_bits());
		return bits_.size();
	}
}

bool RTLIL::Const::empty() const {
	if (is_str())
		return str_.empty();
	else {
		check(is_bits());
		return bits_.empty();
	}
}

void RTLIL::Const::bitvectorize_internal() {
	if (tag == backing_tag::bits)
		return;

	check(is_str());

	bitvectype new_bits;

	new_bits.reserve(str_.size() * 8);
	for (int i = str_.size() - 1; i >= 0; i--) {
		unsigned char ch = str_[i];
		for (int j = 0; j < 8; j++) {
			new_bits.push_back((ch & 1) != 0 ? State::S1 : State::S0);
			ch = ch >> 1;
		}
	}

	{
		// sketchy zone
		str_.~string();
		(void)new ((void*)&bits_) bitvectype(std::move(new_bits));
		tag = backing_tag::bits;
	}
}

void RTLIL::Const::append(const RTLIL::Const &other) {
	bitvectorize_internal();
	bitvectype& bv = get_bits();
	bv.insert(bv.end(), other.begin(), other.end());
}

RTLIL::State RTLIL::Const::const_iterator::operator*() const {
	if (auto bv = parent->get_if_bits())
		return (*bv)[idx];

	int char_idx = parent->get_str().size() - idx / 8 - 1;
	bool bit = (parent->get_str()[char_idx] & (1 << (idx % 8)));
	return bit ? State::S1 : State::S0;
}

bool RTLIL::Const::is_fully_zero() const
{
	if (auto str = get_if_str()) {
		for (char ch : *str)
			if (ch != 0)
				return false;
		return true;
	}

	const bitvectype& bv = get_bits();

	for (const auto &bit : bv)
		if (bit != RTLIL::State::S0)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_ones() const
{
	if (auto str = get_if_str()) {
		for (char ch : *str)
			if (ch != (char)0xff)
				return false;
		return true;
	}

	const bitvectype& bv = get_bits();
	for (const auto &bit : bv)
		if (bit != RTLIL::State::S1)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_def() const
{
	if (is_str())
		return true;

	const bitvectype& bv = get_bits();
	for (const auto &bit : bv)
		if (bit != RTLIL::State::S0 && bit != RTLIL::State::S1)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_undef() const
{
	if (auto str = get_if_str())
		return str->empty();

	const bitvectype& bv = get_bits();
	for (const auto &bit : bv)
		if (bit != RTLIL::State::Sx && bit != RTLIL::State::Sz)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_undef_x_only() const
{
	if (auto str = get_if_str())
		return str->empty();

	const bitvectype& bv = get_bits();
	for (const auto &bit : bv)
		if (bit != RTLIL::State::Sx)
			return false;

	return true;
}

bool RTLIL::Const::is_onehot(int *pos) const
{
	bool found = false;
	int size = GetSize(*this);
	for (int i = 0; i < size; i++) {
		State bit = (*this)[i];
		if (bit != RTLIL::State::S0 && bit != RTLIL::State::S1)
			return false;
		if (bit == RTLIL::State::S1) {
			if (found)
				return false;
			if (pos)
				*pos = i;
			found = true;
		}
	}
	return found;
}

Hasher RTLIL::Const::hash_into(Hasher h) const
{
	if (auto str = get_if_str())
		return hashlib::hash_ops<std::string>::hash_into(*str, h);

	// If the bits are all 0/1, hash packed bits using the string hash.
	// Otherwise hash the leading packed bits with the rest of the bits individually.
	const bitvectype &bv = get_bits();
	int size = GetSize(bv);
	std::string packed;
	int packed_size = (size + 7) >> 3;
	packed.resize(packed_size, 0);
	for (int bi = 0; bi < packed_size; ++bi) {
		char ch = 0;
		int end = std::min((bi + 1)*8, size);
		for (int i = bi*8; i < end; ++i) {
			RTLIL::State b = bv[i];
			if (b > RTLIL::State::S1) {
				// Hash the packed bits we've seen so far, plus the remaining bits.
				h = hashlib::hash_ops<std::string>::hash_into(packed, h);
				h = hashlib::hash_ops<char>::hash_into(ch, h);
				for (; i < size; ++i) {
					h = hashlib::hash_ops<RTLIL::State>::hash_into(bv[i], h);
				}
				h.eat(size);
				return h;
			}
			ch |= static_cast<int>(b) << (i & 7);
		}
		packed[packed_size - 1 - bi] = ch;
	}
	return hashlib::hash_ops<std::string>::hash_into(packed, h);
}

RTLIL::Const RTLIL::Const::extract(int offset, int len, RTLIL::State padding) const {
	bitvectype ret_bv;
	ret_bv.reserve(len);
	for (int i = offset; i < offset + len; i++)
		ret_bv.push_back(i < GetSize(*this) ? (*this)[i] : padding);
	return RTLIL::Const(ret_bv);
}
#undef check /* check(condition) for Const */

bool RTLIL::AttrObject::has_attribute(IdString id) const
{
	if (id == ID::src)
		return meta_ != nullptr && meta_->src != Twine::Null;
	return attributes.count(id);
}

void RTLIL::AttrObject::set_bool_attribute(IdString id, bool value)
{
	log_assert(id != ID::src);
	if (value)
		attributes[id] = RTLIL::Const(1);
	else
		attributes.erase(id);
}

bool RTLIL::AttrObject::get_bool_attribute(IdString id) const
{
	if (id == ID::src)
		return meta_ != nullptr && meta_->src != Twine::Null;
	const auto it = attributes.find(id);
	if (it == attributes.end())
		return false;
	return it->second.as_bool();
}

void RTLIL::AttrObject::set_string_attribute(IdString id, string value)
{
	// ID::src on the base AttrObject is not routable here because the base
	// has no Design context — callers needing string-form src must go
	// through the subtype helper (Cell::set_src_attribute / Wire::… / …)
	// which derives the design from context.
	log_assert(id != ID::src && "set_string_attribute(ID::src,...) on AttrObject base; use the subtype helper");
	if (value.empty())
		attributes.erase(id);
	else
		attributes[id] = value;
}

string RTLIL::AttrObject::get_string_attribute(IdString id) const
{
	// ID::src is not in the dict — callers must use the subtype helper.
	log_assert(id != ID::src && "get_string_attribute(ID::src) on AttrObject base; use the subtype helper");
	std::string value;
	const auto it = attributes.find(id);
	if (it != attributes.end())
		value = it->second.decode_string();
	return value;
}

void RTLIL::Design::obj_set_src_id(RTLIL::AttrObject *obj, TwineRef id)
{
	if (obj->meta_ == nullptr) {
		if (id == Twine::Null)
			return;
		obj->meta_ = alloc_obj_meta();
	}
	ObjMeta &m = *obj->meta_;
	if (m.src == id)
		return;
	// if (m.src != Twine::Null)
	// 	twines.release(m.src);
	m.src = id;
	// if (m.src != Twine::Null)
	// 	twines.retain(m.src);
	if (m.src == Twine::Null && m.name == Twine::Null) {
		free_obj_meta(obj->meta_);
		obj->meta_ = nullptr;
	}
}

void RTLIL::Design::obj_release_src(RTLIL::AttrObject *obj)
{
	if (obj->meta_ == nullptr)
		return;
	ObjMeta &m = *obj->meta_;
	if (m.src != Twine::Null) {
		// twines.release(m.src);
		m.src = Twine::Null;
	}
	if (m.name == Twine::Null) {
		free_obj_meta(obj->meta_);
		obj->meta_ = nullptr;
	}
}

// void RTLIL::Design::obj_set_name(RTLIL::AttrObject *obj, TwineRef name)
// {
// 	if (obj->meta_ == nullptr) {
// 		if (name.empty())
// 			return;
// 		obj->meta_ = alloc_obj_meta();
// 	}
// 	ObjMeta &m = *obj->meta_;
// 	m.name = name;
// 	if (m.name.empty() && m.src == Twine::Null && m.name == Twine::Null) {
// 		free_obj_meta(obj->meta_);
// 		obj->meta_ = nullptr;
// 	}
// }

// void RTLIL::Design::obj_release_name(RTLIL::AttrObject *obj)
// {
// 	if (obj->meta_ == nullptr)
// 		return;
// 	ObjMeta &m = *obj->meta_;
// 	m.name = Twine::Null;
// 	if (m.src == Twine::Null && m.name == Twine::Null) {
// 		free_obj_meta(obj->meta_);
// 		obj->meta_ = nullptr;
// 	}
// }

// void RTLIL::Design::obj_set_name(RTLIL::AttrObject *obj, TwineRef id)
// {
// 	if (obj->meta_ == nullptr) {
// 		if (id == Twine::Null)
// 			return;
// 		obj->meta_ = alloc_obj_meta();
// 	}
// 	ObjMeta &m = *obj->meta_;
// 	if (m.name == id)
// 		return;
// 	// if (m.name != Twine::Null)
// 	// 	twines.release(m.name);
// 	m.name = id;
// 	// if (m.name != Twine::Null)
// 	// 	twines.retain(m.name);
// 	if (m.name == Twine::Null && m.src == Twine::Null) {
// 		free_obj_meta(obj->meta_);
// 		obj->meta_ = nullptr;
// 	}
// }

// void RTLIL::Design::obj_release_name(RTLIL::AttrObject *obj)
// {
// 	if (obj->meta_ == nullptr)
// 		return;
// 	ObjMeta &m = *obj->meta_;
// 	if (m.name != Twine::Null) {
// 		m.name = Twine::Null;
// 	}
// 	if (m.src == Twine::Null && m.name == Twine::Null) {
// 		free_obj_meta(obj->meta_);
// 		obj->meta_ = nullptr;
// 	}
// }

void RTLIL::Design::set_src_attribute(RTLIL::AttrObject *obj, TwineRef src)
{
	obj_set_src_id(obj, src);
}

std::string RTLIL::Design::get_src_attribute(const RTLIL::AttrObject *obj) const
{
	return twines.flat_string(obj_src_id(obj));
}

void RTLIL::Design::adopt_src_from(RTLIL::AttrObject *obj, const RTLIL::AttrObject *source)
{
	adopt_src_from(obj, source, &twines);
}

void RTLIL::Design::adopt_src_from(RTLIL::AttrObject *obj,
		const RTLIL::AttrObject *source, const TwinePool *src_pool)
{
	(void)src_pool;
	if (!source || source->meta_ == nullptr) {
		obj_set_src_id(obj, Twine::Null);
		return;
	}
	// Same-pool semantics: source's meta-vector entry is meaningful in
	// our pool. Cross-pool adoption goes through copy_src_into directly
	// (taking a src Design*), since AttrObject is not polymorphic and
	// we can't downcast to recover the source design from here.
	TwineRef source_id = obj_src_id(source);
	obj_set_src_id(obj, source_id);
}

void RTLIL::Design::absorb_attrs(RTLIL::AttrObject *obj, dict<IdString, RTLIL::Const> &&buf)
{
	auto it = buf.find(ID::src);
	if (it != buf.end()) {
		if (it->second.flags & RTLIL::CONST_FLAG_STRING)
			obj_set_src_id(obj, twines.add(Twine{it->second.decode_string()}));
		buf.erase(it);
	}
	obj->attributes = std::move(buf);
}

// Cross-design src transfer. Source is in `src_design`, dst in this design.
// Both AttrObjects must have their meta_idx_ resolvable through the
// respective designs.
namespace {
	void copy_src_into(const RTLIL::AttrObject *src, const RTLIL::Design *src_design,
			RTLIL::AttrObject *dst, RTLIL::Design *dst_design)
	{
		if (!src || !src_design || !dst_design)
			return;
		TwineRef src_id = src_design->obj_src_id(src);
		if (src_id == Twine::Null) {
			dst_design->obj_set_src_id(dst, Twine::Null);
			return;
		}
		if (src_design == dst_design) {
			dst_design->obj_set_src_id(dst, src_id);
			return;
		}
		TwineRef new_id = dst_design->twines.copy_from(src_design->twines, src_id);
		dst_design->obj_set_src_id(dst, new_id);
	}
}

RTLIL::ObjMeta *RTLIL::Design::alloc_obj_meta()
{
	if (!obj_meta_free_.empty()) {
		ObjMeta *m = obj_meta_free_.back();
		obj_meta_free_.pop_back();
		*m = ObjMeta{};
		return m;
	}
	obj_meta_storage_.emplace_back();
	return &obj_meta_storage_.back();
}

void RTLIL::Design::free_obj_meta(RTLIL::ObjMeta *m)
{
	log_assert(m != nullptr);
	log_assert(m->src == Twine::Null);
	log_assert(m->name == Twine::Null);
	obj_meta_free_.push_back(m);
}

void RTLIL::Design::merge_src(RTLIL::AttrObject *target, const RTLIL::AttrObject *source)
{
	std::vector<TwineRef> ids;
	TwineRef tgt_id = obj_src_id(target);
	if (tgt_id != Twine::Null)
		ids.push_back(tgt_id);
	if (source) {
		TwineRef src_id = obj_src_id(source);
		if (src_id != Twine::Null)
			ids.push_back(src_id);
	}
	if (ids.empty())
		return;
	TwineRef merged = twines.concat(std::span<const TwineRef>{ids});
	obj_set_src_id(target, merged);
}

void RTLIL::Design::merge_src(RTLIL::AttrObject *target, const pool<std::string> &leaves)
{
	std::vector<TwineRef> ids;
	TwineRef tgt_id = obj_src_id(target);
	if (tgt_id != Twine::Null)
		ids.push_back(tgt_id);
	for (const auto &leaf : leaves) {
		if (leaf.empty())
			continue;
		ids.push_back(twines.add(Twine{leaf}));
	}
	if (ids.empty())
		return;
	TwineRef merged = twines.concat(std::span<const TwineRef>{ids});
	obj_set_src_id(target, merged);
}

namespace {
	// Walks every AttrObject in the design and invokes `visit(obj)`.
	template<typename F>
	void walk_attr_objects(RTLIL::Design *design, F visit) {
		for (auto &[_, module] : design->modules_) {
			visit(module);
			for (auto &[_, wire] : module->wires_)
				visit(wire);
			for (auto &[_, mem] : module->memories)
				visit(mem);
			for (auto &[_, cell] : module->cells_)
				visit(cell);
			for (auto &[_, process] : module->processes) {
				visit(process);
				// Walk the process's switch/case tree.
				std::vector<RTLIL::CaseRule*> case_stack{&process->root_case};
				while (!case_stack.empty()) {
					RTLIL::CaseRule *cs = case_stack.back();
					case_stack.pop_back();
					visit(cs);
					for (auto *sw : cs->switches) {
						visit(sw);
						for (auto *case_ : sw->cases)
							case_stack.push_back(case_);
					}
				}
				for (auto *sync : process->syncs)
					for (auto &mwa : sync->mem_write_actions)
						visit(&mwa);
			}
		}
	}
}

int64_t twine_gc_ns;
int twine_gc_count;

size_t RTLIL::Design::gc_twines()
{
	int64_t start = PerformanceTimer::query();
	// Mark phase: gather every TwineRef stored on a live object as a root.
	// TwinePool::gc traces each root's concat/suffix children transitively.
	pool<TwineRef> live;
	auto root = [&](TwineRef ref) {
		if (ref != Twine::Null)
			live.insert(ref);
	};

	walk_attr_objects(this, [&](const RTLIL::AttrObject *obj) {
		if (!obj->meta_)
			return;
		root(obj->meta_->src);
		root(obj->meta_->name);
	});

	for (auto &[_, module] : modules_) {
		for (auto &[_, wire] : module->wires_)
			if (wire->known_driver())
				root(wire->driverPort());
		for (auto &[_, cell] : module->cells_) {
			root(cell->type.ref());
			for (auto &conn : cell->connections())
				root(conn.first);
		}
	}

	for (auto &[_, sel] : selection_vars) {
		for (TwineRef m : sel.selected_modules)
			root(m);
		for (auto &[m, members] : sel.selected_members) {
			root(m);
			for (TwineRef member : members)
				root(member);
		}
	}

	// Sweep: backing refs are stable, so survivors need no remapping.
	size_t erased = twines.gc(live);

	int64_t time_ns = PerformanceTimer::query() - start;
	Pass::subtract_from_current_runtime_ns(time_ns);
	twine_gc_ns += time_ns;
	++twine_gc_count;
	return erased;
}

pool<std::string> RTLIL::Design::src_leaves(const RTLIL::AttrObject *obj) const
{
	pool<std::string> result;
	TwineRef id = obj_src_id(obj);
	if (id == Twine::Null)
		return result;
	const TwinePool *pool = &twines;
	const Twine &n = (*pool)[id];
	if (n.is_flat()) {
		result.insert(pool->flat_string(id));
	} else {
		// Flat-children invariant: every concat child is a Leaf or Suffix.
		for (TwineRef c : n.children())
			result.insert(pool->flat_string(c));
	}
	return result;
}

// std::string RTLIL::AttrObject::strpool_attribute_to_str(const pool<string> &data)
// {
// 	string attrval;
// 	for (const auto &s : data) {
// 		if (!attrval.empty())
// 			attrval += "|";
// 		attrval += s;
// 	}
// 	return attrval;
// }

// void RTLIL::AttrObject::set_strpool_attribute(IdString id, const pool<string> &data)
// {
// 	set_string_attribute(id, strpool_attribute_to_str(data));
// }

// void RTLIL::AttrObject::add_strpool_attribute(IdString id, const pool<string> &data)
// {
// 	pool<string> union_data = get_strpool_attribute(id);
// 	union_data.insert(data.begin(), data.end());
// 	if (!union_data.empty())
// 		set_strpool_attribute(id, union_data);
// }

// pool<string> RTLIL::AttrObject::get_strpool_attribute(IdString id) const
// {
// 	pool<string> data;
// 	if (attributes.count(id) != 0)
// 		for (auto s : split_tokens(get_string_attribute(id), "|"))
// 			data.insert(s);
// 	return data;
// }

void RTLIL::AttrObject::set_hdlname_attribute(const vector<string> &hierarchy)
{
	string attrval;
	for (const auto &ident : hierarchy) {
		if (!attrval.empty())
			attrval += " ";
		attrval += ident;
	}
	set_string_attribute(ID::hdlname, attrval);
}

vector<string> RTLIL::AttrObject::get_hdlname_attribute() const
{
	return split_tokens(get_string_attribute(ID::hdlname), " ");
}

void RTLIL::AttrObject::set_intvec_attribute(IdString id, const vector<int> &data)
{
	std::stringstream attrval;
	for (auto &i : data) {
		if (attrval.tellp() > 0)
			attrval << " ";
		attrval << i;
	}
	attributes[id] = RTLIL::Const(attrval.str());
}

vector<int> RTLIL::AttrObject::get_intvec_attribute(IdString id) const
{
	vector<int> data;
	auto it = attributes.find(id);
	if (it != attributes.end())
		for (const auto &s : split_tokens(attributes.at(id).decode_string())) {
			char *end = nullptr;
			errno = 0;
			long value = strtol(s.c_str(), &end, 10);
			if (end != s.c_str() + s.size())
				log_cmd_error("Literal for intvec attribute has invalid format");
			if (errno == ERANGE || value < INT_MIN || value > INT_MAX)
				log_cmd_error("Literal for intvec attribute is out of range");
			data.push_back(value);
		}
	return data;
}

bool RTLIL::Selection::boxed_module(TwineRef mod_name) const
{
	if (current_design != nullptr) {
		auto module = current_design->module(mod_name);
		// auto module = current_design->module(mod_name);
		return module && module->get_blackbox_attribute();
	} else {
		log_warning("Unable to check if module is boxed for null design.\n");
		return false;
	}
}

bool RTLIL::Selection::selected_module(TwineRef mod_name) const
{
	if (complete_selection)
		return true;
	if (!selects_boxes && boxed_module(mod_name))
		return false;
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	if (selected_members.count(mod_name) > 0)
		return true;
	return false;
}

bool RTLIL::Selection::selected_whole_module(TwineRef mod_name) const
{
	if (complete_selection)
		return true;
	if (!selects_boxes && boxed_module(mod_name))
		return false;
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	return false;
}

bool RTLIL::Selection::selected_member(TwineRef mod_name, TwineRef memb_name) const
{
	if (complete_selection)
		return true;
	if (!selects_boxes && boxed_module(mod_name))
		return false;
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	if (selected_members.count(mod_name) > 0)
		if (selected_members.at(mod_name).count(memb_name) > 0)
			return true;
	return false;
}

void RTLIL::Selection::optimize(RTLIL::Design *design)
{
	if (design != current_design) {
		current_design = design;
	}

	if (selects_boxes && full_selection)
		complete_selection = true;
	if (complete_selection) {
		full_selection = false;
		selects_boxes = true;
	}
	if (selects_all()) {
		selected_modules.clear();
		selected_members.clear();
		return;
	}

	std::vector<TwineRef> del_list, add_list;

	del_list.clear();
	for (auto mod_name : selected_modules) {
		if (current_design->module(mod_name) == nullptr || (!selects_boxes && boxed_module(mod_name)))
			del_list.push_back(mod_name);
		selected_members.erase(mod_name);
	}
	for (auto mod_name : del_list)
		selected_modules.erase(mod_name);

	del_list.clear();
	for (auto &it : selected_members)
		if (current_design->module(it.first) == nullptr || (!selects_boxes && boxed_module(it.first)))
			del_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);

	for (auto &it : selected_members) {
		del_list.clear();
		for (auto memb_name : it.second)
			if (current_design->module(it.first)->count_id(memb_name) == 0)
				del_list.push_back(memb_name);
		for (auto memb_name : del_list)
			it.second.erase(memb_name);
	}

	del_list.clear();
	add_list.clear();
	for (auto &it : selected_members)
		if (it.second.size() == 0)
			del_list.push_back(it.first);
		else if (it.second.size() == current_design->module(it.first)->wires_.size() + current_design->module(it.first)->memories.size() +
				current_design->module(it.first)->cells_.size() + current_design->module(it.first)->processes.size())
			add_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);
	for (auto mod_name : add_list) {
		selected_members.erase(mod_name);
		selected_modules.insert(mod_name);
	}

	if (selected_modules.size() == current_design->modules_.size()) {
		selected_modules.clear();
		selected_members.clear();
		if (selects_boxes)
			complete_selection = true;
		else
			full_selection = true;
	}
}

void RTLIL::Selection::clear()
{
	full_selection = false;
	complete_selection = false;
	selected_modules.clear();
	selected_members.clear();
}

RTLIL::Design::Design()
  : verilog_defines (new define_map_t)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	refcount_modules_ = 0;
	push_full_selection();

	RTLIL::Design::get_all_designs()->insert(std::pair<unsigned int, RTLIL::Design*>(hashidx_, this));
}

RTLIL::Design::~Design()
{
	for (auto &pr : modules_)
		delete pr.second;
	for (auto n : bindings_)
		delete n;
	RTLIL::Design::get_all_designs()->erase(hashidx_);
}

static std::map<unsigned int, RTLIL::Design*> all_designs;
std::map<unsigned int, RTLIL::Design*> *RTLIL::Design::get_all_designs(void)
{
	return &all_designs;
}

RTLIL::ObjRange<RTLIL::Module*, TwineRef> RTLIL::Design::modules()
{
	return RTLIL::ObjRange<RTLIL::Module*, TwineRef>(&modules_, &refcount_modules_);
}

const RTLIL::Module *RTLIL::Design::module(TwineRef id) const {
	return modules_.count(id) ? modules_.at(id) : NULL;
}
RTLIL::Module *RTLIL::Design::module(TwineRef id) {
	return modules_.count(id) ? modules_.at(id) : NULL;
}
// const RTLIL::Module *RTLIL::Design::module(IdString id) const {
// 	TwineRef r = twines.lookup(id.str());
// 	return r == Twine::Null ? NULL : module(r);
// }
// RTLIL::Module *RTLIL::Design::module(IdString id) {
// 	TwineRef r = twines.lookup(id.str());
// 	return r == Twine::Null ? NULL : module(r);
// }

RTLIL::Module *RTLIL::Design::top_module() const
{
	RTLIL::Module *module = nullptr;
	int module_count = 0;

	for (auto mod : selected_modules()) {
		if (mod->get_bool_attribute(ID::top))
			return mod;
		module_count++;
		module = mod;
	}

	return module_count == 1 ? module : nullptr;
}

void RTLIL::Design::add(RTLIL::Binding *binding)
{
	log_assert(binding != nullptr);
	bindings_.push_back(binding);
}

RTLIL::Module *RTLIL::Design::addModule(TwineRef name)
{
	if (modules_.count(name) != 0)
		log_error("Attempted to add new module named '%s', but a module by that name already exists\n", twines.str(name));
	log_assert(refcount_modules_ == 0);

	RTLIL::Module *module = new RTLIL::Module;
	modules_[name] = module;
	module->design = this;
	module->meta_ = alloc_obj_meta();
	module->meta_->name = name;

	for (auto mon : monitors)
		mon->notify_module_add(module);

	if (yosys_xtrace) {
		log("#X# New Module: %s\n", twines.str(name));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	return module;
}

void RTLIL::Design::scratchpad_unset(const std::string &varname)
{
	scratchpad.erase(varname);
}

void RTLIL::Design::scratchpad_set_int(const std::string &varname, int value)
{
	scratchpad[varname] = stringf("%d", value);
}

void RTLIL::Design::scratchpad_set_bool(const std::string &varname, bool value)
{
	scratchpad[varname] = value ? "true" : "false";
}

void RTLIL::Design::scratchpad_set_string(const std::string &varname, std::string value)
{
	scratchpad[varname] = std::move(value);
}

int RTLIL::Design::scratchpad_get_int(const std::string &varname, int default_value) const
{
	auto it = scratchpad.find(varname);
	if (it == scratchpad.end())
		return default_value;

	const std::string &str = it->second;

	if (str == "0" || str == "false")
		return 0;

	if (str == "1" || str == "true")
		return 1;

	char *endptr = nullptr;
	long int parsed_value = strtol(str.c_str(), &endptr, 10);
	return *endptr ? default_value : parsed_value;
}

bool RTLIL::Design::scratchpad_get_bool(const std::string &varname, bool default_value) const
{
	auto it = scratchpad.find(varname);
	if (it == scratchpad.end())
		return default_value;

	const std::string &str = it->second;

	if (str == "0" || str == "false")
		return false;

	if (str == "1" || str == "true")
		return true;

	return default_value;
}

std::string RTLIL::Design::scratchpad_get_string(const std::string &varname, const std::string &default_value) const
{
	auto it = scratchpad.find(varname);
	if (it == scratchpad.end())
		return default_value;

	return it->second;
}

void RTLIL::Design::remove(RTLIL::Module *module)
{
	for (auto mon : monitors)
		mon->notify_module_del(module);

	if (yosys_xtrace) {
		log("#X# Remove Module: %s\n", module);
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	log_assert(modules_.at(module->meta_->name) == module);
	log_assert(refcount_modules_ == 0);
	modules_.erase(module->meta_->name);
	delete module;
}

void RTLIL::Design::rename(RTLIL::Module *module, TwineRef new_name)
{
	modules_.erase(module->meta_->name);
	module->meta_->name = new_name;
	add(module);
}

void RTLIL::Design::sort()
{
	scratchpad.sort();
	modules_.sort();
	for (auto &it : modules_)
		it.second->sort();
}

void RTLIL::Design::sort_modules()
{
	scratchpad.sort();
	modules_.sort();
}

void check_module(RTLIL::Module *module, ParallelDispatchThreadPool &thread_pool);

void RTLIL::Design::check()
{
#ifndef NDEBUG
	log_assert(!selection_stack.empty());
	int pool_size = 0;
	for (auto &it : modules_)
		pool_size = std::max(pool_size, ThreadPool::work_pool_size(0, it.second->cells_size(), 1000));
	ParallelDispatchThreadPool thread_pool(pool_size);
	for (auto &it : modules_) {
		log_assert(this == it.second->design);
		log_assert(it.first == it.second->meta_->name);
		// log_assert(!it.first.empty());
		check_module(it.second, thread_pool);
	}
#endif
}

void RTLIL::Design::optimize()
{
	for (auto &it : modules_)
		it.second->optimize();
	for (auto &it : selection_stack)
		it.optimize(this);
	for (auto &it : selection_vars)
		it.second.optimize(this);
}

void RTLIL::Design::clone_into(RTLIL::Design *dst) const
{
	log_assert(dst->modules_.empty());
	dst->twines = twines;
	for (auto it = modules_.rbegin(); it != modules_.rend(); ++it)
		it->second->clone(dst, /*src_id_verbatim=*/true);
}

bool RTLIL::Design::selected_module(TwineRef mod_name) const
{
	if (selected_active_module && mod_name != selected_active_module)
		return false;
	return selection().selected_module(mod_name);
}

bool RTLIL::Design::selected_whole_module(TwineRef mod_name) const
{
	if (selected_active_module && mod_name != selected_active_module)
		return false;
	return selection().selected_whole_module(mod_name);
}

bool RTLIL::Design::selected_member(TwineRef mod_name, TwineRef memb_name) const
{
	if (selected_active_module && mod_name != selected_active_module)
		return false;
	return selection().selected_member(mod_name, memb_name);
}

bool RTLIL::Design::selected_module(RTLIL::Module *mod) const
{
	return selected_module(mod->meta_->name);
}

bool RTLIL::Design::selected_whole_module(RTLIL::Module *mod) const
{
	return selected_whole_module(mod->meta_->name);
}

void RTLIL::Design::push_selection(RTLIL::Selection sel)
{
	sel.current_design = this;
	selection_stack.push_back(sel);
}

void RTLIL::Design::push_empty_selection()
{
	push_selection(RTLIL::Selection::EmptySelection(this));
}

void RTLIL::Design::push_full_selection()
{
	push_selection(RTLIL::Selection::FullSelection(this));
}

void RTLIL::Design::push_complete_selection()
{
	push_selection(RTLIL::Selection::CompleteSelection(this));
}

void RTLIL::Design::pop_selection()
{
	selection_stack.pop_back();
	// Default to a full_selection if we ran out of stack
	if (selection_stack.empty())
		push_full_selection();
}

std::string RTLIL::Design::to_rtlil_str(bool only_selected) const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_design(f, const_cast<RTLIL::Design*>(this), only_selected);
	return f.str();
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_modules(RTLIL::SelectPartials partials, RTLIL::SelectBoxes boxes) const
{
	bool include_partials = partials == RTLIL::SELECT_ALL;
	bool exclude_boxes = (boxes & RTLIL::SB_UNBOXED_ONLY) != 0;
	bool ignore_wb = (boxes & RTLIL::SB_INCL_WB) != 0;
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_) {
		if (selected_whole_module(it.first) || (include_partials && selected_module(it.first))) {
			if (!(exclude_boxes && it.second->get_blackbox_attribute(ignore_wb)))
				result.push_back(it.second);
			else
				switch (boxes)
				{
				case RTLIL::SB_UNBOXED_WARN:
					log_warning("Ignoring boxed module %s.\n", twines.str(it.first).c_str());
					break;
				case RTLIL::SB_EXCL_BB_WARN:
					log_warning("Ignoring blackbox module %s.\n", twines.str(it.first).c_str());
					break;
				case RTLIL::SB_UNBOXED_ERR:
					log_error("Unsupported boxed module %s.\n", twines.str(it.first).c_str());
					break;
				case RTLIL::SB_EXCL_BB_ERR:
					log_error("Unsupported blackbox module %s.\n", twines.str(it.first).c_str());
					break;
				case RTLIL::SB_UNBOXED_CMDERR:
					log_cmd_error("Unsupported boxed module %s.\n", twines.str(it.first).c_str());
					break;
				case RTLIL::SB_EXCL_BB_CMDERR:
					log_cmd_error("Unsupported blackbox module %s.\n", twines.str(it.first).c_str());
					break;
				default:
					break;
				}
		} else if (!include_partials && selected_module(it.first)) {
			switch(partials)
			{
			case RTLIL::SELECT_WHOLE_WARN:
				log_warning("Ignoring partially selected module %s.\n", twines.str(it.first).c_str());
				break;
			case RTLIL::SELECT_WHOLE_ERR:
				log_error("Unsupported partially selected module %s.\n", twines.str(it.first).c_str());
				break;
			case RTLIL::SELECT_WHOLE_CMDERR:
				log_cmd_error("Unsupported partially selected module %s.\n", twines.str(it.first).c_str());
				break;
			default:
				break;
			}
		}
	}
	return result;
}

RTLIL::Module::Module()
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	design = nullptr;
	refcount_wires_ = 0;
	refcount_cells_ = 0;
	meta_ = new ObjMeta;

#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Module::get_all_modules()->insert(std::pair<unsigned int, RTLIL::Module*>(hashidx_, this));
#endif
}

RTLIL::Module::~Module()
{
	clear_sig_norm_index();
	// Wire/Cell/Process/Memory release their own src via their dtors
	// through module->design. They run after their respective deletes
	// below, so we let them handle their own meta_idx_ cleanup.
	for (auto &pr : wires_)
		delete pr.second;
	for (auto &pr : memories)
		delete pr.second;
	for (auto &pr : cells_)
		delete pr.second;
	for (auto &pr : processes)
		delete pr.second;
	for (auto binding : bindings_)
		delete binding;
	// Module's own src — release last so the pool stays valid for
	// inner releases above.
	if (design)
		design->obj_release_src(this);
#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Module::get_all_modules()->erase(hashidx_);
#endif
}

TwineRef RTLIL::Module::src_id() const
{
	if (!design)
		return Twine::Null;
	return design->obj_src_id(this);
}

void RTLIL::Module::set_src_id(TwineRef id)
{
	log_assert(design && "Module::set_src_id requires the module to be attached to a design");
	design->obj_set_src_id(this, id);
}

void RTLIL::Module::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(design && "Module::set_src_attribute requires the module to be attached to a design");
	design->set_src_attribute(this, src);
}

void RTLIL::Module::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(design && "Module::adopt_src_from requires the module to be attached to a design");
	design->adopt_src_from(this, source);
}

std::string RTLIL::Module::get_src_attribute() const
{
	log_assert(design);
	return design->get_src_attribute(this);
}

void RTLIL::Module::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(design && "Module::absorb_attrs requires the module to be attached to a design");
	design->absorb_attrs(this, std::move(buf));
}

#ifdef YOSYS_ENABLE_PYTHON
static std::map<unsigned int, RTLIL::Module*> all_modules;
std::map<unsigned int, RTLIL::Module*> *RTLIL::Module::get_all_modules(void)
{
	return &all_modules;
}
#endif

void RTLIL::Module::makeblackbox()
{
	pool<RTLIL::Wire*> delwires;

	for (auto it = wires_.begin(); it != wires_.end(); ++it)
		if (!it->second->port_input && !it->second->port_output)
			delwires.insert(it->second);

	for (auto it = memories.begin(); it != memories.end(); ++it)
		delete it->second;
	memories.clear();

	for (auto it = cells_.begin(); it != cells_.end(); ++it)
		delete it->second;
	cells_.clear();

	for (auto it = processes.begin(); it != processes.end(); ++it)
		delete it->second;
	processes.clear();

	connections_.clear();

	remove(delwires);
	set_bool_attribute(ID::blackbox);
}

void RTLIL::Module::expand_interfaces(RTLIL::Design *, const dict<RTLIL::IdString, RTLIL::Module *> &)
{
	log_error("Class doesn't support expand_interfaces (module: `%s')!\n", design->twines.str(meta_->name).c_str());
}

bool RTLIL::Module::reprocess_if_necessary(RTLIL::Design *)
{
	return false;
}

TwineRef RTLIL::Module::derive(RTLIL::Design*, const dict<RTLIL::IdString, RTLIL::Const> &, bool mayfail)
{
	if (mayfail)
		return Twine::Null;
	log_error("Module `%s' is used with parameters but is not parametric!\n", design->twines.str(meta_->name).c_str());
}


TwineRef RTLIL::Module::derive(RTLIL::Design*, const dict<RTLIL::IdString, RTLIL::Const> &, const dict<TwineRef, RTLIL::Module*> &, const dict<TwineRef, TwineRef> &, bool mayfail)
{
	if (mayfail)
		return Twine::Null;
	log_error("Module `%s' is used with parameters but is not parametric!\n", design->twines.str(meta_->name).c_str());
}

size_t RTLIL::Module::count_id(TwineRef id)
{
	return wires_.count(id) + cells_.count(id) + memories.count(id) + processes.count(id);
}

#ifndef NDEBUG
namespace {
	struct InternalCellChecker
	{
		const RTLIL::Module *module;
		RTLIL::Cell *cell;
		pool<IdString> expected_params;
		pool<TwineRef> expected_ports;

		InternalCellChecker(const RTLIL::Module *module, RTLIL::Cell *cell) : module(module), cell(cell) { }

		void error(int linenr)
		{
			std::stringstream buf;
			RTLIL_BACKEND::dump_cell(buf, "  ", cell, cell->module->design);

			std::string mod_name = module ? module->design->twines.str(module->meta_->name) : std::string();
			std::string cell_name = cell->module->design->twines.str(cell->meta_->name);
			log_error("Found error in internal cell %s%s%s (%s) at %s:%d:\n%s",
					mod_name, module ? "." : "",
					cell_name, cell->type.str(), __FILE__, linenr, buf.str());
		}

		int param(IdString name)
		{
			auto it = cell->parameters.find(name);
			if (it == cell->parameters.end())
				error(__LINE__);
			expected_params.insert(name);
			return it->second.as_int();
		}

		int param_bool(IdString name)
		{
			int v = param(name);
			if (GetSize(cell->parameters.at(name)) > 32)
				error(__LINE__);
			if (v != 0 && v != 1)
				error(__LINE__);
			return v;
		}

		int param_bool(IdString name, bool expected)
		{
			int v = param_bool(name);
			if (v != expected)
				error(__LINE__);
			return v;
		}

		void param_bits(IdString name, int width)
		{
			param(name);
			if (GetSize(cell->parameters.at(name)) != width)
				error(__LINE__);
		}

		std::string param_string(IdString name)
		{
			param(name);
			return cell->parameters.at(name).decode_string();
		}

		void port(TwineRef name, int width)
		{
			auto it = cell->connections_.find(name);
			if (it == cell->connections_.end())
				error(__LINE__);
			if (GetSize(it->second) != width)
				error(__LINE__);
			expected_ports.insert(name);
		}

		void check_expected(bool check_matched_sign = false)
		{
			for (auto &para : cell->parameters)
				if (expected_params.count(para.first) == 0)
					error(__LINE__);
			for (auto &conn : cell->connections())
				if (expected_ports.count(conn.first) == 0)
					error(__LINE__);

			if (check_matched_sign) {
				log_assert(expected_params.count(ID::A_SIGNED) != 0 && expected_params.count(ID::B_SIGNED) != 0);
				bool a_is_signed = cell->parameters.at(ID::A_SIGNED).as_bool();
				bool b_is_signed = cell->parameters.at(ID::B_SIGNED).as_bool();
				if (a_is_signed != b_is_signed)
					error(__LINE__);
			}
		}

		void check()
		{
			std::string type_str = cell->type.str();
			std::string_view type_sv = type_str;
			if (!type_sv.starts_with("$") || type_sv.starts_with("$__") || type_sv.starts_with("$paramod") || type_sv.starts_with("$fmcombine") ||
					type_sv.starts_with("$verific$") || type_sv.starts_with("$array:") || type_sv.starts_with("$extern:"))
				return;

			if (cell->type_impl == TW($buf)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($not), TW($pos), TW($neg))) {
				param_bool(ID::A_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($and), TW($or), TW($xor), TW($xnor))) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(true);
				return;
			}

			if (cell->type_impl.in(TW($reduce_and), TW($reduce_or), TW($reduce_xor), TW($reduce_xnor), TW($reduce_bool))) {
				param_bool(ID::A_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($shl), TW($shr), TW($sshl), TW($sshr))) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED, /*expected=*/false);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type_impl.in(TW($shift), TW($shiftx))) {
				if (cell->type == TW($shiftx)) {
					param_bool(ID::A_SIGNED, /*expected=*/false);
				} else {
					param_bool(ID::A_SIGNED);
				}
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type_impl.in(TW($lt), TW($le), TW($eq), TW($ne), TW($eqx), TW($nex), TW($ge), TW($gt))) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(true);
				return;
			}

			if (cell->type_impl.in(TW($add), TW($sub), TW($mul), TW($div), TW($mod), TW($divfloor), TW($modfloor), TW($pow))) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(cell->type != TW($pow));
				return;
			}

			if (cell->type == TW($fa)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH));
				port(TW::C, param(ID::WIDTH));
				port(TW::X, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($lcu)) {
				port(TW::P, param(ID::WIDTH));
				port(TW::G, param(ID::WIDTH));
				port(TW::CI, 1);
				port(TW::CO, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($alu)) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::CI, 1);
				port(TW::BI, 1);
				port(TW::X, param(ID::Y_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				port(TW::CO, param(ID::Y_WIDTH));
				check_expected(true);
				return;
			}

			if (cell->type == TW($macc)) {
				param(ID::CONFIG);
				param(ID::CONFIG_WIDTH);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected();
				Macc().from_cell(cell);
				return;
			}

			if (cell->type == TW($macc_v2)) {
				if (param(ID::NPRODUCTS) < 0)
					error(__LINE__);
				if (param(ID::NADDENDS) < 0)
					error(__LINE__);
				param_bits(ID::PRODUCT_NEGATED, max(param(ID::NPRODUCTS), 1));
				param_bits(ID::ADDEND_NEGATED, max(param(ID::NADDENDS), 1));
				param_bits(ID::A_SIGNED, max(param(ID::NPRODUCTS), 1));
				param_bits(ID::B_SIGNED, max(param(ID::NPRODUCTS), 1));
				param_bits(ID::C_SIGNED, max(param(ID::NADDENDS), 1));
				if (cell->getParam(ID::A_SIGNED) != cell->getParam(ID::B_SIGNED))
					error(__LINE__);
				param_bits(ID::A_WIDTHS, max(param(ID::NPRODUCTS) * 16, 1));
				param_bits(ID::B_WIDTHS, max(param(ID::NPRODUCTS) * 16, 1));
				param_bits(ID::C_WIDTHS, max(param(ID::NADDENDS) * 16, 1));
				const Const &a_width = cell->getParam(ID::A_WIDTHS);
				const Const &b_width = cell->getParam(ID::B_WIDTHS);
				const Const &c_width = cell->getParam(ID::C_WIDTHS);
				int a_width_sum = 0, b_width_sum = 0, c_width_sum = 0;
				for (int i = 0; i < param(ID::NPRODUCTS); i++) {
					a_width_sum += a_width.extract(16 * i, 16).as_int(false);
					b_width_sum += b_width.extract(16 * i, 16).as_int(false);
				}
				for (int i = 0; i < param(ID::NADDENDS); i++) {
					c_width_sum += c_width.extract(16 * i, 16).as_int(false);
				}
				port(TW::A, a_width_sum);
				port(TW::B, b_width_sum);
				port(TW::C, c_width_sum);
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($logic_not)) {
				param_bool(ID::A_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($logic_and), TW($logic_or))) {
				param_bool(ID::A_SIGNED);
				param_bool(ID::B_SIGNED);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type == TW($slice)) {
				param(ID::OFFSET);
				port(TW::A, param(ID::A_WIDTH));
				port(TW::Y, param(ID::Y_WIDTH));
				if (param(ID::OFFSET) + param(ID::Y_WIDTH) > param(ID::A_WIDTH))
					error(__LINE__);
				check_expected();
				return;
			}

			if (cell->type == TW($concat)) {
				port(TW::A, param(ID::A_WIDTH));
				port(TW::B, param(ID::B_WIDTH));
				port(TW::Y, param(ID::A_WIDTH) + param(ID::B_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($mux)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH));
				port(TW::S, 1);
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($pmux)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH) * param(ID::S_WIDTH));
				port(TW::S, param(ID::S_WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($bmux)) {
				port(TW::A, param(ID::WIDTH) << param(ID::S_WIDTH));
				port(TW::S, param(ID::S_WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($demux)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::S, param(ID::S_WIDTH));
				port(TW::Y, param(ID::WIDTH) << param(ID::S_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($lut)) {
				param(ID::LUT);
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, 1);
				check_expected();
				return;
			}

			if (cell->type == TW($sop)) {
				param(ID::DEPTH);
				param(ID::TABLE);
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, 1);
				check_expected();
				return;
			}

			if (cell->type == TW($sr)) {
				param_bool(ID::SET_POLARITY);
				param_bool(ID::CLR_POLARITY);
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				port(TW::Q,   param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($ff)) {
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dff)) {
				param_bool(ID::CLK_POLARITY);
				port(TW::CLK, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dffe)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::EN_POLARITY);
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dffsr)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::SET_POLARITY);
				param_bool(ID::CLR_POLARITY);
				port(TW::CLK, 1);
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dffsre)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::SET_POLARITY);
				param_bool(ID::CLR_POLARITY);
				param_bool(ID::EN_POLARITY);
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($adff)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::ARST_POLARITY);
				param_bits(ID::ARST_VALUE, param(ID::WIDTH));
				port(TW::CLK, 1);
				port(TW::ARST, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($sdff)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::SRST_POLARITY);
				param_bits(ID::SRST_VALUE, param(ID::WIDTH));
				port(TW::CLK, 1);
				port(TW::SRST, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($sdffe), TW($sdffce))) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::EN_POLARITY);
				param_bool(ID::SRST_POLARITY);
				param_bits(ID::SRST_VALUE, param(ID::WIDTH));
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::SRST, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($adffe)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::EN_POLARITY);
				param_bool(ID::ARST_POLARITY);
				param_bits(ID::ARST_VALUE, param(ID::WIDTH));
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::ARST, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($aldff)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::ALOAD_POLARITY);
				port(TW::CLK, 1);
				port(TW::ALOAD, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::AD, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($aldffe)) {
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::EN_POLARITY);
				param_bool(ID::ALOAD_POLARITY);
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::ALOAD, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::AD, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dlatch)) {
				param_bool(ID::EN_POLARITY);
				port(TW::EN, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($adlatch)) {
				param_bool(ID::EN_POLARITY);
				param_bool(ID::ARST_POLARITY);
				param_bits(ID::ARST_VALUE, param(ID::WIDTH));
				port(TW::EN, 1);
				port(TW::ARST, 1);
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($dlatchsr)) {
				param_bool(ID::EN_POLARITY);
				param_bool(ID::SET_POLARITY);
				param_bool(ID::CLR_POLARITY);
				port(TW::EN, 1);
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($fsm)) {
				param(ID::NAME);
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::ARST_POLARITY);
				param(ID::STATE_BITS);
				param(ID::STATE_NUM);
				param(ID::STATE_NUM_LOG2);
				param(ID::STATE_RST);
				param_bits(ID::STATE_TABLE, param(ID::STATE_BITS) * param(ID::STATE_NUM));
				param(ID::TRANS_NUM);
				param_bits(ID::TRANS_TABLE, param(ID::TRANS_NUM) * (2*param(ID::STATE_NUM_LOG2) + param(ID::CTRL_IN_WIDTH) + param(ID::CTRL_OUT_WIDTH)));
				port(TW::CLK, 1);
				port(TW::ARST, 1);
				port(TW::CTRL_IN, param(ID::CTRL_IN_WIDTH));
				port(TW::CTRL_OUT, param(ID::CTRL_OUT_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($memrd)) {
				param(ID::MEMID);
				param_bool(ID::CLK_ENABLE);
				param_bool(ID::CLK_POLARITY);
				param_bool(ID::TRANSPARENT);
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($memrd_v2)) {
				param(ID::MEMID);
				param_bool(ID::CLK_ENABLE);
				param_bool(ID::CLK_POLARITY);
				param(ID::TRANSPARENCY_MASK);
				param(ID::COLLISION_X_MASK);
				param_bool(ID::CE_OVER_SRST);
				param_bits(ID::ARST_VALUE, param(ID::WIDTH));
				param_bits(ID::SRST_VALUE, param(ID::WIDTH));
				param_bits(ID::INIT_VALUE, param(ID::WIDTH));
				port(TW::CLK, 1);
				port(TW::EN, 1);
				port(TW::ARST, 1);
				port(TW::SRST, 1);
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($memwr)) {
				param(ID::MEMID);
				param_bool(ID::CLK_ENABLE);
				param_bool(ID::CLK_POLARITY);
				param(ID::PRIORITY);
				port(TW::CLK, 1);
				port(TW::EN, param(ID::WIDTH));
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($memwr_v2)) {
				param(ID::MEMID);
				param_bool(ID::CLK_ENABLE);
				param_bool(ID::CLK_POLARITY);
				param(ID::PORTID);
				param(ID::PRIORITY_MASK);
				port(TW::CLK, 1);
				port(TW::EN, param(ID::WIDTH));
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($meminit)) {
				param(ID::MEMID);
				param(ID::PRIORITY);
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH) * param(ID::WORDS));
				check_expected();
				return;
			}

			if (cell->type == TW($meminit_v2)) {
				param(ID::MEMID);
				param(ID::PRIORITY);
				port(TW::ADDR, param(ID::ABITS));
				port(TW::DATA, param(ID::WIDTH) * param(ID::WORDS));
				port(TW::EN, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($mem)) {
				param(ID::MEMID);
				param(ID::SIZE);
				param(ID::OFFSET);
				param(ID::INIT);
				param_bits(ID::RD_CLK_ENABLE, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_CLK_POLARITY, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_TRANSPARENT, max(1, param(ID::RD_PORTS)));
				param_bits(ID::WR_CLK_ENABLE, max(1, param(ID::WR_PORTS)));
				param_bits(ID::WR_CLK_POLARITY, max(1, param(ID::WR_PORTS)));
				port(TW::RD_CLK, param(ID::RD_PORTS));
				port(TW::RD_EN, param(ID::RD_PORTS));
				port(TW::RD_ADDR, param(ID::RD_PORTS) * param(ID::ABITS));
				port(TW::RD_DATA, param(ID::RD_PORTS) * param(ID::WIDTH));
				port(TW::WR_CLK, param(ID::WR_PORTS));
				port(TW::WR_EN, param(ID::WR_PORTS) * param(ID::WIDTH));
				port(TW::WR_ADDR, param(ID::WR_PORTS) * param(ID::ABITS));
				port(TW::WR_DATA, param(ID::WR_PORTS) * param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($mem_v2)) {
				param(ID::MEMID);
				param(ID::SIZE);
				param(ID::OFFSET);
				param(ID::INIT);
				param_bits(ID::RD_CLK_ENABLE, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_CLK_POLARITY, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_TRANSPARENCY_MASK, max(1, param(ID::RD_PORTS) * param(ID::WR_PORTS)));
				param_bits(ID::RD_COLLISION_X_MASK, max(1, param(ID::RD_PORTS) * param(ID::WR_PORTS)));
				param_bits(ID::RD_WIDE_CONTINUATION, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_CE_OVER_SRST, max(1, param(ID::RD_PORTS)));
				param_bits(ID::RD_ARST_VALUE, max(1, param(ID::RD_PORTS) * param(ID::WIDTH)));
				param_bits(ID::RD_SRST_VALUE, max(1, param(ID::RD_PORTS) * param(ID::WIDTH)));
				param_bits(ID::RD_INIT_VALUE, max(1, param(ID::RD_PORTS) * param(ID::WIDTH)));
				param_bits(ID::WR_CLK_ENABLE, max(1, param(ID::WR_PORTS)));
				param_bits(ID::WR_CLK_POLARITY, max(1, param(ID::WR_PORTS)));
				param_bits(ID::WR_WIDE_CONTINUATION, max(1, param(ID::WR_PORTS)));
				param_bits(ID::WR_PRIORITY_MASK, max(1, param(ID::WR_PORTS) * param(ID::WR_PORTS)));
				port(TW::RD_CLK, param(ID::RD_PORTS));
				port(TW::RD_EN, param(ID::RD_PORTS));
				port(TW::RD_ARST, param(ID::RD_PORTS));
				port(TW::RD_SRST, param(ID::RD_PORTS));
				port(TW::RD_ADDR, param(ID::RD_PORTS) * param(ID::ABITS));
				port(TW::RD_DATA, param(ID::RD_PORTS) * param(ID::WIDTH));
				port(TW::WR_CLK, param(ID::WR_PORTS));
				port(TW::WR_EN, param(ID::WR_PORTS) * param(ID::WIDTH));
				port(TW::WR_ADDR, param(ID::WR_PORTS) * param(ID::ABITS));
				port(TW::WR_DATA, param(ID::WR_PORTS) * param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($tribuf)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				port(TW::EN, 1);
				check_expected();
				return;
			}

			if (cell->type == TW($bweqx)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($bwmux)) {
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH));
				port(TW::S, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($assert), TW($assume), TW($live), TW($fair), TW($cover))) {
				port(TW::A, 1);
				port(TW::EN, 1);
				check_expected();
				return;
			}

			if (cell->type == TW($initstate)) {
				port(TW::Y, 1);
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($anyconst), TW($anyseq), TW($allconst), TW($allseq))) {
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($anyinit))) {
				port(TW::D, param(ID::WIDTH));
				port(TW::Q, param(ID::WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($equiv)) {
				port(TW::A, 1);
				port(TW::B, 1);
				port(TW::Y, 1);
				check_expected();
				return;
			}

			if (cell->type_impl.in(TW($specify2), TW($specify3))) {
				param_bool(ID::FULL);
				param_bool(ID::SRC_DST_PEN);
				param_bool(ID::SRC_DST_POL);
				param(ID::T_RISE_MIN);
				param(ID::T_RISE_TYP);
				param(ID::T_RISE_MAX);
				param(ID::T_FALL_MIN);
				param(ID::T_FALL_TYP);
				param(ID::T_FALL_MAX);
				port(TW::EN, 1);
				port(TW::SRC, param(ID::SRC_WIDTH));
				port(TW::DST, param(ID::DST_WIDTH));
				if (cell->type == TW($specify3)) {
					param_bool(ID::EDGE_EN);
					param_bool(ID::EDGE_POL);
					param_bool(ID::DAT_DST_PEN);
					param_bool(ID::DAT_DST_POL);
					port(TW::DAT, param(ID::DST_WIDTH));
				}
				check_expected();
				return;
			}

			if (cell->type == TW($specrule)) {
				param(ID::TYPE);
				param_bool(ID::SRC_PEN);
				param_bool(ID::SRC_POL);
				param_bool(ID::DST_PEN);
				param_bool(ID::DST_POL);
				param(ID::T_LIMIT_MIN);
				param(ID::T_LIMIT_TYP);
				param(ID::T_LIMIT_MAX);
				param(ID::T_LIMIT2_MIN);
				param(ID::T_LIMIT2_TYP);
				param(ID::T_LIMIT2_MAX);
				port(TW::SRC_EN, 1);
				port(TW::DST_EN, 1);
				port(TW::SRC, param(ID::SRC_WIDTH));
				port(TW::DST, param(ID::DST_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($print)) {
				param(ID(FORMAT));
				param_bool(ID::TRG_ENABLE);
				param(ID::TRG_POLARITY);
				param(ID::PRIORITY);
				port(TW::EN, 1);
				port(TW::TRG, param(ID::TRG_WIDTH));
				port(TW::ARGS, param(ID::ARGS_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($check)) {
				std::string flavor = param_string(ID(FLAVOR));
				if (!(flavor == "assert" || flavor == "assume" || flavor == "live" || flavor == "fair" || flavor == "cover"))
					error(__LINE__);
				param(ID(FORMAT));
				param_bool(ID::TRG_ENABLE);
				param(ID::TRG_POLARITY);
				param(ID::PRIORITY);
				port(TW::A, 1);
				port(TW::EN, 1);
				port(TW::TRG, param(ID::TRG_WIDTH));
				port(TW::ARGS, param(ID::ARGS_WIDTH));
				check_expected();
				return;
			}

			if (cell->type == TW($scopeinfo)) {
				param(ID::TYPE);
				check_expected();
				std::string scope_type = cell->getParam(ID::TYPE).decode_string();
				if (scope_type != "module" && scope_type != "struct" && scope_type != "blackbox")
					error(__LINE__);
				return;
			}

			if (cell->type == TW($_BUF_))    { port(TW::A,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_NOT_))    { port(TW::A,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_AND_))    { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_NAND_))   { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_OR_))     { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_NOR_))    { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_XOR_))    { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_XNOR_))   { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_ANDNOT_)) { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_ORNOT_))  { port(TW::A,1); port(TW::B,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_MUX_))    { port(TW::A,1); port(TW::B,1); port(TW::S,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_NMUX_))   { port(TW::A,1); port(TW::B,1); port(TW::S,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_AOI3_))   { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_OAI3_))   { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_AOI4_))   { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::D,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_OAI4_))   { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::D,1); port(TW::Y,1); check_expected(); return; }

			if (cell->type == TW($_TBUF_))  { port(TW::A,1); port(TW::Y,1); port(TW::E,1); check_expected(); return; }

			if (cell->type == TW($_MUX4_))  { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::D,1); port(TW::S,1); port(TW::T,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_MUX8_))  { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::D,1); port(TW::E,1); port(TW::F,1); port(TW::G,1); port(TW::H,1); port(TW::S,1); port(TW::T,1); port(TW::U,1); port(TW::Y,1); check_expected(); return; }
			if (cell->type == TW($_MUX16_)) { port(TW::A,1); port(TW::B,1); port(TW::C,1); port(TW::D,1); port(TW::E,1); port(TW::F,1); port(TW::G,1); port(TW::H,1); port(TW::I,1); port(TW::J,1); port(TW::K,1); port(TW::L,1); port(TW::M,1); port(TW::N,1); port(TW::O,1); port(TW::P,1); port(TW::S,1); port(TW::T,1); port(TW::U,1); port(TW::V,1); port(TW::Y,1); check_expected(); return; }

			if (cell->type_impl.in(TW($_SR_NN_), TW($_SR_NP_), TW($_SR_PN_), TW($_SR_PP_)))
				{ port(TW::S,1); port(TW::R,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type == TW($_FF_)) { port(TW::D,1); port(TW::Q,1); check_expected();  return; }

			if (cell->type_impl.in(TW($_DFF_N_), TW($_DFF_P_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); check_expected(); return; }

			if (cell->type_impl.in(TW($_DFFE_NN_), TW($_DFFE_NP_), TW($_DFFE_PN_), TW($_DFFE_PP_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::E,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DFF_NN0_), TW($_DFF_NN1_), TW($_DFF_NP0_), TW($_DFF_NP1_),
					TW($_DFF_PN0_), TW($_DFF_PN1_), TW($_DFF_PP0_), TW($_DFF_PP1_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::R,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DFFE_NN0N_), TW($_DFFE_NN0P_), TW($_DFFE_NN1N_), TW($_DFFE_NN1P_),
					TW($_DFFE_NP0N_), TW($_DFFE_NP0P_), TW($_DFFE_NP1N_), TW($_DFFE_NP1P_),
					TW($_DFFE_PN0N_), TW($_DFFE_PN0P_), TW($_DFFE_PN1N_), TW($_DFFE_PN1P_),
					TW($_DFFE_PP0N_), TW($_DFFE_PP0P_), TW($_DFFE_PP1N_), TW($_DFFE_PP1P_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::R,1); port(TW::E,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_ALDFF_NN_), TW($_ALDFF_NP_), TW($_ALDFF_PN_), TW($_ALDFF_PP_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::L,1); port(TW::AD,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_ALDFFE_NNN_), TW($_ALDFFE_NNP_), TW($_ALDFFE_NPN_), TW($_ALDFFE_NPP_),
					TW($_ALDFFE_PNN_), TW($_ALDFFE_PNP_), TW($_ALDFFE_PPN_), TW($_ALDFFE_PPP_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::L,1); port(TW::AD,1); port(TW::E,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DFFSR_NNN_), TW($_DFFSR_NNP_), TW($_DFFSR_NPN_), TW($_DFFSR_NPP_),
					TW($_DFFSR_PNN_), TW($_DFFSR_PNP_), TW($_DFFSR_PPN_), TW($_DFFSR_PPP_)))
				{ port(TW::C,1); port(TW::S,1); port(TW::R,1); port(TW::D,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DFFSRE_NNNN_), TW($_DFFSRE_NNNP_), TW($_DFFSRE_NNPN_), TW($_DFFSRE_NNPP_),
					TW($_DFFSRE_NPNN_), TW($_DFFSRE_NPNP_), TW($_DFFSRE_NPPN_), TW($_DFFSRE_NPPP_),
					TW($_DFFSRE_PNNN_), TW($_DFFSRE_PNNP_), TW($_DFFSRE_PNPN_), TW($_DFFSRE_PNPP_),
					TW($_DFFSRE_PPNN_), TW($_DFFSRE_PPNP_), TW($_DFFSRE_PPPN_), TW($_DFFSRE_PPPP_)))
				{ port(TW::C,1); port(TW::S,1); port(TW::R,1); port(TW::D,1); port(TW::E,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_SDFF_NN0_), TW($_SDFF_NN1_), TW($_SDFF_NP0_), TW($_SDFF_NP1_),
					TW($_SDFF_PN0_), TW($_SDFF_PN1_), TW($_SDFF_PP0_), TW($_SDFF_PP1_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::R,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_SDFFE_NN0N_), TW($_SDFFE_NN0P_), TW($_SDFFE_NN1N_), TW($_SDFFE_NN1P_),
					TW($_SDFFE_NP0N_), TW($_SDFFE_NP0P_), TW($_SDFFE_NP1N_), TW($_SDFFE_NP1P_),
					TW($_SDFFE_PN0N_), TW($_SDFFE_PN0P_), TW($_SDFFE_PN1N_), TW($_SDFFE_PN1P_),
					TW($_SDFFE_PP0N_), TW($_SDFFE_PP0P_), TW($_SDFFE_PP1N_), TW($_SDFFE_PP1P_),
					TW($_SDFFCE_NN0N_), TW($_SDFFCE_NN0P_), TW($_SDFFCE_NN1N_), TW($_SDFFCE_NN1P_),
					TW($_SDFFCE_NP0N_), TW($_SDFFCE_NP0P_), TW($_SDFFCE_NP1N_), TW($_SDFFCE_NP1P_),
					TW($_SDFFCE_PN0N_), TW($_SDFFCE_PN0P_), TW($_SDFFCE_PN1N_), TW($_SDFFCE_PN1P_),
					TW($_SDFFCE_PP0N_), TW($_SDFFCE_PP0P_), TW($_SDFFCE_PP1N_), TW($_SDFFCE_PP1P_)))
				{ port(TW::D,1); port(TW::Q,1); port(TW::C,1); port(TW::R,1); port(TW::E,1); check_expected(); return; }

			if (cell->type_impl.in(TW($_DLATCH_N_), TW($_DLATCH_P_)))
				{ port(TW::E,1); port(TW::D,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DLATCH_NN0_), TW($_DLATCH_NN1_), TW($_DLATCH_NP0_), TW($_DLATCH_NP1_),
					TW($_DLATCH_PN0_), TW($_DLATCH_PN1_), TW($_DLATCH_PP0_), TW($_DLATCH_PP1_)))
				{ port(TW::E,1); port(TW::R,1); port(TW::D,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type_impl.in(
					TW($_DLATCHSR_NNN_), TW($_DLATCHSR_NNP_), TW($_DLATCHSR_NPN_), TW($_DLATCHSR_NPP_),
					TW($_DLATCHSR_PNN_), TW($_DLATCHSR_PNP_), TW($_DLATCHSR_PPN_), TW($_DLATCHSR_PPP_)))
				{ port(TW::E,1); port(TW::S,1); port(TW::R,1); port(TW::D,1); port(TW::Q,1); check_expected(); return; }

			if (cell->type_impl.in(TW($set_tag))) {
				param(ID::WIDTH);
				param(ID::TAG);
				port(TW::A, param(ID::WIDTH));
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($get_tag),TW($original_tag))) {
				param(ID::WIDTH);
				param(ID::TAG);
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($overwrite_tag))) {
				param(ID::WIDTH);
				param(ID::TAG);
				port(TW::A, param(ID::WIDTH));
				port(TW::SET, param(ID::WIDTH));
				port(TW::CLR, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($future_ff))) {
				param(ID::WIDTH);
				port(TW::A, param(ID::WIDTH));
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($input_port))) {
				param(ID::WIDTH);
				port(TW::Y, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($output_port), TW($public))) {
				param(ID::WIDTH);
				port(TW::A, param(ID::WIDTH));
				check_expected();
				return;
			}
			if (cell->type_impl.in(TW($connect))) {
				param(ID::WIDTH);
				port(TW::A, param(ID::WIDTH));
				port(TW::B, param(ID::WIDTH));
				check_expected();
				return;
			}
			/*
			 * Checklist for adding internal cell types
			 * ========================================
			 * Things to do right away:
			 *    - Add to kernel/celltypes.h (incl. eval() handling for non-mem cells)
			 *    - Add to InternalCellChecker::check() in kernel/rtlil.cc
			 *    - Add to techlibs/common/simlib.v
			 *    - Add to techlibs/common/techmap.v
			 *
			 * Things to do after finalizing the cell interface:
			 *    - Add support to kernel/satgen.h for the new cell type
			 *    - Add to docs/source/CHAPTER_CellLib.rst (or just add a fixme to the bottom)
			 *    - Maybe add support to the Verilog backend for dumping such cells as expression
			 *
			 */
			error(__LINE__);
		}
	};
}
#endif

void RTLIL::Module::sort()
{
	wires_.sort(sort_by_twine_str_expensive(design->twines));
	cells_.sort(sort_by_twine_str_expensive(design->twines));
	parameter_default_values.sort(sort_by_id_str());
	memories.sort(sort_by_twine_str_expensive(design->twines));
	processes.sort(sort_by_twine_str_expensive(design->twines));
	for (auto &it : cells_)
		it.second->sort();
	for (auto &it : wires_)
		it.second->attributes.sort(sort_by_id_str());
	for (auto &it : memories)
		it.second->attributes.sort(sort_by_id_str());
}

void check_module(RTLIL::Module *module, ParallelDispatchThreadPool &thread_pool)
{
#ifndef NDEBUG
	ParallelDispatchThreadPool::Subpool subpool(thread_pool, ThreadPool::work_pool_size(0, module->cells_size(), 1000));
	const RTLIL::Module *const_module = module;

	pool<std::string> memory_strings;
	for (auto &it : module->memories) {
		log_assert(it.second->meta_ && it.first == it.second->meta_->name);
		log_assert(it.first != Twine::Null);
		log_assert(it.second->width >= 0);
		log_assert(it.second->size >= 0);
		for (auto &it2 : it.second->attributes)
			log_assert(!it2.first.empty());
		memory_strings.insert(module->design->twines.str(it.second->meta_->name));
	}

	std::vector<MonotonicFlag> ports_declared(GetSize(module->ports));
	ShardedVector<std::string> memids(subpool);
	subpool.run([const_module, &ports_declared, &memory_strings, &memids](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			auto it = *const_module->cells_.element(i);
			log_assert(const_module == it.second->module);
			log_assert(it.second->meta_ && it.first == it.second->meta_->name);
			log_assert(it.first != Twine::Null);
			log_assert(!it.second->type.empty());
			for (auto &it2 : it.second->connections()) {
				log_assert(it2.first != Twine::Null);
				it2.second.check(const_module);
			}
			for (auto &it2 : it.second->attributes)
				log_assert(!it2.first.empty());
			for (auto &it2 : it.second->parameters)
				log_assert(!it2.first.empty());
			InternalCellChecker checker(const_module, it.second);
			checker.check();
			if (it.second->has_memid()) {
				log_assert(memory_strings.count(it.second->parameters.at(ID::MEMID).decode_string()));
			} else if (it.second->is_mem_cell()) {
				std::string memid = it.second->parameters.at(ID::MEMID).decode_string();
				log_assert(!memory_strings.count(memid));
				memids.insert(ctx, std::move(memid));
			}
			auto cell_mod = const_module->design->module(it.second->meta_->name);
			if (cell_mod != nullptr) {
				// assertion check below to make sure that there are no
				// cases where a cell has a blackbox attribute since
				// that is deprecated
				#ifdef __GNUC__
				#pragma GCC diagnostic push
				#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
				#endif
				log_assert(!it.second->get_blackbox_attribute());
				#ifdef __GNUC__
				#pragma GCC diagnostic pop
				#endif
			}
		}

		for (int i : ctx.item_range(const_module->wires_size())) {
			auto it = *const_module->wires_.element(i);
			log_assert(const_module == it.second->module);
			log_assert(it.second->meta_ && it.first == it.second->meta_->name);
			log_assert(it.first != Twine::Null);
			log_assert(it.second->width >= 0);
			log_assert(it.second->port_id >= 0);
			for (auto &it2 : it.second->attributes)
				log_assert(!it2.first.empty());
			if (it.second->port_id) {
				log_assert(GetSize(const_module->ports) >= it.second->port_id);
				log_assert(const_module->ports.at(it.second->port_id-1) == it.second->meta_->name);
				log_assert(it.second->port_input || it.second->port_output);
				log_assert(it.second->port_id <= GetSize(ports_declared));
				bool previously_declared = ports_declared[it.second->port_id-1].set_and_return_old();
				log_assert(previously_declared == false);
			} else
				log_assert(!it.second->port_input && !it.second->port_output);
		}
	});
	for (const MonotonicFlag &port_declared : ports_declared)
		log_assert(port_declared.load() == true);
	pool<std::string> memids_pool;
	for (std::string &memid : memids)
		log_assert(memids_pool.insert(memid).second);

	for (auto &it : module->processes) {
		log_assert(it.second->meta_ && it.first == it.second->meta_->name);
		log_assert(it.first != Twine::Null);
		log_assert(it.second->root_case.compare.empty());
		std::vector<RTLIL::CaseRule*> all_cases = {&it.second->root_case};
		for (size_t i = 0; i < all_cases.size(); i++) {
			for (auto &switch_it : all_cases[i]->switches) {
				for (auto &case_it : switch_it->cases) {
					for (auto &compare_it : case_it->compare) {
						log_assert(switch_it->signal.size() == compare_it.size());
					}
					all_cases.push_back(case_it);
				}
			}
		}
		for (auto &sync_it : it.second->syncs) {
			switch (sync_it->type) {
				case RTLIL::SyncType::ST0:
				case RTLIL::SyncType::ST1:
				case RTLIL::SyncType::STp:
				case RTLIL::SyncType::STn:
				case RTLIL::SyncType::STe:
					log_assert(!sync_it->signal.empty());
					break;
				case RTLIL::SyncType::STa:
				case RTLIL::SyncType::STg:
				case RTLIL::SyncType::STi:
					log_assert(sync_it->signal.empty());
					break;
			}
		}
	}

	for (auto &it : module->connections_) {
		log_assert(it.first.size() == it.second.size());
		log_assert(!it.first.has_const());
		it.first.check(module);
		it.second.check(module);
	}

	for (auto &it : module->attributes)
		log_assert(!it.first.empty());
#endif
}

void RTLIL::Module::check()
{
	int pool_size = ThreadPool::work_pool_size(0, cells_size(), 1000);
	ParallelDispatchThreadPool thread_pool(pool_size);
	check_module(this, thread_pool);
}

void RTLIL::Module::optimize()
{
}

void RTLIL::Module::cloneInto(RTLIL::Module *new_mod, bool src_id_verbatim) const
{
	log_assert(new_mod->refcount_wires_ == 0);
	log_assert(new_mod->refcount_cells_ == 0);

	new_mod->avail_parameters = avail_parameters;
	new_mod->parameter_default_values = parameter_default_values;

	for (auto &conn : connections())
		new_mod->connect(conn);

	for (auto &attr : attributes)
		new_mod->attributes[attr.first] = attr.second;
	if (src_id_verbatim) {
		// Caller (Design::clone_into) copied twines wholesale, so
		// TwineRefs preserve their meaning. Allocate per-AttrObject
		// meta in dst's pool and copy the fields. dst's twine refcounts
		// were inherited via the wholesale copy and already account for
		// these new AttrObjects, so no retain on src.
		if (this->meta_ && new_mod->design) {
			// The Module::name masquerade write in clone() may have
			// pre-allocated this slot; reuse it so the name-write
			// before cloneInto isn't leaked.
			if (!new_mod->meta_)
				new_mod->meta_ = new_mod->design->alloc_obj_meta();
			*new_mod->meta_ = *this->meta_;
		}
	} else {
		// Transfer src across designs. Both modules must be attached
		// to a design for the migration to happen; in the
		// detached-clone() scratch flow (equiv_make, etc.) src is
		// dropped here — those callers don't preserve src across the
		// temp clone by design.
		if (this->design && new_mod->design)
			copy_src_into(this, this->design, new_mod, new_mod->design);
	}

	if (src_id_verbatim) {
		// Per-AttrObject meta clone via dst design's pool. TwineRefs for
		// src attributes transfer verbatim (twines was wholesale-copied).
		// name is re-interned by addWire/addCell; copy_meta restores it.
		auto copy_meta = [&](const RTLIL::AttrObject *src_obj, RTLIL::AttrObject *dst_obj) {
			if (!src_obj->meta_ || !new_mod->design)
				return;
			// Preserve name already set by addWire/addCell (in dst's pool).
			TwineRef saved_name = dst_obj->meta_ ? dst_obj->meta_->name : Twine::Null;
			// Recycle old meta slot (no field releases — name's retain lives on).
			if (dst_obj->meta_)
				new_mod->design->free_obj_meta(dst_obj->meta_);
			// Alloc new meta and struct-copy (src field is valid; name from
			// src pool is stale and will be overwritten).
			dst_obj->meta_ = new_mod->design->alloc_obj_meta();
			*dst_obj->meta_ = *src_obj->meta_;
			dst_obj->meta_->name = saved_name;
		};
		for (auto it = wires_.rbegin(); it != wires_.rend(); ++it) {
			const RTLIL::Wire *o = it->second;
			TwineRef dst_name = new_mod->design->twines.copy_from(design->twines, it->first);
			RTLIL::Wire *w = new_mod->addWire(dst_name, o->width);
			w->start_offset = o->start_offset;
			w->port_id = o->port_id;
			w->port_input = o->port_input;
			w->port_output = o->port_output;
			w->upto = o->upto;
			w->is_signed = o->is_signed;
			w->attributes = o->attributes;
			copy_meta(o, w);
		}
		for (auto it = memories.rbegin(); it != memories.rend(); ++it) {
			const RTLIL::Memory *o = it->second;
			TwineRef dst_name = new_mod->design->twines.copy_from(design->twines, it->first);
			RTLIL::Memory *m = new_mod->addMemory(dst_name);
			m->width = o->width;
			m->start_offset = o->start_offset;
			m->size = o->size;
			m->attributes = o->attributes;
			copy_meta(o, m);
		}
		for (auto it = cells_.rbegin(); it != cells_.rend(); ++it) {
			const RTLIL::Cell *o = it->second;
			TwineRef dst_name = new_mod->design->twines.copy_from(design->twines, it->first);
			RTLIL::Cell *c = new_mod->addCell(dst_name, o->type_impl);
			c->connections_ = o->connections_;
			c->parameters = o->parameters;
			c->attributes = o->attributes;
			copy_meta(o, c);
		}
		for (auto it = processes.rbegin(); it != processes.rend(); ++it) {
			const RTLIL::Process *o = it->second;
			TwineRef dst_name = new_mod->design->twines.copy_from(design->twines, it->first);
			RTLIL::Process *p = o->clone();
			if (!p->meta_)
				p->meta_ = new_mod->design->alloc_obj_meta();
			p->meta_->name = dst_name;
			new_mod->add(p);
			copy_meta(o, p);
			std::vector<std::pair<const RTLIL::CaseRule*, RTLIL::CaseRule*>> case_stack;
			case_stack.emplace_back(&o->root_case, &p->root_case);
			while (!case_stack.empty()) {
				auto [s_cs, d_cs] = case_stack.back();
				case_stack.pop_back();
				copy_meta(s_cs, d_cs);
				log_assert(s_cs->switches.size() == d_cs->switches.size());
				for (size_t i = 0; i < s_cs->switches.size(); i++) {
					const auto *s_sw = s_cs->switches[i];
					auto *d_sw = d_cs->switches[i];
					copy_meta(s_sw, d_sw);
					log_assert(s_sw->cases.size() == d_sw->cases.size());
					for (size_t j = 0; j < s_sw->cases.size(); j++)
						case_stack.emplace_back(s_sw->cases[j], d_sw->cases[j]);
				}
			}
			log_assert(o->syncs.size() == p->syncs.size());
			for (size_t i = 0; i < o->syncs.size(); i++) {
				const auto *s_sync = o->syncs[i];
				auto *d_sync = p->syncs[i];
				log_assert(s_sync->mem_write_actions.size() == d_sync->mem_write_actions.size());
				for (size_t j = 0; j < s_sync->mem_write_actions.size(); j++)
					copy_meta(&s_sync->mem_write_actions[j], &d_sync->mem_write_actions[j]);
			}
		}
	} else {
		// Iterate via rbegin/rend so we walk in forward INSERTION
		// order, not hashlib::dict's default reverse-insertion. The
		// TwinePool allocates slots sequentially as copy_src_into →
		// copy_from interns each wire's src, so the destination pool
		// ends up with leaves in the same order the frontend
		// originally interned them — that lets write_rtlil emit
		// byte-equal "@N" refs across single-module clones into an
		// existing destination design.
		// Re-intern each wire/cell name from the source design's pool into
		// the destination design's pool. copy_from is a no-op if both
		// designs share the same pool (same-design clone).
		for (auto it = wires_.rbegin(); it != wires_.rend(); ++it) {
			TwineRef dst_id = new_mod->design->twines.copy_from(design->twines, it->first);
			new_mod->addWire(dst_id, it->second);
		}

		for (auto it = memories.rbegin(); it != memories.rend(); ++it) {
			TwineRef dst_id = new_mod->design->twines.copy_from(design->twines, it->first);
			new_mod->addMemory(dst_id, it->second);
		}

		for (auto it = cells_.rbegin(); it != cells_.rend(); ++it) {
			TwineRef dst_id = new_mod->design->twines.copy_from(design->twines, it->first);
			new_mod->addCell(dst_id, it->second);
		}

		for (auto it = processes.rbegin(); it != processes.rend(); ++it) {
			TwineRef dst_id = new_mod->design->twines.copy_from(design->twines, it->first);
			new_mod->addProcess(dst_id, it->second);
		}
	}

	struct RewriteSigSpecWorker
	{
		RTLIL::Module *mod;
		void operator()(RTLIL::SigSpec &sig)
		{
			sig.rewrite_wires([this](RTLIL::Wire *&wire) {
				// wire points to original module; look up by name in new module.
				// Use the IdString materialisation path: works for both same-design
				// and cross-design clones without assuming pool identity.
				wire = mod->wire(wire->meta_->name);
			});
		}
	};

	RewriteSigSpecWorker rewriteSigSpecWorker;
	rewriteSigSpecWorker.mod = new_mod;
	new_mod->rewrite_sigspecs(rewriteSigSpecWorker);
	new_mod->fixup_ports();
}

RTLIL::Module *RTLIL::Module::clone() const
{
	RTLIL::Module *new_mod = new RTLIL::Module;
	new_mod->design = design;
	new_mod->meta_ = design->alloc_obj_meta();
	new_mod->meta_->name = meta_->name;
	cloneInto(new_mod);
	return new_mod;
}

RTLIL::Module *RTLIL::Module::clone(RTLIL::Design *dst, bool src_id_verbatim) const
{
	RTLIL::Module *new_mod = new RTLIL::Module;
	new_mod->design = dst;
	new_mod->meta_ = dst->alloc_obj_meta();
	new_mod->meta_->name = dst->twines.copy_from(design->twines, meta_->name);
	cloneInto(new_mod, src_id_verbatim);
	dst->add(new_mod);
	return new_mod;
}

RTLIL::Module *RTLIL::Module::clone(RTLIL::Design *dst, TwineRef target_name, bool src_id_verbatim) const
{
	RTLIL::Module *new_mod = new RTLIL::Module;
	new_mod->design = dst;
	new_mod->meta_ = dst->alloc_obj_meta();
	new_mod->meta_->name = target_name;
	cloneInto(new_mod, src_id_verbatim);
	dst->add(new_mod);
	return new_mod;
}

bool RTLIL::Module::has_memories() const
{
	return !memories.empty();
}

bool RTLIL::Module::has_processes() const
{
	return !processes.empty();
}

bool RTLIL::Module::has_memories_warn() const
{
	if (!memories.empty())
		log_warning("Ignoring module %s because it contains memories (run 'memory' command first).\n", this);
	return !memories.empty();
}

bool RTLIL::Module::has_processes_warn() const
{
	if (!processes.empty())
		log_warning("Ignoring module %s because it contains processes (run 'proc' command first).\n", this);
	return !processes.empty();
}

bool RTLIL::Module::is_selected() const
{
	return design->selected_module(this->meta_->name);
}

bool RTLIL::Module::is_selected_whole() const
{
	return design->selected_whole_module(this->meta_->name);
}

std::vector<RTLIL::Wire*> RTLIL::Module::selected_wires() const
{
	std::vector<RTLIL::Wire*> result;
	result.reserve(wires_.size());
	for (auto &it : wires_)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Cell*> RTLIL::Module::selected_cells() const
{
	std::vector<RTLIL::Cell*> result;
	result.reserve(cells_.size());
	for (auto &it : cells_)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Memory*> RTLIL::Module::selected_memories() const
{
	std::vector<RTLIL::Memory*> result;
	result.reserve(memories.size());
	for (auto &it : memories)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Process*> RTLIL::Module::selected_processes() const
{
	std::vector<RTLIL::Process*> result;
	result.reserve(processes.size());
	for (auto &it : processes)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::AttrObject*> RTLIL::Module::selected_members() const
{
	std::vector<RTLIL::AttrObject*> result;
	auto cells = selected_cells();
	auto memories = selected_memories();
	auto wires = selected_wires();
	auto processes = selected_processes();
	result.insert(result.end(), cells.begin(), cells.end());
	result.insert(result.end(), memories.begin(), memories.end());
	result.insert(result.end(), wires.begin(), wires.end());
	result.insert(result.end(), processes.begin(), processes.end());
	return result;
}

void RTLIL::Module::add(RTLIL::Wire *wire)
{
	log_assert(wire->meta_ && wire->meta_->name != Twine::Null);
	TwineRef id = wire->meta_->name;
	log_assert(wires_.count(id) == 0);
	log_assert(refcount_wires_ == 0);
	wires_[id] = wire;
	wire->module = this;
}

void RTLIL::Module::add(RTLIL::Cell *cell)
{
	log_assert(cell->meta_ && cell->meta_->name != Twine::Null);
	TwineRef id = cell->meta_->name;
	log_assert(cells_.count(id) == 0);
	log_assert(refcount_cells_ == 0);
	cells_[id] = cell;
	cell->module = this;
}

void RTLIL::Module::add(RTLIL::Process *process)
{
	log_assert(process->meta_ && process->meta_->name != Twine::Null);
	log_assert(count_id(process->meta_->name) == 0);
	processes[process->meta_->name] = process;
	process->module = this;
	// Propagate module back-pointer to every CaseRule/SwitchRule in the
	// root case tree and every MemWriteAction in the sync rules — so the
	// per-Design src meta vector can be resolved from any inner-process
	// AttrObject via `module->design` after attach.
	process->root_case.setModuleRecursive(this);
	for (auto *sync : process->syncs)
		for (auto &mwa : sync->mem_write_actions)
			mwa.module = this;
}

void RTLIL::Module::add(RTLIL::Binding *binding)
{
	log_assert(binding != nullptr);
	bindings_.push_back(binding);
}

void RTLIL::Module::remove(const pool<RTLIL::Wire*> &wires)
{
	log_assert(refcount_wires_ == 0);
	if (wires.empty())
		return;

	struct DeleteWireWorker
	{
		RTLIL::Module *module;
		const pool<RTLIL::Wire*> *wires_p;

		void operator()(RTLIL::SigSpec &sig) {
			sig.rewrite_wires([this](RTLIL::Wire *&wire) {
				if (wires_p->count(wire))
					wire = module->addWire(Twine{stringf("$delete_wire$%d", (int)autoidx++)}, wire->width);
			});
		}

		void operator()(RTLIL::SigSpec &lhs, RTLIL::SigSpec &rhs) {
			// If a deleted wire occurs on the lhs or rhs we just remove that part
			// of the assignment
			lhs.remove2(*wires_p, &rhs);
			rhs.remove2(*wires_p, &lhs);
		}
	};

	DeleteWireWorker delete_wire_worker;
	delete_wire_worker.module = this;
	delete_wire_worker.wires_p = &wires;
	rewrite_sigspecs2(delete_wire_worker);

	if (design->flagBufferedNormalized) {
		for (auto wire : wires) {
			buf_norm_wire_queue.erase(wire);
			buf_norm_connect_index.erase(wire);
		}
	}

	for (auto &it : wires) {
		log_assert(it->meta_ && it->meta_->name != Twine::Null);
		TwineRef id = it->meta_->name;
		log_assert(wires_.count(id) != 0);
		wires_.erase(id);
		delete it;  // Wire::~Wire releases src and name
	}
}

void RTLIL::Module::remove(RTLIL::Memory *memory)
{
	log_assert(memory->meta_ && memories.count(memory->meta_->name) != 0);
	memories.erase(memory->meta_->name);
	delete memory;
}

void RTLIL::Module::remove(RTLIL::Process *process)
{
	log_assert(process->meta_ && processes.count(process->meta_->name) != 0);
	processes.erase(process->meta_->name);
	delete process;
}

void RTLIL::Module::rename(RTLIL::Wire *wire, TwineRef new_name)
{
	log_assert(wire->meta_ && wire->meta_->name != Twine::Null);
	TwineRef old_id = wire->meta_->name;
	log_assert(wires_[old_id] == wire);
	log_assert(refcount_wires_ == 0);
	wires_.erase(old_id);
	wire->meta_->name = new_name;
	// design->obj_set_name(wire, new_name);
	add(wire);
}

void RTLIL::Module::rename(RTLIL::Cell *cell, TwineRef new_name)
{
	log_assert(cell->meta_ && cell->meta_->name != Twine::Null);
	TwineRef old_id = cell->meta_->name;
	log_assert(cells_[old_id] == cell);
	log_assert(refcount_cells_ == 0);
	cells_.erase(old_id);
	cell->meta_->name = new_name;
	add(cell);
}

void RTLIL::Module::rename(TwineRef old_name, TwineRef new_name)
{
	TwineRef old_id = old_name;
	if (old_id != Twine::Null && wires_.count(old_id))
		rename(wires_.at(old_id), new_name);
	else if (old_id != Twine::Null && cells_.count(old_id))
		rename(cells_.at(old_id), new_name);
	else
		log_abort();
}

void RTLIL::Module::swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2)
{
	log_assert(w1->meta_ && w1->meta_->name != Twine::Null);
	log_assert(w2->meta_ && w2->meta_->name != Twine::Null);
	TwineRef id1 = w1->meta_->name;
	TwineRef id2 = w2->meta_->name;
	log_assert(wires_[id1] == w1);
	log_assert(wires_[id2] == w2);
	log_assert(refcount_wires_ == 0);

	// Swap dict entries and names; refcounts don't change.
	wires_[id1] = w2;
	wires_[id2] = w1;
	std::swap(w1->meta_->name, w2->meta_->name);
}

void RTLIL::Module::swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2)
{
	log_assert(c1->meta_ && c1->meta_->name != Twine::Null);
	log_assert(c2->meta_ && c2->meta_->name != Twine::Null);
	TwineRef id1 = c1->meta_->name;
	TwineRef id2 = c2->meta_->name;
	log_assert(cells_[id1] == c1);
	log_assert(cells_[id2] == c2);
	log_assert(refcount_cells_ == 0);

	// Swap dict entries and names; refcounts don't change.
	cells_[id1] = c2;
	cells_[id2] = c1;
	std::swap(c1->meta_->name, c2->meta_->name);
}

TwineRef RTLIL::Module::uniquify(TwineRef name)
{
	int index = 0;
	return uniquify(name, index);
}

TwineRef RTLIL::Module::uniquify(Twine&& name)
{
	return uniquify(design->twines.add(Twine{std::move(name)}));
}

TwineRef RTLIL::Module::uniquify(TwineRef name, int &index)
{
	if (index == 0) {
		if (count_id(name) == 0)
			return name;
		index++;
	}

	while (1) {
		TwineRef new_name = twine_tag(design->twines.add(Twine{Twine::Suffix{name, stringf("_%d", index)}}), twine_is_public(name));
		if (count_id(new_name) == 0)
			return new_name;
		index++;
	}
}

TwineRef RTLIL::Module::uniquify(Twine&& name, int &index)
{
	return uniquify(design->twines.add(Twine{std::move(name)}), index);
}

static bool fixup_ports_compare(const RTLIL::Wire *a, const RTLIL::Wire *b)
{
	if (a->port_id && !b->port_id)
		return true;
	if (!a->port_id && b->port_id)
		return false;

	if (a->port_id == b->port_id)
		return a->name < b->name;
	return a->port_id < b->port_id;
}

void RTLIL::Module::connect(const RTLIL::SigSig &conn)
{
	for (auto mon : monitors)
		mon->notify_connect(this, conn);

	if (design)
		for (auto mon : design->monitors)
			mon->notify_connect(this, conn);

	// ignore all attempts to assign constants to other constants
	if (conn.first.has_const()) {
		RTLIL::SigSig new_conn;
		for (int i = 0; i < GetSize(conn.first); i++)
			if (conn.first[i].wire) {
				new_conn.first.append(conn.first[i]);
				new_conn.second.append(conn.second[i]);
			}
		if (GetSize(new_conn.first))
			connect(new_conn);
		return;
	}

	if (yosys_xtrace) {
		log("#X# Connect (SigSig) in %s: %s = %s (%d bits)\n", this, log_signal(conn.first), log_signal(conn.second), GetSize(conn.first));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	log_assert(GetSize(conn.first) == GetSize(conn.second));
	connections_.push_back(conn);
}

void RTLIL::Module::connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs)
{
	connect(RTLIL::SigSig(lhs, rhs));
}


void RTLIL::Module::fixup_ports()
{
	std::vector<RTLIL::Wire*> all_ports;

	for (auto &w : wires_)
		if (w.second->port_input || w.second->port_output)
			all_ports.push_back(w.second);
		else
			w.second->port_id = 0;

	std::sort(all_ports.begin(), all_ports.end(), fixup_ports_compare);

	if (design && design->flagBufferedNormalized) {
		for (auto &w : wires_)
			if (w.second->driverCell_ && w.second->driverCell_->type == TW($input_port))
				buf_norm_wire_queue.insert(w.second);

		buf_norm_wire_queue.insert(all_ports.begin(), all_ports.end());
	}

	ports.clear();
	for (size_t i = 0; i < all_ports.size(); i++) {
		ports.push_back(all_ports[i]->meta_->name);
		all_ports[i]->port_id = i+1;
	}
}

RTLIL::Wire *RTLIL::Module::addWire(TwineRef name, int width)
{
	log_assert(design);
	RTLIL::Wire *wire = new RTLIL::Wire(Wire::ConstructToken{});
	wire->width = width;
	if (!wire->meta_)
		wire->meta_ = design->alloc_obj_meta();
	wire->meta_->name = name;
	add(wire);
	return wire;
}

RTLIL::Wire *RTLIL::Module::addWire(Twine &&name, int width)
{
	log_assert(design);
	return addWire(design->twines.add(std::move(name)), width);
}

RTLIL::Wire *RTLIL::Module::addWire(TwineRef name, const RTLIL::Wire *other)
{
	RTLIL::Wire *wire = addWire(name);
	wire->width = other->width;
	wire->start_offset = other->start_offset;
	wire->port_id = other->port_id;
	wire->port_input = other->port_input;
	wire->port_output = other->port_output;
	wire->upto = other->upto;
	wire->is_signed = other->is_signed;
	wire->attributes = other->attributes;
	{
		const RTLIL::Design *src_design = other->module ? other->module->design : nullptr;
		if (src_design && this->design)
			copy_src_into(other, src_design, wire, this->design);
	}
	return wire;
}

RTLIL::Wire *RTLIL::Module::addWire(Twine &&name, const RTLIL::Wire *other)
{
	log_assert(design);
	return addWire(design->twines.add(std::move(name)), other);
}

RTLIL::Cell *RTLIL::Module::addCell(TwineRef name, TwineRef type)
{
	log_assert(design);
	RTLIL::Cell *cell = new RTLIL::Cell(Cell::ConstructToken{});
	cell->type_impl = type;
	if (!cell->meta_)
		cell->meta_ = design->alloc_obj_meta();
	cell->meta_->name = name;
	add(cell);
	return cell;
}

RTLIL::Cell *RTLIL::Module::addCell(Twine &&name, TwineRef type)
{
	log_assert(design);
	return addCell(design->twines.add(std::move(name)), type);
}

RTLIL::Cell *RTLIL::Module::addCell(TwineRef name, Twine &&type)
{
	log_assert(design);
	return addCell(std::move(name), design->twines.add(std::move(type)));
}

RTLIL::Cell *RTLIL::Module::addCell(Twine name, Twine type)
{
	log_assert(design);
	return addCell(design->twines.add(std::move(name)), design->twines.add(std::move(type)));
}

RTLIL::Cell *RTLIL::Module::addCell(TwineRef name, const RTLIL::Cell *other)
{
	RTLIL::Cell *cell = addCell(name, other->type_impl);
	cell->connections_ = other->connections_;
	cell->parameters = other->parameters;
	cell->attributes = other->attributes;
	{
		const RTLIL::Design *src_design = other->module ? other->module->design : nullptr;
		if (src_design && this->design)
			copy_src_into(other, src_design, cell, this->design);
	}
	return cell;
}

RTLIL::Cell *RTLIL::Module::addCell(Twine &&name, const RTLIL::Cell *other)
{
	log_assert(design);
	return addCell(design->twines.add(std::move(name)), other);
}

RTLIL::Memory *RTLIL::Module::addMemory(TwineRef name)
{
	log_assert(design);
	RTLIL::Memory *mem = new RTLIL::Memory;
	mem->module = this;
	mem->meta_ = design->alloc_obj_meta();
	mem->meta_->name = name;
	memories[name] = mem;
	return mem;
}

RTLIL::Memory *RTLIL::Module::addMemory(Twine &&name)
{
	log_assert(design);
	return addMemory(design->twines.add(std::move(name)));
}

RTLIL::Memory *RTLIL::Module::addMemory(TwineRef name, const RTLIL::Memory *other)
{
	log_assert(design);
	RTLIL::Memory *mem = new RTLIL::Memory;
	mem->module = this;
	mem->meta_ = design->alloc_obj_meta();
	mem->meta_->name = name;
	mem->width = other->width;
	mem->start_offset = other->start_offset;
	mem->size = other->size;
	mem->attributes = other->attributes;
	{
		// Clone path drops src for now — caller responsible for migrating
		// src across the design boundary if needed. addMemory(name) is the
		// common case.
		(void)other;
	}
	memories[name] = mem;
	return mem;
}

RTLIL::Process *RTLIL::Module::addProcess(TwineRef name)
{
	log_assert(design);
	RTLIL::Process *proc = new RTLIL::Process;
	proc->meta_ = design->alloc_obj_meta();
	proc->meta_->name = name;
	add(proc);
	return proc;
}

RTLIL::Process *RTLIL::Module::addProcess(Twine &&name)
{
	log_assert(design);
	return addProcess(design->twines.add(std::move(name)));
}

namespace {
	// Walk two process trees in parallel and transfer src across the
	// design boundary for every AttrObject (CaseRule, SwitchRule,
	// MemWriteAction). Process::clone() drops src on these inner objects
	// because they have no pool backpointer; this restores it now that
	// both source and destination designs are known.
	void migrate_process_tree_src(const RTLIL::Process *src, const RTLIL::Design *src_design,
			RTLIL::Process *dst, RTLIL::Design *dst_design)
	{
		if (!src_design || !dst_design)
			return;
		// Top-level Process src is handled by the addProcess() caller via
		// copy_src_into; here we only walk inner objects.
		std::vector<std::pair<const RTLIL::CaseRule*, RTLIL::CaseRule*>> case_stack;
		case_stack.emplace_back(&src->root_case, &dst->root_case);
		while (!case_stack.empty()) {
			auto [s_cs, d_cs] = case_stack.back();
			case_stack.pop_back();
			copy_src_into(s_cs, src_design, d_cs, dst_design);
			log_assert(s_cs->switches.size() == d_cs->switches.size());
			for (size_t i = 0; i < s_cs->switches.size(); i++) {
				const auto *s_sw = s_cs->switches[i];
				auto *d_sw = d_cs->switches[i];
				copy_src_into(s_sw, src_design, d_sw, dst_design);
				log_assert(s_sw->cases.size() == d_sw->cases.size());
				for (size_t j = 0; j < s_sw->cases.size(); j++)
					case_stack.emplace_back(s_sw->cases[j], d_sw->cases[j]);
			}
		}
		log_assert(src->syncs.size() == dst->syncs.size());
		for (size_t i = 0; i < src->syncs.size(); i++) {
			const auto *s_sync = src->syncs[i];
			auto *d_sync = dst->syncs[i];
			log_assert(s_sync->mem_write_actions.size() == d_sync->mem_write_actions.size());
			for (size_t j = 0; j < s_sync->mem_write_actions.size(); j++)
				copy_src_into(&s_sync->mem_write_actions[j], src_design,
						&d_sync->mem_write_actions[j], dst_design);
		}
	}
}

RTLIL::Process *RTLIL::Module::addProcess(TwineRef name, const RTLIL::Process *other)
{
	log_assert(design);
	RTLIL::Process *proc = other->clone();
	if (!proc->meta_)
		proc->meta_ = design->alloc_obj_meta();
	proc->meta_->name = name;
	add(proc);
	// Migrate src across the design boundary for the inner-process tree.
	// Process::clone drops src on CaseRule/SwitchRule/MemWriteAction since
	// those types have no module backpointer; with both designs now known
	// (other's via other->module->design; ours via this->design) we can
	// walk in parallel and migrate.
	if (other->module && other->module->design && this->design) {
		const RTLIL::Design *src_design = other->module->design;
		RTLIL::Design *dst_design = this->design;
		// Top-level Process src.
		copy_src_into(other, src_design, proc, dst_design);
		// Inner tree.
		migrate_process_tree_src(other, src_design, proc, dst_design);
	}
	return proc;
}

	#define DEF_METHOD(_func, _y_size, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool is_signed, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);           \
			cell->parameters[ID::A_SIGNED] = is_signed;         \
			cell->parameters[ID::A_WIDTH] = sig_a.size();       \
			cell->parameters[ID::Y_WIDTH] = sig_y.size();       \
			cell->setPort(TW::A, sig_a);                        \
			cell->setPort(TW::Y, sig_y);                        \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                       \
			return cell;                                        \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, bool is_signed, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _y_size);    \
			add ## _func(std::move(name), sig_a, sig_y, is_signed, src);   \
			return sig_y;                                       \
		}
	DEF_METHOD(Not,        sig_a.size(), TW($not))
	DEF_METHOD(Pos,        sig_a.size(), TW($pos))
	DEF_METHOD(Neg,        sig_a.size(), TW($neg))
	DEF_METHOD(ReduceAnd,  1, TW($reduce_and))
	DEF_METHOD(ReduceOr,   1, TW($reduce_or))
	DEF_METHOD(ReduceXor,  1, TW($reduce_xor))
	DEF_METHOD(ReduceXnor, 1, TW($reduce_xnor))
	DEF_METHOD(ReduceBool, 1, TW($reduce_bool))
	DEF_METHOD(LogicNot,   1, TW($logic_not))
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _y_size, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, bool /* is_signed */, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);           \
			cell->parameters[ID::WIDTH] = sig_a.size();         \
			cell->setPort(TW::A, sig_a);                        \
			cell->setPort(TW::Y, sig_y);                        \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                       \
			return cell;                                        \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, bool is_signed, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _y_size);    \
			add ## _func(std::move(name), sig_a, sig_y, is_signed, src);   \
			return sig_y;                                       \
		}
	DEF_METHOD(Buf, sig_a.size(), TW($buf))
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _y_size, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);           \
			cell->parameters[ID::A_SIGNED] = is_signed;         \
			cell->parameters[ID::B_SIGNED] = is_signed;         \
			cell->parameters[ID::A_WIDTH] = sig_a.size();       \
			cell->parameters[ID::B_WIDTH] = sig_b.size();       \
			cell->parameters[ID::Y_WIDTH] = sig_y.size();       \
			cell->setPort(TW::A, sig_a);                        \
			cell->setPort(TW::B, sig_b);                        \
			cell->setPort(TW::Y, sig_y);                        \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                       \
			return cell;                                        \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _y_size);         \
			add ## _func(std::move(name), sig_a, sig_b, sig_y, is_signed, src); \
			return sig_y;                                            \
		}
	DEF_METHOD(And,      max(sig_a.size(), sig_b.size()), TW($and))
	DEF_METHOD(Or,       max(sig_a.size(), sig_b.size()), TW($or))
	DEF_METHOD(Xor,      max(sig_a.size(), sig_b.size()), TW($xor))
	DEF_METHOD(Xnor,     max(sig_a.size(), sig_b.size()), TW($xnor))
	DEF_METHOD(Shift,    sig_a.size(), TW($shift))
	DEF_METHOD(Lt,       1, TW($lt))
	DEF_METHOD(Le,       1, TW($le))
	DEF_METHOD(Eq,       1, TW($eq))
	DEF_METHOD(Ne,       1, TW($ne))
	DEF_METHOD(Eqx,      1, TW($eqx))
	DEF_METHOD(Nex,      1, TW($nex))
	DEF_METHOD(Ge,       1, TW($ge))
	DEF_METHOD(Gt,       1, TW($gt))
	DEF_METHOD(Add,      max(sig_a.size(), sig_b.size()), TW($add))
	DEF_METHOD(Sub,      max(sig_a.size(), sig_b.size()), TW($sub))
	DEF_METHOD(Mul,      max(sig_a.size(), sig_b.size()), TW($mul))
	DEF_METHOD(Div,      max(sig_a.size(), sig_b.size()), TW($div))
	DEF_METHOD(Mod,      max(sig_a.size(), sig_b.size()), TW($mod))
	DEF_METHOD(DivFloor, max(sig_a.size(), sig_b.size()), TW($divfloor))
	DEF_METHOD(ModFloor, max(sig_a.size(), sig_b.size()), TW($modfloor))
	DEF_METHOD(LogicAnd, 1, TW($logic_and))
	DEF_METHOD(LogicOr,  1, TW($logic_or))
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _y_size, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);           \
			cell->parameters[ID::A_SIGNED] = is_signed;         \
			cell->parameters[ID::B_SIGNED] = false;             \
			cell->parameters[ID::A_WIDTH] = sig_a.size();       \
			cell->parameters[ID::B_WIDTH] = sig_b.size();       \
			cell->parameters[ID::Y_WIDTH] = sig_y.size();       \
			cell->setPort(TW::A, sig_a);                        \
			cell->setPort(TW::B, sig_b);                        \
			cell->setPort(TW::Y, sig_y);                        \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                       \
			return cell;                                        \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _y_size);         \
			add ## _func(std::move(name), sig_a, sig_b, sig_y, is_signed, src); \
			return sig_y;                                            \
		}
	DEF_METHOD(Shl,      sig_a.size(), TW($shl))
	DEF_METHOD(Shr,      sig_a.size(), TW($shr))
	DEF_METHOD(Sshl,     sig_a.size(), TW($sshl))
	DEF_METHOD(Sshr,     sig_a.size(), TW($sshr))
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _y_size, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool is_signed, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);           \
			cell->parameters[ID::A_SIGNED] = false;             \
			cell->parameters[ID::B_SIGNED] = is_signed;         \
			cell->parameters[ID::A_WIDTH] = sig_a.size();       \
			cell->parameters[ID::B_WIDTH] = sig_b.size();       \
			cell->parameters[ID::Y_WIDTH] = sig_y.size();       \
			cell->setPort(TW::A, sig_a);                        \
			cell->setPort(TW::B, sig_b);                        \
			cell->setPort(TW::Y, sig_y);                        \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                       \
			return cell;                                        \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, bool is_signed, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _y_size);         \
			add ## _func(std::move(name), sig_a, sig_b, sig_y, is_signed, src); \
			return sig_y;                                            \
		}
	DEF_METHOD(Shiftx,      sig_a.size(), TW($shiftx))
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _type, _pmux) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);                 \
			cell->parameters[ID::WIDTH] = sig_a.size();               \
			if (_pmux) cell->parameters[ID::S_WIDTH] = sig_s.size();  \
			cell->setPort(TW::A, sig_a);                              \
			cell->setPort(TW::B, sig_b);                              \
			cell->setPort(TW::S, sig_s);                              \
			cell->setPort(TW::Y, sig_y);                              \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                             \
			return cell;                                              \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_s, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, sig_a.size());     \
			add ## _func(std::move(name), sig_a, sig_b, sig_s, sig_y, src);      \
			return sig_y;                                             \
		}
	DEF_METHOD(Mux,      TW($mux),        0)
	DEF_METHOD(Bwmux,    TW($bwmux),      0)
	DEF_METHOD(Pmux,     TW($pmux),       1)
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _type, _demux) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_y, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);                 \
			cell->parameters[ID::WIDTH] = _demux ? sig_a.size() : sig_y.size(); \
			cell->parameters[ID::S_WIDTH] = sig_s.size();             \
			cell->setPort(TW::A, sig_a);                              \
			cell->setPort(TW::S, sig_s);                              \
			cell->setPort(TW::Y, sig_y);                              \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                             \
			return cell;                                              \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, _demux ? sig_a.size() << sig_s.size() : sig_a.size() >> sig_s.size()); \
			add ## _func(std::move(name), sig_a, sig_s, sig_y, src);             \
			return sig_y;                                             \
		}
	DEF_METHOD(Bmux,     TW($bmux),       0)
	DEF_METHOD(Demux,    TW($demux),      1)
	#undef DEF_METHOD

	#define DEF_METHOD(_func, _type) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);                 \
			cell->parameters[ID::WIDTH] = sig_a.size();               \
			cell->setPort(TW::A, sig_a);                              \
			cell->setPort(TW::B, sig_b);                              \
			cell->setPort(TW::Y, sig_y);                              \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                             \
			return cell;                                              \
		} \
		template<typename Derived> RTLIL::SigSpec CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, TwineRef src) { \
			RTLIL::SigSpec sig_y = static_cast<Derived*>(this)->addWire(NEW_TWINE, sig_a.size());     \
			add ## _func(std::move(name), sig_a, sig_s, sig_y, src);             \
			return sig_y;                                             \
		}
	DEF_METHOD(Bweqx,    TW($bweqx))
	#undef DEF_METHOD

	#define DEF_METHOD_2(_func, _type, _P1, _P2) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);         \
			cell->setPort(TW::_P1, sig1);                   \
			cell->setPort(TW::_P2, sig2);                   \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                     \
			return cell;                                      \
		} \
		template<typename Derived> RTLIL::SigBit CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigBit &sig1, TwineRef src) { \
			RTLIL::SigBit sig2 = static_cast<Derived*>(this)->addWire(NEW_TWINE);             \
			add ## _func(std::move(name), sig1, sig2, src);              \
			return sig2;                                      \
		}
	#define DEF_METHOD_3(_func, _type, _P1, _P2, _P3) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, const RTLIL::SigBit &sig3, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);         \
			cell->setPort(TW::_P1, sig1);                   \
			cell->setPort(TW::_P2, sig2);                   \
			cell->setPort(TW::_P3, sig3);                   \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                     \
			return cell;                                      \
		} \
		template<typename Derived> RTLIL::SigBit CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, TwineRef src) { \
			RTLIL::SigBit sig3 = static_cast<Derived*>(this)->addWire(NEW_TWINE);             \
			add ## _func(std::move(name), sig1, sig2, sig3, src);        \
			return sig3;                                      \
		}
	#define DEF_METHOD_4(_func, _type, _P1, _P2, _P3, _P4) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, const RTLIL::SigBit &sig3, const RTLIL::SigBit &sig4, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);         \
			cell->setPort(TW::_P1, sig1);                   \
			cell->setPort(TW::_P2, sig2);                   \
			cell->setPort(TW::_P3, sig3);                   \
			cell->setPort(TW::_P4, sig4);                   \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                     \
			return cell;                                      \
		} \
		template<typename Derived> RTLIL::SigBit CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, const RTLIL::SigBit &sig3, TwineRef src) { \
			RTLIL::SigBit sig4 = static_cast<Derived*>(this)->addWire(NEW_TWINE);             \
			add ## _func(std::move(name), sig1, sig2, sig3, sig4, src);  \
			return sig4;                                      \
		}
	#define DEF_METHOD_5(_func, _type, _P1, _P2, _P3, _P4, _P5) \
		template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::add ## _func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, const RTLIL::SigBit &sig3, const RTLIL::SigBit &sig4, const RTLIL::SigBit &sig5, TwineRef src) { \
			RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _type);         \
			cell->setPort(TW::_P1, sig1);                   \
			cell->setPort(TW::_P2, sig2);                   \
			cell->setPort(TW::_P3, sig3);                   \
			cell->setPort(TW::_P4, sig4);                   \
			cell->setPort(TW::_P5, sig5);                   \
			static_cast<Derived*>(this)->cell_set_src(cell, src);                     \
			return cell;                                      \
		} \
		template<typename Derived> RTLIL::SigBit CellAdderMixin<Derived>::_func(Twine &&name, const RTLIL::SigBit &sig1, const RTLIL::SigBit &sig2, const RTLIL::SigBit &sig3, const RTLIL::SigBit &sig4, TwineRef src) { \
			RTLIL::SigBit sig5 = static_cast<Derived*>(this)->addWire(NEW_TWINE);                  \
			add ## _func(std::move(name), sig1, sig2, sig3, sig4, sig5, src); \
			return sig5;                                           \
		}
	DEF_METHOD_2(BufGate,    TW($_BUF_),    A, Y)
	DEF_METHOD_2(NotGate,    TW($_NOT_),    A, Y)
	DEF_METHOD_3(AndGate,    TW($_AND_),    A, B, Y)
	DEF_METHOD_3(NandGate,   TW($_NAND_),   A, B, Y)
	DEF_METHOD_3(OrGate,     TW($_OR_),     A, B, Y)
	DEF_METHOD_3(NorGate,    TW($_NOR_),    A, B, Y)
	DEF_METHOD_3(XorGate,    TW($_XOR_),    A, B, Y)
	DEF_METHOD_3(XnorGate,   TW($_XNOR_),   A, B, Y)
	DEF_METHOD_3(AndnotGate, TW($_ANDNOT_), A, B, Y)
	DEF_METHOD_3(OrnotGate,  TW($_ORNOT_),  A, B, Y)
	DEF_METHOD_4(MuxGate,    TW($_MUX_),    A, B, S, Y)
	DEF_METHOD_4(NmuxGate,   TW($_NMUX_),   A, B, S, Y)
	DEF_METHOD_4(Aoi3Gate,   TW($_AOI3_),   A, B, C, Y)
	DEF_METHOD_4(Oai3Gate,   TW($_OAI3_),   A, B, C, Y)
	DEF_METHOD_5(Aoi4Gate,   TW($_AOI4_),   A, B, C, D, Y)
	DEF_METHOD_5(Oai4Gate,   TW($_OAI4_),   A, B, C, D, Y)
	#undef DEF_METHOD_2
	#undef DEF_METHOD_3
	#undef DEF_METHOD_4
	#undef DEF_METHOD_5

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addPow(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, bool a_signed, bool b_signed, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($pow));
		cell->parameters[ID::A_SIGNED] = a_signed;
		cell->parameters[ID::B_SIGNED] = b_signed;
		cell->parameters[ID::A_WIDTH] = sig_a.size();
		cell->parameters[ID::B_WIDTH] = sig_b.size();
		cell->parameters[ID::Y_WIDTH] = sig_y.size();
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::B, sig_b);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addFa(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_c, const RTLIL::SigSpec &sig_x, const RTLIL::SigSpec &sig_y, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($fa));
		cell->parameters[ID::WIDTH] = sig_a.size();
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::B, sig_b);
		cell->setPort(TW::C, sig_c);
		cell->setPort(TW::X, sig_x);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSlice(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, RTLIL::Const offset, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($slice));
		cell->parameters[ID::A_WIDTH] = sig_a.size();
		cell->parameters[ID::Y_WIDTH] = sig_y.size();
		cell->parameters[ID::OFFSET] = offset;
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addConcat(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($concat));
		cell->parameters[ID::A_WIDTH] = sig_a.size();
		cell->parameters[ID::B_WIDTH] = sig_b.size();
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::B, sig_b);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addLut(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_y, RTLIL::Const lut, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($lut));
		cell->parameters[ID::LUT] = lut;
		cell->parameters[ID::WIDTH] = sig_a.size();
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addTribuf(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_y, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($tribuf));
		cell->parameters[ID::WIDTH] = sig_a.size();
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAssert(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($assert));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAssume(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($assume));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addLive(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($live));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addFair(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($fair));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addCover(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_en, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($cover));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::EN, sig_en);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addEquiv(Twine &&name, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_b, const RTLIL::SigSpec &sig_y, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($equiv));
		cell->setPort(TW::A, sig_a);
		cell->setPort(TW::B, sig_b);
		cell->setPort(TW::Y, sig_y);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSr(Twine &&name, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr, const RTLIL::SigSpec &sig_q, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($sr));
		cell->parameters[ID::SET_POLARITY] = set_polarity;
		cell->parameters[ID::CLR_POLARITY] = clr_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::SET, sig_set);
		cell->setPort(TW::CLR, sig_clr);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addFf(Twine &&name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($ff));
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDff(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dff));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffe(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool en_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dffe));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffsr(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dffsr));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::SET_POLARITY] = set_polarity;
		cell->parameters[ID::CLR_POLARITY] = clr_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::SET, sig_set);
		cell->setPort(TW::CLR, sig_clr);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffsre(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool en_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dffsre));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::SET_POLARITY] = set_polarity;
		cell->parameters[ID::CLR_POLARITY] = clr_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::SET, sig_set);
		cell->setPort(TW::CLR, sig_clr);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdff(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const arst_value, bool clk_polarity, bool arst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($adff));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::ARST_POLARITY] = arst_polarity;
		cell->parameters[ID::ARST_VALUE] = arst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::ARST, sig_arst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdffe(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const arst_value, bool clk_polarity, bool en_polarity, bool arst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($adffe));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::ARST_POLARITY] = arst_polarity;
		cell->parameters[ID::ARST_VALUE] = arst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::ARST, sig_arst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAldff(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity, bool aload_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($aldff));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::ALOAD_POLARITY] = aload_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::ALOAD, sig_aload);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::AD, sig_ad);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAldffe(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity, bool en_polarity, bool aload_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($aldffe));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::ALOAD_POLARITY] = aload_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::ALOAD, sig_aload);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::AD, sig_ad);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdff(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const srst_value, bool clk_polarity, bool srst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($sdff));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::SRST_POLARITY] = srst_polarity;
		cell->parameters[ID::SRST_VALUE] = srst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::SRST, sig_srst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdffe(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const srst_value, bool clk_polarity, bool en_polarity, bool srst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($sdffe));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::SRST_POLARITY] = srst_polarity;
		cell->parameters[ID::SRST_VALUE] = srst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::SRST, sig_srst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdffce(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const srst_value, bool clk_polarity, bool en_polarity, bool srst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($sdffce));
		cell->parameters[ID::CLK_POLARITY] = clk_polarity;
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::SRST_POLARITY] = srst_polarity;
		cell->parameters[ID::SRST_VALUE] = srst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::CLK, sig_clk);
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::SRST, sig_srst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDlatch(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dlatch));
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdlatch(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			RTLIL::Const arst_value, bool en_polarity, bool arst_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($adlatch));
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::ARST_POLARITY] = arst_polarity;
		cell->parameters[ID::ARST_VALUE] = arst_value;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::ARST, sig_arst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDlatchsr(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($dlatchsr));
		cell->parameters[ID::EN_POLARITY] = en_polarity;
		cell->parameters[ID::SET_POLARITY] = set_polarity;
		cell->parameters[ID::CLR_POLARITY] = clr_polarity;
		cell->parameters[ID::WIDTH] = sig_q.size();
		cell->setPort(TW::EN, sig_en);
		cell->setPort(TW::SET, sig_set);
		cell->setPort(TW::CLR, sig_clr);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	static TwinePool& _cell_adder_twines(RTLIL::Module* m) { return m->design->twines; }
	static TwinePool& _cell_adder_twines(RTLIL::Patch* p) { return p->mod->design->twines; }

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSrGate(Twine &&name, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			const RTLIL::SigSpec &sig_q, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_SR_%c%c_", set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::S, sig_set);
		cell->setPort(TW::R, sig_clr);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addFfGate(Twine &&name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, TwineRef src)
	{
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), TW($_FF_));
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFF_%c_", clk_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffeGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool en_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFFE_%c%c_", clk_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffsrGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFFSR_%c%c%c_", clk_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::S, sig_set);
		cell->setPort(TW::R, sig_clr);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDffsreGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool clk_polarity, bool en_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFFSRE_%c%c%c%c_", clk_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::S, sig_set);
		cell->setPort(TW::R, sig_clr);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdffGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value, bool clk_polarity, bool arst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFF_%c%c%c_", clk_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::R, sig_arst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdffeGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value, bool clk_polarity, bool en_polarity, bool arst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DFFE_%c%c%c%c_", clk_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::R, sig_arst);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAldffGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity, bool aload_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_ALDFF_%c%c_", clk_polarity ? 'P' : 'N', aload_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::L, sig_aload);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::AD, sig_ad);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAldffeGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_aload, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			const RTLIL::SigSpec &sig_ad, bool clk_polarity, bool en_polarity, bool aload_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_ALDFFE_%c%c%c_", clk_polarity ? 'P' : 'N', aload_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::L, sig_aload);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::AD, sig_ad);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdffGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value, bool clk_polarity, bool srst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_SDFF_%c%c%c_", clk_polarity ? 'P' : 'N', srst_polarity ? 'P' : 'N', srst_value ? '1' : '0')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::R, sig_srst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdffeGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value, bool clk_polarity, bool en_polarity, bool srst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_SDFFE_%c%c%c%c_", clk_polarity ? 'P' : 'N', srst_polarity ? 'P' : 'N', srst_value ? '1' : '0', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::R, sig_srst);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addSdffceGate(Twine &&name, const RTLIL::SigSpec &sig_clk, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_srst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool srst_value, bool clk_polarity, bool en_polarity, bool srst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_SDFFCE_%c%c%c%c_", clk_polarity ? 'P' : 'N', srst_polarity ? 'P' : 'N', srst_value ? '1' : '0', en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::C, sig_clk);
		cell->setPort(TW::R, sig_srst);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDlatchGate(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DLATCH_%c_", en_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addAdlatchGate(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_arst, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q,
			bool arst_value, bool en_polarity, bool arst_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DLATCH_%c%c%c_", en_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::R, sig_arst);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

	template<typename Derived> RTLIL::Cell* CellAdderMixin<Derived>::addDlatchsrGate(Twine &&name, const RTLIL::SigSpec &sig_en, const RTLIL::SigSpec &sig_set, const RTLIL::SigSpec &sig_clr,
			RTLIL::SigSpec sig_d, const RTLIL::SigSpec &sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, TwineRef src)
	{
		TwineRef _t = _cell_adder_twines(static_cast<Derived*>(this)).add(Twine{stringf("$_DLATCHSR_%c%c%c_", en_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N')});
		RTLIL::Cell *cell = static_cast<Derived*>(this)->addCell(std::move(name), _t);
		cell->setPort(TW::E, sig_en);
		cell->setPort(TW::S, sig_set);
		cell->setPort(TW::R, sig_clr);
		cell->setPort(TW::D, sig_d);
		cell->setPort(TW::Q, sig_q);
		static_cast<Derived*>(this)->cell_set_src(cell, src);
		return cell;
	}

RTLIL::Cell* RTLIL::Module::addAnyinit(TwineRef name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, TwineRef src)
{
	RTLIL::Cell *cell = addCell(name, TW($anyinit));
	cell->parameters[ID::WIDTH] = sig_q.size();
	cell->setPort(TW::D, sig_d);
	cell->setPort(TW::Q, sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAnyinit(Twine &&name, const RTLIL::SigSpec &sig_d, const RTLIL::SigSpec &sig_q, TwineRef src)
{
	return addAnyinit(design->twines.add(std::move(name)), sig_d, sig_q, src);
}

RTLIL::SigSpec RTLIL::Module::Anyconst(TwineRef name, int width, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, width);
	Cell *cell = addCell(name, TW($anyconst));
	cell->setParam(ID::WIDTH, width);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Anyseq(TwineRef name, int width, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, width);
	Cell *cell = addCell(name, TW($anyseq));
	cell->setParam(ID::WIDTH, width);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Allconst(TwineRef name, int width, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, width);
	Cell *cell = addCell(name, TW($allconst));
	cell->setParam(ID::WIDTH, width);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Allseq(TwineRef name, int width, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, width);
	Cell *cell = addCell(name, TW($allseq));
	cell->setParam(ID::WIDTH, width);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Initstate(TwineRef name, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE);
	Cell *cell = addCell(name, TW($initstate));
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::SetTag(TwineRef name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, sig_a.size());
	Cell *cell = addCell(name, TW($set_tag));
	cell->parameters[ID::WIDTH] = sig_a.size();
	cell->parameters[ID::TAG] = tag;
	cell->setPort(TW::A, sig_a);
	cell->setPort(TW::SET, sig_s);
	cell->setPort(TW::CLR, sig_c);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::Cell* RTLIL::Module::addSetTag(TwineRef name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, const RTLIL::SigSpec &sig_y, TwineRef src)
{
	Cell *cell = addCell(name, TW($set_tag));
	cell->parameters[ID::WIDTH] = sig_a.size();
	cell->parameters[ID::TAG] = tag;
	cell->setPort(TW::A, sig_a);
	cell->setPort(TW::SET, sig_s);
	cell->setPort(TW::CLR, sig_c);
	cell->setPort(TW::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::SigSpec RTLIL::Module::GetTag(TwineRef name, const std::string &tag, const RTLIL::SigSpec &sig_a, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, sig_a.size());
	Cell *cell = addCell(name, TW($get_tag));
	cell->parameters[ID::WIDTH] = sig_a.size();
	cell->parameters[ID::TAG] = tag;
	cell->setPort(TW::A, sig_a);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::Cell* RTLIL::Module::addOverwriteTag(TwineRef name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, TwineRef src)
{
	RTLIL::Cell *cell = addCell(name, TW($overwrite_tag));
	cell->parameters[ID::WIDTH] = sig_a.size();
	cell->parameters[ID::TAG] = tag;
	cell->setPort(TW::A, sig_a);
	cell->setPort(TW::SET, sig_s);
	cell->setPort(TW::CLR, sig_c);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::SigSpec RTLIL::Module::OriginalTag(TwineRef name, const std::string &tag, const RTLIL::SigSpec &sig_a, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, sig_a.size());
	Cell *cell = addCell(name, TW($original_tag));
	cell->parameters[ID::WIDTH] = sig_a.size();
	cell->parameters[ID::TAG] = tag;
	cell->setPort(TW::A, sig_a);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::FutureFF(TwineRef name, const RTLIL::SigSpec &sig_e, TwineRef src)
{
	RTLIL::SigSpec sig = addWire(NEW_TWINE, sig_e.size());
	Cell *cell = addCell(name, TW($future_ff));
	cell->parameters[ID::WIDTH] = sig_e.size();
	cell->setPort(TW::A, sig_e);
	cell->setPort(TW::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Anyconst(Twine &&name, int width, TwineRef src)   { return Anyconst(design->twines.add(std::move(name)), width, src); }
RTLIL::SigSpec RTLIL::Module::Anyseq(Twine &&name, int width, TwineRef src)     { return Anyseq(design->twines.add(std::move(name)), width, src); }
RTLIL::SigSpec RTLIL::Module::Allconst(Twine &&name, int width, TwineRef src)   { return Allconst(design->twines.add(std::move(name)), width, src); }
RTLIL::SigSpec RTLIL::Module::Allseq(Twine &&name, int width, TwineRef src)     { return Allseq(design->twines.add(std::move(name)), width, src); }
RTLIL::SigSpec RTLIL::Module::Initstate(Twine &&name, TwineRef src)             { return Initstate(design->twines.add(std::move(name)), src); }

RTLIL::SigSpec RTLIL::Module::SetTag(Twine &&name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, TwineRef src)
	{ return SetTag(design->twines.add(std::move(name)), tag, sig_a, sig_s, sig_c, src); }
RTLIL::Cell* RTLIL::Module::addSetTag(Twine &&name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, const RTLIL::SigSpec &sig_y, TwineRef src)
	{ return addSetTag(design->twines.add(std::move(name)), tag, sig_a, sig_s, sig_c, sig_y, src); }
RTLIL::SigSpec RTLIL::Module::GetTag(Twine &&name, const std::string &tag, const RTLIL::SigSpec &sig_a, TwineRef src)
	{ return GetTag(design->twines.add(std::move(name)), tag, sig_a, src); }
RTLIL::Cell* RTLIL::Module::addOverwriteTag(Twine &&name, const std::string &tag, const RTLIL::SigSpec &sig_a, const RTLIL::SigSpec &sig_s, const RTLIL::SigSpec &sig_c, TwineRef src)
	{ return addOverwriteTag(design->twines.add(std::move(name)), tag, sig_a, sig_s, sig_c, src); }
RTLIL::SigSpec RTLIL::Module::OriginalTag(Twine &&name, const std::string &tag, const RTLIL::SigSpec &sig_a, TwineRef src)
	{ return OriginalTag(design->twines.add(std::move(name)), tag, sig_a, src); }
RTLIL::SigSpec RTLIL::Module::FutureFF(Twine &&name, const RTLIL::SigSpec &sig_e, TwineRef src)
	{ return FutureFF(design->twines.add(std::move(name)), sig_e, src); }

std::string RTLIL::Module::to_rtlil_str() const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_module(f, "", const_cast<RTLIL::Module*>(this), design, false);
	return f.str();
}

RTLIL::Wire::Wire(ConstructToken)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	module = nullptr;
	width = 1;
	start_offset = 0;
	port_id = 0;
	port_input = false;
	port_output = false;
	upto = false;
	is_signed = false;

#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Wire::get_all_wires()->insert(std::pair<unsigned int, RTLIL::Wire*>(hashidx_, this));
#endif
}

RTLIL::Wire::~Wire()
{
	// if (module && module->design) {
	// 	module->design->obj_release_src(this);
	// 	module->design->obj_release_name(this);
	// }
#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Wire::get_all_wires()->erase(hashidx_);
#endif
}

TwineRef RTLIL::Wire::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}

void RTLIL::Wire::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "Wire::set_src_id requires the wire to be attached to a module in a design");
	module->design->obj_set_src_id(this, id);
}

void RTLIL::Wire::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "Wire::set_src_attribute requires the wire to be attached to a module in a design");
	module->design->set_src_attribute(this, src);
}

std::string RTLIL::Wire::get_src_attribute() const
{
	log_assert(module);
	log_assert(module->design);
	return module->design->get_src_attribute(this);
}

void RTLIL::Wire::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "Wire::adopt_src_from requires the wire to be attached to a module in a design");
	module->design->adopt_src_from(this, source);
}

void RTLIL::Wire::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "Wire::absorb_attrs requires the wire to be attached to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

std::string RTLIL::Wire::to_rtlil_str() const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_wire(f, "", this);
	return f.str();
}

#ifdef YOSYS_ENABLE_PYTHON
static std::map<unsigned int, RTLIL::Wire*> all_wires;
std::map<unsigned int, RTLIL::Wire*> *RTLIL::Wire::get_all_wires(void)
{
	return &all_wires;
}
#endif

RTLIL::Memory::Memory()
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	width = 1;
	start_offset = 0;
	size = 0;
#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Memory::get_all_memorys()->insert(std::pair<unsigned int, RTLIL::Memory*>(hashidx_, this));
#endif
}

std::string RTLIL::Memory::to_rtlil_str() const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_memory(f, "", this);
	return f.str();
}

RTLIL::Process::Process() : module(nullptr)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;
}

std::string RTLIL::Process::to_rtlil_str() const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_proc(f, "", this);
	return f.str();
}

RTLIL::Cell::Cell(ConstructToken) : module(nullptr), type_impl(Twine::Null)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	// log("#memtrace# %p\n", this);
	memhasher();

#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Cell::get_all_cells()->insert(std::pair<unsigned int, RTLIL::Cell*>(hashidx_, this));
#endif
}

RTLIL::Cell::~Cell()
{
	// if (module && module->design) {
	// 	module->design->obj_release_src(this);
	// 	module->design->obj_release_name(this);
	// }
#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Cell::get_all_cells()->erase(hashidx_);
#endif
}

TwineRef RTLIL::Cell::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}

void RTLIL::Cell::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "Cell::set_src_id requires the cell to be attached to a module in a design");
	module->design->obj_set_src_id(this, id);
}

void RTLIL::Cell::set_src_attribute(TwineRef src)
{
	log_assert(module && module->design && "Cell::set_src_attribute requires the cell to be attached to a module in a design");
	module->design->set_src_attribute(this, src);
}

std::string RTLIL::Cell::get_src_attribute() const
{
	log_assert(module);
	log_assert(module->design);
	return module->design->get_src_attribute(this);
}

void RTLIL::Cell::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "Cell::adopt_src_from requires the cell to be attached to a module in a design");
	module->design->adopt_src_from(this, source);
}

void RTLIL::Cell::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "Cell::absorb_attrs requires the cell to be attached to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

std::string RTLIL::Cell::to_rtlil_str() const
{
	std::ostringstream f;
	RTLIL_BACKEND::dump_cell(f, "", this);
	return f.str();
}

#ifdef YOSYS_ENABLE_PYTHON
static std::map<unsigned int, RTLIL::Cell*> all_cells;
std::map<unsigned int, RTLIL::Cell*> *RTLIL::Cell::get_all_cells(void)
{
	return &all_cells;
}
#endif

bool RTLIL::Cell::hasPort(TwineRef portname) const
{
	return connections_.count(portname) != 0;
}

// bufnorm

const RTLIL::SigSpec &RTLIL::Cell::getPort(TwineRef portname) const
{
	return connections_.at(portname);
}

const dict<TwineRef, RTLIL::SigSpec> &RTLIL::Cell::connections() const
{
	return connections_;
}

bool RTLIL::Cell::known() const
{
	if (yosys_celltypes.cell_known(type_impl))
		return true;
	if (module && module->design && module->design->module(type_impl))
		return true;
	return false;
}

bool RTLIL::Cell::input(TwineRef portname) const
{
	if (yosys_celltypes.cell_known(type_impl))
		return yosys_celltypes.cell_input(type_impl, portname);
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type_impl);
		RTLIL::Wire *w = m ? m->wire(portname) : nullptr;
		return w && w->port_input;
	}
	return false;
}

bool RTLIL::Cell::output(TwineRef portname) const
{
	if (yosys_celltypes.cell_known(type_impl))
		return yosys_celltypes.cell_output(type_impl, portname);
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type_impl);
		RTLIL::Wire *w = m ? m->wire(portname) : nullptr;
		return w && w->port_output;
	}
	return false;
}

RTLIL::PortDir RTLIL::Cell::port_dir(TwineRef portname) const
{
	if (yosys_celltypes.cell_known(type_impl))
		return yosys_celltypes.cell_port_dir(type_impl, portname);
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type_impl);
		if (m == nullptr)
			return PortDir::PD_UNKNOWN;
		RTLIL::Wire *w = m->wire(portname);
		if (w == nullptr)
			return PortDir::PD_UNKNOWN;
		return PortDir(w->port_input + w->port_output * 2);
	}
	return PortDir::PD_UNKNOWN;
}

bool RTLIL::Cell::hasParam(IdString paramname) const
{
	return parameters.count(paramname) != 0;
}

void RTLIL::Cell::unsetParam(IdString paramname)
{
	parameters.erase(paramname);
}

void RTLIL::Cell::setParam(IdString paramname, RTLIL::Const value)
{
	parameters[paramname] = std::move(value);
}

const RTLIL::Const &RTLIL::Cell::getParam(IdString paramname) const
{
	const auto &it = parameters.find(paramname);
	if (it != parameters.end())
		return it->second;
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type_impl);
		if (m)
			return m->parameter_default_values.at(paramname);
	}
	throw std::out_of_range("Cell::getParam()");
}

void RTLIL::Cell::sort()
{
	connections_.sort();
	parameters.sort(sort_by_id_str());
	attributes.sort(sort_by_id_str());
}

void RTLIL::Cell::check()
{
#ifndef NDEBUG
	InternalCellChecker checker(NULL, this);
	checker.check();
#endif
}

void RTLIL::Cell::fixup_parameters(bool set_a_signed, bool set_b_signed)
{
	std::string type_str = type.str();
	std::string_view type_sv = type_str;
	if (!type_sv.starts_with("$") || type_sv.starts_with("$_") || type_sv.starts_with("$paramod") || type_sv.starts_with("$fmcombine") ||
			type_sv.starts_with("$verific$") || type_sv.starts_with("$array:") || type_sv.starts_with("$extern:"))
		return;

	if (type == TW($buf) || type == TW($mux) || type == TW($pmux) || type == TW($bmux) || type == TW($bwmux) || type == TW($bweqx)) {
		parameters[ID::WIDTH] = GetSize(connections_[TW::Y]);
		if (type_impl.in(TW($pmux), TW($bmux)))
			parameters[ID::S_WIDTH] = GetSize(connections_[TW::S]);
		check();
		return;
	}

	if (type == TW($demux)) {
		parameters[ID::WIDTH] = GetSize(connections_[TW::A]);
		parameters[ID::S_WIDTH] = GetSize(connections_[TW::S]);
		check();
		return;
	}

	if (type == TW($lut) || type == TW($sop)) {
		parameters[ID::WIDTH] = GetSize(connections_[TW::A]);
		return;
	}

	if (type == TW($fa)) {
		parameters[ID::WIDTH] = GetSize(connections_[TW::Y]);
		return;
	}

	if (type == TW($lcu)) {
		parameters[ID::WIDTH] = GetSize(connections_[TW::CO]);
		return;
	}

	if (type == TW($macc_v2)) {
		parameters[ID::Y_WIDTH] = GetSize(connections_[TW::Y]);
		return;
	}

	bool signedness_ab = !type_impl.in(TW($slice), TW($concat), TW($macc));

	if (connections_.count(TW::A)) {
		if (signedness_ab) {
			if (set_a_signed)
				parameters[ID::A_SIGNED] = true;
			else if (parameters.count(ID::A_SIGNED) == 0)
				parameters[ID::A_SIGNED] = false;
		}
		parameters[ID::A_WIDTH] = GetSize(connections_[TW::A]);
	}

	if (connections_.count(TW::B)) {
		if (signedness_ab) {
			if (set_b_signed)
				parameters[ID::B_SIGNED] = true;
			else if (parameters.count(ID::B_SIGNED) == 0)
				parameters[ID::B_SIGNED] = false;
		}
		parameters[ID::B_WIDTH] = GetSize(connections_[TW::B]);
	}

	if (connections_.count(TW::Y) && type != TW($concat))
		parameters[ID::Y_WIDTH] = GetSize(connections_[TW::Y]);

	if (connections_.count(TW::Q))
		parameters[ID::WIDTH] = GetSize(connections_[TW::Q]);

	check();
}

bool RTLIL::Cell::has_keep_attr() const {
	return get_bool_attribute(ID::keep) || (module && module->design && module->design->module(type_impl) &&
			module->design->module(type_impl)->get_bool_attribute(ID::keep));
}

bool RTLIL::Cell::has_memid() const
{
	return type_impl.in(TW($memwr), TW($memwr_v2), TW($memrd), TW($memrd_v2), TW($meminit), TW($meminit_v2));
}

bool RTLIL::Cell::is_mem_cell() const
{
	return type_impl.in(TW($mem), TW($mem_v2)) || has_memid();
}

bool RTLIL::Cell::is_builtin_ff() const {
	return StaticCellTypes::categories.is_ff(type_impl);
}

RTLIL::SigChunk::SigChunk(const RTLIL::SigBit &bit)
{
	wire = bit.wire;
	offset = 0;
	if (wire == NULL)
		data = {bit.data};
	else
		offset = bit.offset;
	width = 1;
}

RTLIL::SigChunk RTLIL::SigChunk::extract(int offset, int length) const
{
	log_assert(offset >= 0);
	log_assert(length >= 0);
	log_assert(offset + length <= width);
	RTLIL::SigChunk ret;
	if (wire) {
		ret.wire = wire;
		ret.offset = this->offset + offset;
		ret.width = length;
	} else {
		for (int i = 0; i < length; i++)
			ret.data.push_back(data[offset+i]);
		ret.width = length;
	}
	return ret;
}

RTLIL::SigBit RTLIL::SigChunk::operator[](int offset) const
{
	log_assert(offset >= 0);
	log_assert(offset < width);
	RTLIL::SigBit ret;
	if (wire) {
		ret.wire = wire;
		ret.offset = this->offset + offset;
	} else {
		ret.data = data[offset];
	}
	return ret;
}

bool RTLIL::SigChunk::operator <(const RTLIL::SigChunk &other) const
{
	if (wire && other.wire)
		if (wire->name != other.wire->name)
			return wire->name < other.wire->name;

	if (wire != other.wire)
		return wire < other.wire;

	if (offset != other.offset)
		return offset < other.offset;

	if (width != other.width)
		return width < other.width;

	return data < other.data;
}

bool RTLIL::SigChunk::operator ==(const RTLIL::SigChunk &other) const
{
	return wire == other.wire && width == other.width && offset == other.offset && data == other.data;
}

bool RTLIL::SigChunk::operator !=(const RTLIL::SigChunk &other) const
{
	if (*this == other)
		return false;
	return true;
}

RTLIL::SigSpec::SigSpec(std::initializer_list<RTLIL::SigSpec> parts)
{
	init_empty_bits();
	log_assert(parts.size() > 0);
	auto ie = parts.begin();
	auto it = ie + parts.size() - 1;
	while (it >= ie)
		append(*it--);
}

RTLIL::SigSpec::SigSpec(const RTLIL::Const &value)
{
	if (GetSize(value) != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(value);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Const &&value)
{
	if (GetSize(value) != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(value);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(const RTLIL::SigChunk &chunk)
{
	if (chunk.width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(chunk);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::SigChunk &&chunk)
{
	if (chunk.width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(chunk);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Wire *wire)
{
	if (wire->width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(wire);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Wire *wire, int offset, int width)
{
	if (width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(wire, offset, width);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(const std::string &str)
{
	if (str.size() != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(str);
	} else {
		init_empty_bits();
	}
	check();
}

RTLIL::SigSpec::SigSpec(int val, int width)
{
	if (width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(val, width);
	} else
		init_empty_bits();
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::State bit, int width)
{
	if (width != 0) {
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(bit, width);
	} else
		init_empty_bits();
	check();
}

RTLIL::SigSpec::SigSpec(const RTLIL::SigBit &bit, int width)
{
	if (width != 0) {
		if (bit.wire == NULL) {
			rep_ = CHUNK;
			new (&chunk_) RTLIL::SigChunk(bit.data, width);
		} else if (width == 1) {
			rep_ = CHUNK;
			new (&chunk_) RTLIL::SigChunk(bit);
		} else {
			init_empty_bits();
			bits_.reserve(width);
			for (int i = 0; i < width; i++)
				bits_.push_back(bit);
		}
	} else
		init_empty_bits();
	check();
}

RTLIL::SigSpec::SigSpec(const std::vector<RTLIL::SigChunk> &chunks)
{
	init_empty_bits();
	for (const auto &c : chunks)
		append(c);
	check();
}

RTLIL::SigSpec::SigSpec(const std::vector<RTLIL::SigBit> &bits)
{
	init_empty_bits();
	for (const auto &bit : bits)
		append(bit);
	check();
}

RTLIL::SigSpec::SigSpec(const pool<RTLIL::SigBit> &bits)
{
	init_empty_bits();
	for (const auto &bit : bits)
		append(bit);
	check();
}

RTLIL::SigSpec::SigSpec(const std::set<RTLIL::SigBit> &bits)
{
	init_empty_bits();
	for (const auto &bit : bits)
		append(bit);
	check();
}

RTLIL::SigSpec::SigSpec(bool bit)
{
	rep_ = CHUNK;
	new (&chunk_) RTLIL::SigChunk(bit ? RTLIL::S1 : RTLIL::S0);
	check();
}

void RTLIL::SigSpec::Chunks::const_iterator::next_chunk_bits()
{
	int bits_size = GetSize(spec.bits_);
	if (bit_index >= bits_size)
		return;
	int i = bit_index;
	const SigBit &bit = spec.bits_[i++];
	chunk.wire = bit.wire;
	chunk.data.clear();
	if (bit.is_wire()) {
		chunk.offset = bit.offset;
		while (i < bits_size && spec.bits_[i].wire == bit.wire &&
			spec.bits_[i].offset == bit.offset + i - bit_index)
			++i;
	} else {
		chunk.offset = 0;
		chunk.data.push_back(bit.data);
		while (i < bits_size && !spec.bits_[i].is_wire()) {
			chunk.data.push_back(spec.bits_[i].data);
			++i;
		}
	}
	chunk.width = i - bit_index;
}

void RTLIL::SigSpec::unpack()
{
	if (rep_ == BITS)
		return;

	std::vector<RTLIL::SigBit> bits;
	bits.reserve(chunk_.width);
	for (int i = 0; i < chunk_.width; i++)
		bits.emplace_back(chunk_, i);

	chunk_.~SigChunk();
	rep_ = BITS;
	new (&bits_) std::vector<RTLIL::SigBit>(std::move(bits));
}

void RTLIL::SigSpec::try_repack()
{
	if (rep_ != BITS)
		return;

	int bits_size = GetSize(bits_);
	if (bits_size == 0)
		return;
	if (bits_[0].is_wire()) {
		for (int i = 1; i < bits_size; i++)
			if (bits_[0].wire != bits_[i].wire || bits_[0].offset + i != bits_[i].offset)
				return;
		SigChunk chunk(bits_[0].wire, bits_[0].offset, bits_size);
		bits_.~vector();
		rep_ = CHUNK;
		new (&chunk_) SigChunk(std::move(chunk));
		return;
	}
	std::vector<RTLIL::State> bits;
	bits.reserve(bits_size);
	bits.push_back(bits_[0].data);
	for (int i = 1; i < bits_size; i++) {
		if (bits_[i].is_wire())
			return;
		bits.push_back(bits_[i].data);
	}
	bits_.~vector();
	rep_ = CHUNK;
	new (&chunk_) SigChunk(std::move(bits));
}

Hasher::hash_t RTLIL::SigSpec::updhash() const
{
	Hasher h;
	for (auto &c : chunks())
		if (c.wire == NULL) {
			for (auto &v : c.data)
				h.eat(v);
		} else {
			h.eat(c.wire->meta_ ? c.wire->meta_->name : Twine::Null);
			h.eat(c.offset);
			h.eat(c.width);
		}
	Hasher::hash_t result = h.yield();
	if (result == 0)
		result = 1;
	hash_.set(result);
	return result;
}

void RTLIL::SigSpec::sort()
{
	unpack();
	std::sort(bits_.begin(), bits_.end());
	hash_.clear();
	try_repack();
}

void RTLIL::SigSpec::sort_and_unify()
{
	unpack();
	// A copy of the bits vector is used to prevent duplicating the logic from
	// SigSpec::SigSpec(std::vector<SigBit>).  This incurrs an extra copy but
	// that isn't showing up as significant in profiles.
	std::vector<SigBit> unique_bits = bits_;
	std::sort(unique_bits.begin(), unique_bits.end());
	auto last = std::unique(unique_bits.begin(), unique_bits.end());
	unique_bits.erase(last, unique_bits.end());

	*this = unique_bits;
	hash_.clear();
	try_repack();
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with)
{
	replace(pattern, with, this);
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const
{
	log_assert(other != NULL);
	log_assert(size() == other->size());
	log_assert(pattern.size() == with.size());

	dict<RTLIL::SigBit, int> pattern_to_with;
	int pattern_size = pattern.size();
	for (int i = 0; i < pattern_size; i++) {
		SigBit pattern_bit = pattern[i];
		if (pattern_bit.wire != NULL) {
			pattern_to_with.emplace(pattern_bit, i);
		}
	}

	int this_size = size();
	bool other_modified = false;
	for (int j = 0; j < this_size; j++) {
		auto it = pattern_to_with.find((*this)[j]);
		if (it != pattern_to_with.end()) {
			other_modified = true;
			(*other)[j] = with[it->second];
		}
	}

	if (other_modified)
		other->try_repack();
	other->check();
}

void RTLIL::SigSpec::replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules)
{
	replace(rules, this);
}

void RTLIL::SigSpec::replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const
{
	log_assert(other != NULL);
	log_assert(size() == other->size());

	if (rules.empty()) return;

	int this_size = size();
	bool other_modified = false;
	for (int i = 0; i < this_size; i++) {
		auto it = rules.find((*this)[i]);
		if (it != rules.end()) {
			other_modified = true;
			(*other)[i] = it->second;
		}
	}

	if (other_modified)
		other->try_repack();
	other->check();
}

void RTLIL::SigSpec::replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules)
{
	replace(rules, this);
}

void RTLIL::SigSpec::replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const
{
	log_assert(other != NULL);
	log_assert(size() == other->size());

	if (rules.empty()) return;

	int this_size = size();
	bool other_modified = false;
	for (int i = 0; i < this_size; i++) {
		auto it = rules.find((*this)[i]);
		if (it != rules.end()) {
			other_modified = true;
			(*other)[i] = it->second;
		}
	}

	if (other_modified)
		other->try_repack();
	other->check();
}

void RTLIL::SigSpec::remove(const RTLIL::SigSpec &pattern)
{
	remove2(pattern, NULL);
}

void RTLIL::SigSpec::remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const
{
	RTLIL::SigSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void RTLIL::SigSpec::remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other)
{
	unpack();
	if (other != NULL) {
		log_assert(size() == other->size());
		other->unpack();
	}

	//  Convert pattern to pool for O(1) lookup, avoiding O(n*m) chunk iteration
	pool<SigBit> pattern_bits;
	pattern_bits.reserve(pattern.size());
	for (auto &bit : pattern)
		if (bit.wire != NULL)
			pattern_bits.insert(bit);

	// Compact in-place to avoid O(n^2) erase operations
	size_t write_idx = 0;
	for (size_t read_idx = 0; read_idx < bits_.size(); read_idx++)
	{
		if (!(bits_[read_idx].wire != NULL && pattern_bits.count(bits_[read_idx]))) {
			if (write_idx != read_idx) {
				bits_[write_idx] = bits_[read_idx];
				if (other != NULL)
					other->bits_[write_idx] = other->bits_[read_idx];
			}
			write_idx++;
		}
	}

	bool modified = (write_idx < bits_.size());
	if (modified) {
		bits_.resize(write_idx);
		hash_.clear();
		try_repack();
	}
	if (other != NULL && modified) {
		other->bits_.resize(write_idx);
		other->hash_.clear();
		other->try_repack();
	}
	check();
}

void RTLIL::SigSpec::remove(const pool<RTLIL::SigBit> &pattern)
{
	remove2(pattern, NULL);
}

void RTLIL::SigSpec::remove(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other) const
{
	RTLIL::SigSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void RTLIL::SigSpec::remove2(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other)
{
	unpack();

	if (other != NULL) {
		log_assert(size() == other->size());
		other->unpack();
	}

	// Avoid O(n^2) complexity by compacting in-place
	size_t write_idx = 0;
	for (size_t read_idx = 0; read_idx < bits_.size(); read_idx++) {
		if (!(bits_[read_idx].wire != NULL && pattern.count(bits_[read_idx]))) {
			if (write_idx != read_idx) {
				bits_[write_idx] = bits_[read_idx];
				if (other != NULL)
					other->bits_[write_idx] = other->bits_[read_idx];
			}
			write_idx++;
		}
	}

	bool modified = (write_idx < bits_.size());
	if (modified) {
		bits_.resize(write_idx);
		hash_.clear();
		try_repack();
	}
	if (other != NULL && modified) {
		other->bits_.resize(write_idx);
		other->hash_.clear();
		other->try_repack();
	}
	check();
}

void RTLIL::SigSpec::remove2(const std::set<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other)
{
	unpack();

	if (other != NULL) {
		log_assert(size() == other->size());
		other->unpack();
	}

	// Avoid O(n^2) complexity by compacting in-place
	size_t write_idx = 0;
	for (size_t read_idx = 0; read_idx < bits_.size(); read_idx++) {
		if (!(bits_[read_idx].wire != NULL && pattern.count(bits_[read_idx]))) {
			if (write_idx != read_idx) {
				bits_[write_idx] = bits_[read_idx];
				if (other != NULL)
					other->bits_[write_idx] = other->bits_[read_idx];
			}
			write_idx++;
		}
	}

	bool modified = (write_idx < bits_.size());
	if (modified) {
		bits_.resize(write_idx);
		hash_.clear();
		try_repack();
	}
	if (other != NULL && modified) {
		other->bits_.resize(write_idx);
		other->hash_.clear();
		other->try_repack();
	}
	check();
}

void RTLIL::SigSpec::remove2(const pool<RTLIL::Wire*> &pattern, RTLIL::SigSpec *other)
{
	unpack();

	if (other != NULL) {
		log_assert(size() == other->size());
		other->unpack();
	}

	bool modified = false;
	bool other_modified = false;
	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].wire != NULL && pattern.count(bits_[i].wire)) {
			modified = true;
			bits_.erase(bits_.begin() + i);
			if (other != NULL) {
				other_modified = true;
				other->bits_.erase(other->bits_.begin() + i);
			}
		}
	}

	if (modified) {
		hash_.clear();
		try_repack();
	}
	if (other_modified) {
		other->hash_.clear();
		other->try_repack();
	}
	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other) const
{
	log_assert(other == NULL || size() == other->size());

	RTLIL::SigSpec ret;
	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();

	for (auto& pattern_chunk : pattern.chunks()) {
		if (other) {
			std::vector<RTLIL::SigBit> bits_other = other->to_sigbit_vector();
			int i = 0;
			for (const RTLIL::SigBit &bit : bits_match) {
				if (bit.wire &&
					bit.wire == pattern_chunk.wire &&
					bit.offset >= pattern_chunk.offset &&
					bit.offset < pattern_chunk.offset + pattern_chunk.width)
					ret.append(bits_other[i]);
				++i;
			}
		} else {
			for (const RTLIL::SigBit &bit : bits_match)
				if (bit.wire &&
					bit.wire == pattern_chunk.wire &&
					bit.offset >= pattern_chunk.offset &&
					bit.offset < pattern_chunk.offset + pattern_chunk.width)
					ret.append(bit);
		}
	}

	ret.check();
	return ret;
}

RTLIL::SigSpec RTLIL::SigSpec::extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other) const
{
	log_assert(other == NULL || size() == other->size());

	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();
	RTLIL::SigSpec ret;

	if (other) {
		std::vector<RTLIL::SigBit> bits_other = other->to_sigbit_vector();
		int i = 0;
		for (const RTLIL::SigBit &bit : bits_match) {
			if (bit.wire && pattern.count(bit))
				ret.append(bits_other[i]);
			++i;
		}
	} else {
		for (const RTLIL::SigBit &bit : bits_match)
			if (bit.wire && pattern.count(bit))
				ret.append(bit);
	}

	ret.check();
	return ret;
}

void RTLIL::SigSpec::replace(int offset, const RTLIL::SigSpec &with)
{
	if (with.size() == 0)
		return;

	unpack();

	log_assert(offset >= 0);
	log_assert(with.size() >= 0);
	log_assert(offset+with.size() <= size());

	int i = 0;
	for (const RTLIL::SigBit &bit : with.bits()) {
		bits_.at(offset + i) = bit;
		++i;
	}
	hash_.clear();
	try_repack();

	check();
}

void RTLIL::SigSpec::remove_const()
{
	if (rep_ == CHUNK)
	{
		if (chunk_.wire == NULL) {
			chunk_.~SigChunk();
			init_empty_bits();
			hash_.clear();
		}
	}
	else
	{
		std::vector<RTLIL::SigBit> new_bits;
		new_bits.reserve(bits_.size());
		for (auto &bit : bits_)
			if (bit.wire != NULL)
				new_bits.push_back(bit);
		if (GetSize(new_bits) != GetSize(bits_)) {
			bits_.swap(new_bits);
			hash_.clear();
			try_repack();
		}
	}

	check();
}

void RTLIL::SigSpec::remove(int offset, int length)
{
	if (length == 0)
		return;

	unpack();

	log_assert(offset >= 0);
	log_assert(length >= 0);
	log_assert(offset + length <= size());

	bits_.erase(bits_.begin() + offset, bits_.begin() + offset + length);

	hash_.clear();
	try_repack();
	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(int offset, int length) const
{
	log_assert(offset >= 0);
	log_assert(length >= 0);
	log_assert(offset + length <= size());

	std::vector<SigBit> extracted;
	SigBit first;
	bool is_packing = true;
	for (int i = offset; i < offset + length; i++) {
		bool was_packing_before = is_packing;
		SigBit bit = (*this)[i];
		if (i == offset) {
			first = bit;
			if (!bit.wire)
				is_packing = false;
		} else {
			if (bit.wire != first.wire)
				is_packing = false;
			if (bit.wire)
				if (bit.offset != first.offset + (i - offset))
					is_packing = false;
		}
		if (was_packing_before && !is_packing)
			for (int j = offset; j < i; j++)
				extracted.push_back((*this)[j]);
		if (!is_packing)
			extracted.push_back((*this)[i]);
	}
	if (is_packing)
		return SigChunk(first.wire, first.offset, length);

	return extracted;
}

void RTLIL::SigSpec::rewrite_wires(std::function<void(RTLIL::Wire*& wire)> rewrite)
{
	if (rep_ == CHUNK) {
		if (chunk_.wire != nullptr)
			rewrite(chunk_.wire);
		return;
	}

	std::vector<RTLIL::SigBit> new_bits;
	for (const RTLIL::SigChunk &chunk : chunks()) {
		RTLIL::SigChunk c = chunk;
		if (c.wire != nullptr)
			rewrite(c.wire);
		for (int i = 0; i < c.width; i++)
			new_bits.emplace_back(c, i);
	}
	bits_ = std::move(new_bits);
	hash_.clear();
}

void RTLIL::SigSpec::append(const RTLIL::SigSpec &signal)
{
	if (signal.size() == 0)
		return;

	if (size() == 0) {
		*this = signal;
		return;
	}

	hash_.clear();
	if (rep_ == CHUNK && signal.rep_ == CHUNK && chunk_.wire == signal.chunk_.wire) {
		if (chunk_.wire == NULL) {
			chunk_.data.insert(chunk_.data.end(), signal.chunk_.data.begin(), signal.chunk_.data.end());
			chunk_.width = GetSize(chunk_.data);
			return;
		}
		if (chunk_.offset + chunk_.width == signal.chunk_.offset) {
			chunk_.width += signal.chunk_.width;
			return;
		}
	}

	unpack();
	for (const SigBit &bit : signal.bits())
		bits_.push_back(bit);
	check();
}

void RTLIL::SigSpec::append(const RTLIL::SigBit &bit)
{
	hash_.clear();

	if (size() == 0) {
		destroy();
		rep_ = CHUNK;
		new (&chunk_) RTLIL::SigChunk(bit);
		return;
	}

	if (rep_ == CHUNK && chunk_.wire == bit.wire) {
		if (chunk_.wire == NULL) {
			chunk_.data.push_back(bit.data);
			chunk_.width++;
			return;
		}
		if (chunk_.offset + chunk_.width == bit.offset) {
			chunk_.width++;
			return;
		}
	}

	unpack();

	bits_.push_back(bit);
	check();
}

void RTLIL::SigSpec::extend_u0(int width, bool is_signed)
{
	if (size() > width)
		remove(width, size() - width);

	if (size() < width) {
		RTLIL::SigBit padding = size() > 0 ? (*this)[size() - 1] : RTLIL::State::Sx;
		if (!is_signed)
			padding = RTLIL::State::S0;
		while (size() < width)
			append(padding);
	}
}

RTLIL::SigSpec RTLIL::SigSpec::repeat(int num) const
{
	RTLIL::SigSpec sig;
	for (int i = 0; i < num; i++)
		sig.append(*this);
	return sig;
}

#ifndef NDEBUG
void RTLIL::SigSpec::check(const Module *mod) const
{
	if (rep_ == CHUNK)
	{
		log_assert(chunk_.width != 0);
		if (chunk_.wire == NULL) {
			log_assert(chunk_.offset == 0);
			log_assert(chunk_.data.size() == (size_t)chunk_.width);
		} else {
			log_assert(chunk_.offset >= 0);
			log_assert(chunk_.width >= 0);
			log_assert(chunk_.offset + chunk_.width <= chunk_.wire->width);
			log_assert(chunk_.data.size() == 0);
			if (mod != nullptr)
				log_assert(chunk_.wire->module == mod);
		}
	}
	else if (size() <= 64)
	{
		if (mod != nullptr) {
			for (const RTLIL::SigBit &bit : bits_)
				if (bit.wire != nullptr)
					log_assert(bit.wire->module == mod);
		}
	}
}
#endif

bool RTLIL::SigSpec::operator <(const RTLIL::SigSpec &other) const
{
	if (this == &other)
		return false;

	if (size() != other.size())
		return size() < other.size();

	auto other_it = other.chunks().begin();
	for (const SigChunk &c : chunks()) {
		if (c != *other_it)
			return c < *other_it;
		++other_it;
	}

	return false;
}

bool RTLIL::SigSpec::operator ==(const RTLIL::SigSpec &other) const
{
	if (this == &other)
		return true;

	if (size() != other.size())
		return false;

	auto other_it = other.chunks().begin();
	for (const SigChunk &c : chunks()) {
		if (c != *other_it)
			return false;
		++other_it;
	}

	return true;
}

bool RTLIL::SigSpec::is_wire() const
{
	Chunks cs = chunks();
	auto it = cs.begin();
	if (it == cs.end())
		return false;
	const RTLIL::SigChunk &chunk = *it;
	return chunk.wire && chunk.wire->width == size() && ++it == cs.end();
}

bool RTLIL::SigSpec::is_chunk() const
{
	Chunks cs = chunks();
	auto it = cs.begin();
	if (it == cs.end())
		return false;
	return ++it == cs.end();
}

bool RTLIL::SigSpec::known_driver() const
{
	for (auto &chunk : chunks())
		if (chunk.is_wire() && !chunk.wire->known_driver())
			return false;
	return true;
}

bool RTLIL::SigSpec::is_fully_const() const
{
	for (auto &chunk : chunks())
		if (chunk.width > 0 && chunk.wire != NULL)
			return false;
	return true;
}

bool RTLIL::SigSpec::is_fully_zero() const
{
	for (auto &chunk : chunks()) {
		if (chunk.width > 0 && chunk.wire != NULL)
			return false;
		for (RTLIL::State d : chunk.data)
			if (d != RTLIL::State::S0)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_ones() const
{
	for (auto &chunk : chunks()) {
		if (chunk.width > 0 && chunk.wire != NULL)
			return false;
		for (RTLIL::State d : chunk.data)
			if (d != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_def() const
{
	for (auto &chunk : chunks()) {
		if (chunk.width > 0 && chunk.wire != NULL)
			return false;
		for (RTLIL::State d : chunk.data)
			if (d != RTLIL::State::S0 && d != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_undef() const
{
	for (auto &chunk : chunks()) {
		if (chunk.width > 0 && chunk.wire != NULL)
			return false;
		for (RTLIL::State d : chunk.data)
			if (d != RTLIL::State::Sx && d != RTLIL::State::Sz)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::has_const() const
{
	for (auto &chunk : chunks())
		if (chunk.width > 0 && chunk.wire == NULL)
			return true;
	return false;
}

bool RTLIL::SigSpec::has_const(State state) const
{
	for (auto &chunk : chunks())
		if (chunk.width > 0 && chunk.wire == NULL && std::find(chunk.data.begin(), chunk.data.end(), state) != chunk.data.end())
			return true;
	return false;
}


bool RTLIL::SigSpec::has_marked_bits() const
{
	for (auto &chunk : chunks())
		if (chunk.width > 0 && chunk.wire == NULL) {
			for (RTLIL::State d : chunk.data)
				if (d == RTLIL::State::Sm)
					return true;
		}
	return false;
}

bool RTLIL::SigSpec::is_onehot(int *pos) const
{
	if (std::optional<RTLIL::Const> c = try_as_const())
		return c->is_onehot(pos);
	return false;
}

bool RTLIL::SigSpec::as_bool() const
{
	std::optional<RTLIL::Const> c = try_as_const();
	log_assert(c.has_value());
	return c->as_bool();
}

int RTLIL::SigSpec::as_int(bool is_signed) const
{
	std::optional<RTLIL::Const> c = try_as_const();
	log_assert(c.has_value());
	return c->as_int(is_signed);
}

bool RTLIL::SigSpec::convertible_to_int(bool is_signed) const
{
	std::optional<RTLIL::Const> c = try_as_const();
	if (!c.has_value())
		return false;
	return c->convertible_to_int(is_signed);
}

std::optional<int> RTLIL::SigSpec::try_as_int(bool is_signed) const
{
	std::optional<RTLIL::Const> c = try_as_const();
	if (!c.has_value())
		return std::nullopt;
	return c->try_as_int(is_signed);
}

int RTLIL::SigSpec::as_int_saturating(bool is_signed) const
{
	std::optional<RTLIL::Const> c = try_as_const();
	log_assert(c.has_value());
	return c->as_int_saturating(is_signed);
}

std::string RTLIL::SigSpec::as_string() const
{
	std::string str;
	str.reserve(size());
	std::vector<RTLIL::SigChunk> chunks = *this;
	for (size_t i = chunks.size(); i > 0; i--) {
		const RTLIL::SigChunk &chunk = chunks[i-1];
		if (chunk.wire != NULL)
			str.append(chunk.width, '?');
		else
			str += RTLIL::Const(chunk.data).as_string();
	}
	return str;
}

std::optional<RTLIL::Const> RTLIL::SigSpec::try_as_const() const
{
	Chunks cs = chunks();
	auto it = cs.begin();
	if (it == cs.end())
		return RTLIL::Const();
	SigChunk chunk = *it;
	if (chunk.wire != NULL || ++it != cs.end())
		return std::nullopt;
	return RTLIL::Const(std::move(chunk.data));
}

RTLIL::Const RTLIL::SigSpec::as_const() const
{
	std::optional<RTLIL::Const> c = try_as_const();
	log_assert(c.has_value());
	return *c;
}

RTLIL::Wire *RTLIL::SigSpec::as_wire() const
{
	Chunks cs = chunks();
	auto it = cs.begin();
	log_assert(it != cs.end());
	RTLIL::SigChunk chunk = *it;
	log_assert(++it == cs.end() && chunk.wire && chunk.wire->width == size());
	return chunk.wire;
}

RTLIL::SigChunk RTLIL::SigSpec::as_chunk() const
{
	Chunks cs = chunks();
	auto it = cs.begin();
	log_assert(it != cs.end());
	RTLIL::SigChunk chunk = *it;
	log_assert(++it == cs.end());
	return chunk;
}

RTLIL::SigBit RTLIL::SigSpec::as_bit() const
{
	return RTLIL::SigBit(*this);
}

bool RTLIL::SigSpec::match(const char* pattern) const
{
	int pattern_len = strlen(pattern);
	log_assert(pattern_len == size());

	for (int i = 0; i < pattern_len; ++i) {
		char ch = pattern[i];
		if (ch == ' ')
			continue;
		RTLIL::SigBit bit = (*this)[pattern_len - 1 - i];
		if (ch == '*') {
			if (bit != State::Sz && bit != State::Sx)
				return false;
			continue;
		}
		if (ch == '0') {
			if (bit != State::S0)
				return false;
		} else
		if (ch == '1') {
			if (bit != State::S1)
				return false;
		} else
			log_abort();
	}

	return true;
}

std::set<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_set() const
{
	std::set<RTLIL::SigBit> sigbits;
	for (auto &c : chunks())
		for (int i = 0; i < c.width; i++)
			sigbits.insert(RTLIL::SigBit(c, i));
	return sigbits;
}

pool<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_pool() const
{
	pool<RTLIL::SigBit> sigbits;
	sigbits.reserve(size());
	for (auto &c : chunks())
		for (int i = 0; i < c.width; i++)
			sigbits.insert(RTLIL::SigBit(c, i));
	return sigbits;
}

std::vector<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_vector() const
{
	std::vector<RTLIL::SigBit> result;
	result.reserve(size());
	for (SigBit bit : *this)
		result.push_back(bit);
	return result;
}

std::map<RTLIL::SigBit, RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_map(const RTLIL::SigSpec &other) const
{
	int this_size = size();
	log_assert(this_size == other.size());

	std::map<RTLIL::SigBit, RTLIL::SigBit> new_map;
	for (int i = 0; i < this_size; i++)
		new_map[(*this)[i]] = other[i];

	return new_map;
}

dict<RTLIL::SigBit, RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_dict(const RTLIL::SigSpec &other) const
{
	int this_size = size();
	log_assert(this_size == other.size());

	dict<RTLIL::SigBit, RTLIL::SigBit> new_map;
	new_map.reserve(this_size);
	for (int i = 0; i < this_size; i++)
		new_map[(*this)[i]] = other[i];

	return new_map;
}

static void sigspec_parse_split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

bool RTLIL::SigSpec::parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	std::vector<std::string> tokens;
	sigspec_parse_split(tokens, str, ',');

	sig = RTLIL::SigSpec();
	std::optional<TwineSearch> search;
	if (module)
		search.emplace(&module->design->twines);
	for (int tokidx = int(tokens.size())-1; tokidx >= 0; tokidx--)
	{
		std::string netname = tokens[tokidx];
		std::string indices;

		if (netname.size() == 0)
			continue;

		if (('0' <= netname[0] && netname[0] <= '9') || netname[0] == '\'') {
			VERILOG_FRONTEND::ConstParser p{Location()};
			auto ast = p.const2ast(netname);
			if (ast == nullptr)
				return false;
			sig.append(RTLIL::Const(ast->bits));
			continue;
		}

		if (module == NULL)
			return false;

		if (netname[0] != '$' && netname[0] != '\\')
			netname = "\\" + netname;

		if (search->find(netname) == Twine::Null) {
			size_t indices_pos = netname.size()-1;
			if (indices_pos > 2 && netname[indices_pos] == ']')
			{
				indices_pos--;
				while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				if (indices_pos > 0 && netname[indices_pos] == ':') {
					indices_pos--;
					while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				}
				if (indices_pos > 0 && netname[indices_pos] == '[') {
					indices = netname.substr(indices_pos);
					netname = netname.substr(0, indices_pos);
				}
			}
		}

		{
			TwineRef wid = search->find(netname);
			if (wid == Twine::Null || module->wires_.count(wid) == 0)
				return false;
		}

		RTLIL::Wire *wire = module->wire(search->find(netname));
		if (!indices.empty()) {
			std::vector<std::string> index_tokens;
			sigspec_parse_split(index_tokens, indices.substr(1, indices.size()-2), ':');
			if (index_tokens.size() == 1) {
				int a = atoi(index_tokens.at(0).c_str());
				if (a < 0 || a >= wire->width)
					return false;
				sig.append(RTLIL::SigSpec(wire, a));
			} else {
				int a = atoi(index_tokens.at(0).c_str());
				int b = atoi(index_tokens.at(1).c_str());
				if (a > b) {
					int tmp = a;
					a = b, b = tmp;
				}
				if (a < 0 || a >= wire->width)
					return false;
				if (b < 0 || b >= wire->width)
					return false;
				sig.append(RTLIL::SigSpec(wire, a, b-a+1));
			}
		} else
			sig.append(wire);
	}

	return true;
}

bool RTLIL::SigSpec::parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str)
{
	if (str.empty() || str[0] != '@')
		return parse(sig, module, str);

	str = RTLIL::escape_id(str.substr(1));
	if (design->selection_vars.count(str) == 0)
		return false;

	sig = RTLIL::SigSpec();
	RTLIL::Selection &sel = design->selection_vars.at(str);
	for (auto &it : module->wires_)
		if (sel.selected_member(module->meta_->name, it.second->meta_->name))
			sig.append(it.second);

	return true;
}

bool RTLIL::SigSpec::parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	if (str == "0") {
		sig = RTLIL::SigSpec(RTLIL::State::S0, lhs.size());
		return true;
	}

	if (str == "~0") {
		sig = RTLIL::SigSpec(RTLIL::State::S1, lhs.size());
		return true;
	}

	if (lhs.is_chunk()) {
		char *p = (char*)str.c_str(), *endptr;
		long int val = strtol(p, &endptr, 10);
		if (endptr && endptr != p && *endptr == 0) {
			sig = RTLIL::SigSpec(val, lhs.size());
			return true;
		}
	}

	if (!parse(sig, module, str))
		return false;
	if (sig.size() > lhs.size())
		sig.remove(lhs.size(), sig.size() - lhs.size());
	return true;
}

RTLIL::SigSpec::operator std::vector<RTLIL::SigChunk>() const
{
	std::vector<RTLIL::SigChunk> result;
	for (const RTLIL::SigChunk &c : chunks())
		result.push_back(c);
	return result;
}

RTLIL::CaseRule::~CaseRule()
{
	for (auto it = switches.begin(); it != switches.end(); it++)
		delete *it;
}

bool RTLIL::CaseRule::empty() const
{
	return actions.empty() && switches.empty();
}

void RTLIL::CaseRule::setModuleRecursive(RTLIL::Module *m)
{
	module = m;
	for (auto *sw : switches)
		sw->setModuleRecursive(m);
}

void RTLIL::SwitchRule::setModuleRecursive(RTLIL::Module *m)
{
	module = m;
	for (auto *cs : cases)
		cs->setModuleRecursive(m);
}

RTLIL::CaseRule *RTLIL::CaseRule::clone() const
{
	RTLIL::CaseRule *new_caserule = new RTLIL::CaseRule;
	new_caserule->compare = compare;
	new_caserule->actions = actions;
	new_caserule->attributes = attributes;
	// clone() drops src — CaseRule has no pool backpointer, so we can't
	// retain. The caller (Module::addProcess(name, other)) is responsible
	// for walking the cloned tree and migrating src via context.
	for (auto &it : switches)
		new_caserule->switches.push_back(it->clone());
	return new_caserule;
}

RTLIL::SwitchRule::~SwitchRule()
{
	for (auto it = cases.begin(); it != cases.end(); it++)
		delete *it;
}

bool RTLIL::SwitchRule::empty() const
{
	return cases.empty();
}

RTLIL::SwitchRule *RTLIL::SwitchRule::clone() const
{
	RTLIL::SwitchRule *new_switchrule = new RTLIL::SwitchRule;
	new_switchrule->signal = signal;
	new_switchrule->attributes = attributes;
	// clone() drops src — see CaseRule::clone for rationale.
	for (auto &it : cases)
		new_switchrule->cases.push_back(it->clone());
	return new_switchrule;

}

RTLIL::SyncRule *RTLIL::SyncRule::clone() const
{
	RTLIL::SyncRule *new_syncrule = new RTLIL::SyncRule;
	new_syncrule->type = type;
	new_syncrule->signal = signal;
	new_syncrule->actions = actions;
	new_syncrule->mem_write_actions = mem_write_actions;
	// Drop meta_idx_ on the cloned MemWriteActions — the integer was
	// copied by the vector assignment above without registering with
	// any pool; the caller is responsible for migrating src across the
	// clone via context (see Process::clone).
	for (auto &mwa : new_syncrule->mem_write_actions)
		mwa.meta_ = nullptr;
	return new_syncrule;
}

namespace {
	// Release the meta src slot on each AttrObject inside a Process tree.
	// Called from Process::~Process while module->design is still valid.
	void release_process_tree_src(RTLIL::Process *p)
	{
		if (!p->module || !p->module->design)
			return;
		RTLIL::Design *d = p->module->design;
		std::vector<RTLIL::CaseRule*> case_stack{&p->root_case};
		while (!case_stack.empty()) {
			RTLIL::CaseRule *cs = case_stack.back();
			case_stack.pop_back();
			d->obj_release_src(cs);
			for (auto *sw : cs->switches) {
				d->obj_release_src(sw);
				for (auto *case_ : sw->cases)
					case_stack.push_back(case_);
			}
		}
		for (auto *sync : p->syncs)
			for (auto &mwa : sync->mem_write_actions)
				d->obj_release_src(&mwa);
	}
}

RTLIL::Process::~Process()
{
	// Walk the inner tree first while module->design is still valid,
	// then release Process's own src.
	release_process_tree_src(this);
	if (module && module->design)
		module->design->obj_release_src(this);
	for (auto it = syncs.begin(); it != syncs.end(); it++)
		delete *it;
}

TwineRef RTLIL::Process::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}

void RTLIL::Process::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "Process::set_src_id requires the process to be attached to a module in a design");
	module->design->obj_set_src_id(this, id);
}

void RTLIL::Process::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "Process::set_src_attribute requires the process to be attached to a module in a design");
	module->design->set_src_attribute(this, src);
}

std::string RTLIL::Process::get_src_attribute() const
{
	if (!module || !module->design)
		return {};
	return module->design->get_src_attribute(this);
}

void RTLIL::Process::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "Process::adopt_src_from requires the process to be attached to a module in a design");
	module->design->adopt_src_from(this, source);
}

void RTLIL::Process::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "Process::absorb_attrs requires the process to be attached to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

RTLIL::Process *RTLIL::Process::clone() const
{
	RTLIL::Process *new_proc = new RTLIL::Process;

	new_proc->attributes = attributes;
	// clone() drops src across the whole tree; the caller is responsible
	// for migrating src via context after the clone has a module.

	RTLIL::CaseRule *rc_ptr = root_case.clone();
	new_proc->root_case = *rc_ptr;
	rc_ptr->switches.clear();
	delete rc_ptr;

	for (auto &it : syncs)
		new_proc->syncs.push_back(it->clone());

	return new_proc;
}

RTLIL::Memory::~Memory()
{
	if (module && module->design)
		module->design->obj_release_src(this);
#ifdef YOSYS_ENABLE_PYTHON
	RTLIL::Memory::get_all_memorys()->erase(hashidx_);
#endif
}

TwineRef RTLIL::Memory::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}

void RTLIL::Memory::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "Memory::set_src_id requires the memory to be attached to a module in a design");
	module->design->obj_set_src_id(this, id);
}

void RTLIL::Memory::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "Memory::set_src_attribute requires the memory to be attached to a module in a design");
	module->design->set_src_attribute(this, src);
}

std::string RTLIL::Memory::get_src_attribute() const
{
	if (!module || !module->design)
		return {};
	return module->design->get_src_attribute(this);
}

void RTLIL::Memory::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "Memory::adopt_src_from requires the memory to be attached to a module in a design");
	module->design->adopt_src_from(this, source);
}

void RTLIL::Memory::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "Memory::absorb_attrs requires the memory to be attached to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

// CaseRule / SwitchRule / MemWriteAction src helpers — all delegate to
// module->design->obj_* via the back-pointer added in the earlier commit.
TwineRef RTLIL::CaseRule::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}
void RTLIL::CaseRule::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "CaseRule::set_src_id requires the case to belong to a module in a design");
	module->design->obj_set_src_id(this, id);
}
void RTLIL::CaseRule::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "CaseRule::set_src_attribute requires the case to belong to a module in a design");
	module->design->set_src_attribute(this, src);
}
std::string RTLIL::CaseRule::get_src_attribute() const
{
	if (!module || !module->design)
		return {};
	return module->design->get_src_attribute(this);
}
void RTLIL::CaseRule::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "CaseRule::adopt_src_from requires the case to belong to a module in a design");
	module->design->adopt_src_from(this, source);
}
void RTLIL::CaseRule::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "CaseRule::absorb_attrs requires the case to belong to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

TwineRef RTLIL::SwitchRule::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}
void RTLIL::SwitchRule::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "SwitchRule::set_src_id requires the switch to belong to a module in a design");
	module->design->obj_set_src_id(this, id);
}
void RTLIL::SwitchRule::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "SwitchRule::set_src_attribute requires the switch to belong to a module in a design");
	module->design->set_src_attribute(this, src);
}
std::string RTLIL::SwitchRule::get_src_attribute() const
{
	if (!module || !module->design)
		return {};
	return module->design->get_src_attribute(this);
}
void RTLIL::SwitchRule::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "SwitchRule::adopt_src_from requires the switch to belong to a module in a design");
	module->design->adopt_src_from(this, source);
}
void RTLIL::SwitchRule::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "SwitchRule::absorb_attrs requires the switch to belong to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

TwineRef RTLIL::MemWriteAction::src_id() const
{
	if (!module || !module->design)
		return Twine::Null;
	return module->design->obj_src_id(this);
}
void RTLIL::MemWriteAction::set_src_id(TwineRef id)
{
	log_assert(module && module->design && "MemWriteAction::set_src_id requires the action to belong to a module in a design");
	module->design->obj_set_src_id(this, id);
}
void RTLIL::MemWriteAction::set_src_attribute(TwineRef src)
{
	if (src == Twine::Null && meta_ == nullptr)
		return;
	log_assert(module && module->design && "MemWriteAction::set_src_attribute requires the action to belong to a module in a design");
	module->design->set_src_attribute(this, src);
}
std::string RTLIL::MemWriteAction::get_src_attribute() const
{
	if (!module || !module->design)
		return {};
	return module->design->get_src_attribute(this);
}
void RTLIL::MemWriteAction::adopt_src_from(const RTLIL::AttrObject *source)
{
	log_assert(module && module->design && "MemWriteAction::adopt_src_from requires the action to belong to a module in a design");
	module->design->adopt_src_from(this, source);
}
void RTLIL::MemWriteAction::absorb_attrs(dict<IdString, RTLIL::Const> &&buf)
{
	log_assert(module && module->design && "MemWriteAction::absorb_attrs requires the action to belong to a module in a design");
	module->design->absorb_attrs(this, std::move(buf));
}

#ifdef YOSYS_ENABLE_PYTHON
static std::map<unsigned int, RTLIL::Memory*> all_memorys;
std::map<unsigned int, RTLIL::Memory*> *RTLIL::Memory::get_all_memorys(void)
{
	return &all_memorys;
}
#endif

template class CellAdderMixin<RTLIL::Module>;
template class CellAdderMixin<RTLIL::Patch>;

YOSYS_NAMESPACE_END
