// Internal. Request publishing this header if you need it
#ifndef MATCHER_H
#define MATCHER_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

struct MatchContext
{
	Module *module = nullptr;
	SigMap sigmap = {};
	dict<SigBit, pool<Cell*>> sigusers = {};
	pool<Cell*> blacklist_cells = {};
	pool<Cell*> autoremove_cells = {};
	dict<Cell*, int> rollback_cache = {};
	int rollback = 0;
	int depth = 0;
	bool generate_mode = false;
	uint32_t rngseed = 12345678;

	MatchContext(Module *module) : module(module), sigmap(module)
	{
		for (auto port : module->ports)
			add_siguser(module->wire(port), nullptr);
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				add_siguser(conn.second, cell);
	}

	MatchContext(const MatchContext &) = delete;
	MatchContext &operator=(const MatchContext &) = delete;

	~MatchContext()
	{
		for (auto cell : autoremove_cells)
			module->remove(cell);
	}

	void add_siguser(const SigSpec &sig, Cell *cell)
	{
		for (auto bit : sigmap(sig)) {
			if (bit.wire == nullptr)
				continue;
			sigusers[bit].insert(cell);
		}
	}

	int rng(unsigned int n)
	{
		rngseed ^= rngseed << 13;
		rngseed ^= rngseed >> 17;
		rngseed ^= rngseed << 5;
		return rngseed % n;
	}
};

struct MatchFrame
{
	MatchContext &ctx;
	int level = 0;
	Cell *cell = nullptr;
	bool inserted = false;

	MatchFrame(MatchContext &ctx) : ctx(ctx), level(++ctx.depth) {}
	MatchFrame(const MatchFrame &) = delete;
	MatchFrame &operator=(const MatchFrame &) = delete;
	~MatchFrame() { ctx.depth--; }

	void enter(Cell *candidate)
	{
		cell = candidate;
		inserted = ctx.rollback_cache.insert({candidate, level}).second;
	}

	[[nodiscard]] bool leave()
	{
		if (inserted)
			ctx.rollback_cache.erase(cell);
		if (ctx.rollback == 0)
			return false;
		if (ctx.rollback != level)
			return true;
		ctx.rollback = 0;
		return false;
	}
};

template <typename K, typename V = Cell*>
struct MatchIndex
{
	dict<K, vector<V>> buckets = {};

	void add(const K &key, const V &value)
	{
		buckets[key].push_back(value);
	}

	const vector<V> &find(const K &key) const
	{
		static const vector<V> none = {};
		auto it = buckets.find(key);
		return it == buckets.end() ? none : it->second;
	}
};

struct MatchPatternBase
{
	MatchContext &ctx;
	Module *module = nullptr;
	SigMap &sigmap;

	MatchPatternBase(MatchContext &ctx) : ctx(ctx), module(ctx.module), sigmap(ctx.sigmap) {}
	MatchPatternBase(const MatchPatternBase &) = delete;
	MatchPatternBase &operator=(const MatchPatternBase &) = delete;

	SigSpec port(Cell *cell, IdString portname) const
	{
		try {
			return sigmap(cell->getPort(portname));
		} catch(std::out_of_range&) { log_error("Accessing non existing port %s\n", cell->module->design->twines().str(portname).c_str()); }
	}

	SigSpec port(Cell *cell, IdString portname, const SigSpec &defval) const
	{
		return sigmap(cell->connections_.at(portname, defval));
	}

	Const param(Cell *cell, IdString paramname) const
	{
		try {
			return cell->getParam(paramname);
		} catch(std::out_of_range&) { log_error("Accessing non existing parameter %s\n", PooledName(module, paramname).unescape()); }
	}

	Const param(Cell *cell, IdString paramname, const Const &defval) const
	{
		return cell->parameters.at(paramname, defval);
	}

	int nusers(const SigSpec &sig) const
	{
		pool<Cell*> users = {};
		for (auto bit : sigmap(sig)) {
			auto it = ctx.sigusers.find(bit);
			if (it == ctx.sigusers.end())
				continue;
			for (auto user : it->second)
				users.insert(user);
		}
		return GetSize(users);
	}

	void add_siguser(const SigSpec &sig, Cell *cell)
	{
		ctx.add_siguser(sig, cell);
	}

	void blacklist(Cell *cell)
	{
		if (cell == nullptr || !ctx.blacklist_cells.insert(cell).second)
			return;
		auto it = ctx.rollback_cache.find(cell);
		if (it == ctx.rollback_cache.end())
			return;
		if (ctx.rollback == 0 || ctx.rollback > it->second)
			ctx.rollback = it->second;
	}

	void autoremove(Cell *cell)
	{
		if (cell == nullptr)
			return;
		ctx.autoremove_cells.insert(cell);
		blacklist(cell);
	}

	bool blacklisted(Cell *cell) const
	{
		return ctx.blacklist_cells.count(cell) != 0;
	}

	bool unwinding() const
	{
		return ctx.rollback != 0;
	}

	void finish()
	{
		ctx.rollback = -1;
	}

	int rng(unsigned int n)
	{
		return ctx.rng(n);
	}

	bool should_generate(bool found_any_match, int unmatched_pct, int matched_pct)
	{
		return ctx.generate_mode && rng(100) < (found_any_match ? matched_pct : unmatched_pct);
	}
};

template <typename Pattern, typename M>
struct MatchPattern : MatchPatternBase
{
	using Match = M;
	using Callback = void (*)(Pattern &, const Match &);
	using Stage = void (Pattern::*)(const Match &);

	Stage first_stage = nullptr;
	Callback on_accept = nullptr;
	int accept_cnt = 0;

	MatchPattern(MatchContext &ctx, Stage first_stage) : MatchPatternBase(ctx), first_stage(first_stage) {}

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		accept_cnt = 0;
		ctx.rollback = 0;
		(static_cast<Pattern *>(this)->*first_stage)(Match{});
		log_assert(ctx.rollback_cache.empty());
		return accept_cnt;
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*static_cast<Pattern *>(this), m);
		return unwinding();
	}

	template <typename Cells, typename Next>
	void match_each(const Match &m, const Cells &cells, Cell *Match::*state, Next next)
	{
		MatchFrame frame(ctx);
		for (Cell *cell : cells) {
			if (blacklisted(cell))
				continue;
			Match n = m;
			n.*state = cell;
			frame.enter(cell);
			(static_cast<Pattern *>(this)->*next)(n);
			if (frame.leave())
				return;
		}
	}
};

YOSYS_NAMESPACE_END

#endif
