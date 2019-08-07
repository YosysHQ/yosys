/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct mutate_t {
	string mode;
	pool<string> src;
	IdString module, cell;
	IdString port, wire;
	int portbit = -1;
	int ctrlbit = -1;
	int wirebit = -1;
	bool used = false;
};

struct mutate_opts_t {
	int seed = 0;
	std::string mode;
	pool<string> src;
	IdString module, cell, port, wire;
	int portbit = -1;
	int ctrlbit = -1;
	int wirebit = -1;

	IdString ctrl_name;
	int ctrl_width = -1, ctrl_value = -1;

	bool none = false;

	int pick_cover_prcnt = 80;

	int weight_cover = 500;

	int weight_pq_w = 100;
	int weight_pq_b = 100;
	int weight_pq_c = 100;
	int weight_pq_s = 100;

	int weight_pq_mw = 100;
	int weight_pq_mb = 100;
	int weight_pq_mc = 100;
	int weight_pq_ms = 100;
};

void database_add(std::vector<mutate_t> &database, const mutate_opts_t &opts, const mutate_t &entry)
{
	if (!opts.mode.empty() && opts.mode != entry.mode)
		return;

	if (!opts.src.empty()) {
		bool found_match = false;
		for (auto &s : opts.src) {
			if (entry.src.count(s))
				found_match = true;
		}
		if (!found_match)
			return;
	}

	if (!opts.module.empty() && opts.module != entry.module)
		return;

	if (!opts.cell.empty() && opts.cell != entry.cell)
		return;

	if (!opts.port.empty() && opts.port != entry.port)
		return;

	if (opts.portbit >= 0 && opts.portbit != entry.portbit)
		return;

	if (opts.ctrlbit >= 0 && opts.ctrlbit != entry.ctrlbit)
		return;

	if (!opts.wire.empty() && opts.wire != entry.wire)
		return;

	if (opts.wirebit >= 0 && opts.wirebit != entry.wirebit)
		return;

	database.push_back(entry);
}

struct xs128_t
{
	uint32_t x = 123456789;
	uint32_t y = 0, z = 0, w = 0;

	xs128_t(int seed = 0) : w(seed) {
		next();
		next();
		next();
	}

	void next() {
		uint32_t t = x ^ (x << 11);
		x = y, y = z, z = w;
		w ^= (w >> 19) ^ t ^ (t >> 8);
	}

	int operator()() {
		next();
		return w & 0x3fffffff;
	}

	int operator()(int n) {
		if (n < 2)
			return 0;
		while (1) {
			int k = (*this)(), p = k % n;
			if ((k - p + n) <= 0x40000000)
				return p;
		}
	}
};

struct coverdb_t
{
	dict<string, int> src_db;
	dict<tuple<IdString, IdString>, int> wire_db;
	dict<tuple<IdString, IdString, int>, int> wirebit_db;

	void insert(const mutate_t &m) {
		if (!m.wire.empty()) {
			wire_db[tuple<IdString, IdString>(m.module, m.wire)] = 0;
			wirebit_db[tuple<IdString, IdString, int>(m.module, m.wire, m.wirebit)] = 0;
		}
		for (auto &s : m.src) {
			src_db[s] = 0;
		}
	}

	void update(const mutate_t &m) {
		if (!m.wire.empty()) {
			wire_db.at(tuple<IdString, IdString>(m.module, m.wire))++;
			wirebit_db.at(tuple<IdString, IdString, int>(m.module, m.wire, m.wirebit))++;
		}
		for (auto &s : m.src) {
			src_db.at(s)++;
		}
	}

	int score(const mutate_t &m) {
		int this_score = m.src.empty() ? 0 : 1;
		if (!m.wire.empty()) {
			this_score += wire_db.at(tuple<IdString, IdString>(m.module, m.wire)) ? 0 : 5;
			this_score += wirebit_db.at(tuple<IdString, IdString, int>(m.module, m.wire, m.wirebit)) ? 0 : 1;
		}
		for (auto &s : m.src) {
			this_score += src_db.at(s) ? 0 : 5;
		}
		return this_score;
	}
};

struct mutate_queue_t
{
	pool<mutate_t*, hash_ptr_ops> db;

	mutate_t *pick(xs128_t &rng, coverdb_t &coverdb, const mutate_opts_t &opts) {
		mutate_t *m = nullptr;
		if (rng(100) < opts.pick_cover_prcnt) {
			vector<mutate_t*> candidates, rmqueue;
			int best_score = -1;
			for (auto p : db) {
				if (p->used) {
					rmqueue.push_back(p);
					continue;
				}
				int this_score = coverdb.score(*p);
				if (this_score > best_score) {
					best_score = this_score;
					candidates.clear();
				}
				if (best_score == this_score)
					candidates.push_back(p);
			}
			for (auto p : rmqueue)
				db.erase(p);
			if (!candidates.empty())
				m = candidates[rng(GetSize(candidates))];
		}
		if (m == nullptr) {
			while (!db.empty()) {
				int i = rng(GetSize(db));
				auto it = db.element(i);
				mutate_t *p = *it;
				db.erase(it);
				if (p->used == false) {
					m = p;
					break;
				}
			}
		}
		return m;
	}

	void add(mutate_t *m) {
		db.insert(m);
	}
};

template <typename K, typename T>
struct mutate_chain_queue_t
{
	dict<K, T> db;

	mutate_t *pick(xs128_t &rng, coverdb_t &coverdb, const mutate_opts_t &opts) {
		while (!db.empty()) {
			int i = rng(GetSize(db));
			auto it = db.element(i);
			mutate_t *m = it->second.pick(rng, coverdb, opts);
			if (m != nullptr)
				return m;
			db.erase(it);
		}
		return nullptr;
	}

	template<typename... Args>
	void add(mutate_t *m, K key, Args... args) {
		db[key].add(m, args...);
	}
};

template <typename K, typename T>
struct mutate_once_queue_t
{
	dict<K, T> db;

	mutate_t *pick(xs128_t &rng, coverdb_t &coverdb, const mutate_opts_t &opts) {
		while (!db.empty()) {
			int i = rng(GetSize(db));
			auto it = db.element(i);
			mutate_t *m = it->second.pick(rng, coverdb, opts);
			db.erase(it);
			if (m != nullptr)
				return m;
		}
		return nullptr;
	}

	template<typename... Args>
	void add(mutate_t *m, K key, Args... args) {
		db[key].add(m, args...);
	}
};

void database_reduce(std::vector<mutate_t> &database, const mutate_opts_t &opts, int N, xs128_t &rng)
{
	std::vector<mutate_t> new_database;
	coverdb_t coverdb;

	int total_weight = opts.weight_cover + opts.weight_pq_w + opts.weight_pq_b + opts.weight_pq_c + opts.weight_pq_s;
	total_weight += opts.weight_pq_mw + opts.weight_pq_mb + opts.weight_pq_mc + opts.weight_pq_ms;

	if (N >= GetSize(database))
		return;

	mutate_once_queue_t<tuple<IdString, IdString>, mutate_queue_t> primary_queue_wire;
	mutate_once_queue_t<tuple<IdString, IdString, int>, mutate_queue_t> primary_queue_bit;
	mutate_once_queue_t<tuple<IdString, IdString>, mutate_queue_t> primary_queue_cell;
	mutate_once_queue_t<string, mutate_queue_t> primary_queue_src;

	mutate_chain_queue_t<IdString, mutate_once_queue_t<IdString, mutate_queue_t>> primary_queue_module_wire;
	mutate_chain_queue_t<IdString, mutate_once_queue_t<pair<IdString, int>, mutate_queue_t>> primary_queue_module_bit;
	mutate_chain_queue_t<IdString, mutate_once_queue_t<IdString, mutate_queue_t>> primary_queue_module_cell;
	mutate_chain_queue_t<IdString, mutate_once_queue_t<string, mutate_queue_t>> primary_queue_module_src;

	for (auto &m : database)
	{
		coverdb.insert(m);

		if (!m.wire.empty()) {
			primary_queue_wire.add(&m, tuple<IdString, IdString>(m.module, m.wire));
			primary_queue_bit.add(&m, tuple<IdString, IdString, int>(m.module, m.wire, m.wirebit));
			primary_queue_module_wire.add(&m, m.module, m.wire);
			primary_queue_module_bit.add(&m, m.module, pair<IdString, int>(m.wire, m.wirebit));
		}

		primary_queue_cell.add(&m, tuple<IdString, IdString>(m.module, m.cell));
		primary_queue_module_cell.add(&m, m.module, m.cell);

		for (auto &s : m.src) {
			primary_queue_src.add(&m, s);
			primary_queue_module_src.add(&m, m.module, s);
		}
	}

	vector<mutate_t*> cover_candidates;
	int best_cover_score = -1;
	bool skip_cover = false;

	while (GetSize(new_database) < N)
	{
		int k = rng(total_weight);

		k -= opts.weight_cover;
		if (k < 0) {
			while (!skip_cover) {
				if (cover_candidates.empty()) {
					best_cover_score = -1;
					for (auto &m : database) {
						if (m.used || m.src.empty())
							continue;
						int this_score = -1;
						for (auto &s : m.src) {
							if (this_score == -1 || this_score > coverdb.src_db.at(s))
								this_score = coverdb.src_db.at(s);
						}
						log_assert(this_score != -1);
						if (best_cover_score == -1 || this_score < best_cover_score) {
							cover_candidates.clear();
							best_cover_score = this_score;
						}
						if (best_cover_score == this_score)
							cover_candidates.push_back(&m);
					}
					if (best_cover_score == -1) {
						skip_cover = true;
						break;
					}
				}

				mutate_t *m = nullptr;
				while (!cover_candidates.empty())
				{
					int idx = rng(GetSize(cover_candidates));
					mutate_t *p = cover_candidates[idx];
					cover_candidates[idx] = cover_candidates.back();
					cover_candidates.pop_back();

					if (p->used)
						continue;

					int this_score = -1;
					for (auto &s : p->src) {
						if (this_score == -1 || this_score > coverdb.src_db.at(s))
							this_score = coverdb.src_db.at(s);
					}

					if (this_score != best_cover_score)
						continue;

					m = p;
					break;
				}

				if (m != nullptr) {
					m->used = true;
					coverdb.update(*m);
					new_database.push_back(*m);
					break;
				}
			}
			continue;
		}

#define X(__wght, __queue)                               \
    k -= __wght;                                         \
    if (k < 0) {                                         \
      mutate_t *m = __queue.pick(rng, coverdb, opts);    \
      if (m != nullptr) {                                \
        m->used = true;                                  \
        coverdb.update(*m);                              \
        new_database.push_back(*m);                      \
      };                                                 \
      continue;                                          \
    }

		X(opts.weight_pq_w, primary_queue_wire)
		X(opts.weight_pq_b, primary_queue_bit)
		X(opts.weight_pq_c, primary_queue_cell)
		X(opts.weight_pq_s, primary_queue_src)

		X(opts.weight_pq_mw, primary_queue_module_wire)
		X(opts.weight_pq_mb, primary_queue_module_bit)
		X(opts.weight_pq_mc, primary_queue_module_cell)
		X(opts.weight_pq_ms, primary_queue_module_src)
#undef X
	}

	std::swap(new_database, database);

	int covered_src_cnt = 0;
	int covered_wire_cnt = 0;
	int covered_wirebit_cnt = 0;

	for (auto &it : coverdb.src_db)
		if (it.second)
			covered_src_cnt++;

	for (auto &it : coverdb.wire_db)
		if (it.second)
			covered_wire_cnt++;

	for (auto &it : coverdb.wirebit_db)
		if (it.second)
			covered_wirebit_cnt++;

	log("Covered %d/%d src attributes (%.2f%%).\n", covered_src_cnt, GetSize(coverdb.src_db), 100.0 * covered_src_cnt / GetSize(coverdb.src_db));
	log("Covered %d/%d wires (%.2f%%).\n", covered_wire_cnt, GetSize(coverdb.wire_db), 100.0 * covered_wire_cnt / GetSize(coverdb.wire_db));
	log("Covered %d/%d wire bits (%.2f%%).\n", covered_wirebit_cnt, GetSize(coverdb.wirebit_db), 100.0 * covered_wirebit_cnt / GetSize(coverdb.wirebit_db));
}

void mutate_list(Design *design, const mutate_opts_t &opts, const string &filename, const string &srcsfile, int N)
{
	pool<string> sources;
	std::vector<mutate_t> database;
	xs128_t rng(opts.seed);

	for (auto module : design->selected_modules())
	{
		if (!opts.module.empty() && module->name != opts.module)
			continue;

		SigMap sigmap(module);
		dict<SigBit, int> bit_user_cnt;

		for (auto wire : module->wires()) {
			if (wire->name[0] == '\\' && wire->attributes.count("\\src"))
				sigmap.add(wire);
		}

		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					bit_user_cnt[bit]++;
			}
		}

		for (auto wire : module->selected_wires())
		{
			for (SigBit bit : SigSpec(wire))
			{
				SigBit sigbit = sigmap(bit);

				if (bit.wire == nullptr || sigbit.wire == nullptr)
					continue;

				if (!bit.wire->port_id != !sigbit.wire->port_id) {
					if (bit.wire->port_id)
						sigmap.add(bit);
					continue;
				}

				if (!bit.wire->name[0] != !sigbit.wire->name[0]) {
					if (bit.wire->name[0] == '\\')
						sigmap.add(bit);
					continue;
				}
			}
		}

		for (auto cell : module->selected_cells())
		{
			if (!opts.cell.empty() && cell->name != opts.cell)
				continue;

			for (auto &conn : cell->connections())
			{
				for (int i = 0; i < GetSize(conn.second); i++) {
					mutate_t entry;
					entry.module = module->name;
					entry.cell = cell->name;
					entry.port = conn.first;
					entry.portbit = i;

					for (auto &s : cell->get_strpool_attribute("\\src"))
						entry.src.insert(s);

					SigBit bit = sigmap(conn.second[i]);
					if (bit.wire && bit.wire->name[0] == '\\' && (cell->output(conn.first) || bit_user_cnt[bit] == 1)) {
						for (auto &s : bit.wire->get_strpool_attribute("\\src"))
							entry.src.insert(s);
						entry.wire = bit.wire->name;
						entry.wirebit = bit.offset;
					}

					if (!srcsfile.empty())
						sources.insert(entry.src.begin(), entry.src.end());

					entry.mode = "inv";
					database_add(database, opts, entry);

					entry.mode = "const0";
					database_add(database, opts, entry);

					entry.mode = "const1";
					database_add(database, opts, entry);

					entry.mode = "cnot0";
					entry.ctrlbit = rng(GetSize(conn.second));
					if (entry.ctrlbit != entry.portbit && conn.second[entry.ctrlbit].wire)
						database_add(database, opts, entry);

					entry.mode = "cnot1";
					entry.ctrlbit = rng(GetSize(conn.second));
					if (entry.ctrlbit != entry.portbit && conn.second[entry.ctrlbit].wire)
						database_add(database, opts, entry);
				}
			}
		}
	}

	log("Raw database size: %d\n", GetSize(database));
	if (N != 0) {
		database_reduce(database, opts, opts.none ? N-1 : N, rng);
		log("Reduced database size: %d\n", GetSize(database));
	}

	if (!srcsfile.empty()) {
		std::ofstream sout;
		sout.open(srcsfile, std::ios::out | std::ios::trunc);
		if (!sout.is_open())
			log_error("Could not open file \"%s\" with write access.\n", srcsfile.c_str());
		sources.sort();
		for (auto &s : sources)
			sout << s << std::endl;
	}

	std::ofstream fout;

	if (!filename.empty()) {
		fout.open(filename, std::ios::out | std::ios::trunc);
		if (!fout.is_open())
			log_error("Could not open file \"%s\" with write access.\n", filename.c_str());
	}

	int ctrl_value = opts.ctrl_value;

	if (opts.none) {
		string str = "mutate";
		if (!opts.ctrl_name.empty())
			str += stringf(" -ctrl %s %d %d", log_id(opts.ctrl_name), opts.ctrl_width, ctrl_value++);
		str += " -mode none";
		if (filename.empty())
			log("%s\n", str.c_str());
		else
			fout << str << std::endl;
	}

	for (auto &entry : database) {
		string str = "mutate";
		if (!opts.ctrl_name.empty())
			str += stringf(" -ctrl %s %d %d", log_id(opts.ctrl_name), opts.ctrl_width, ctrl_value++);
		str += stringf(" -mode %s", entry.mode.c_str());
		if (!entry.module.empty())
			str += stringf(" -module %s", log_id(entry.module));
		if (!entry.cell.empty())
			str += stringf(" -cell %s", log_id(entry.cell));
		if (!entry.port.empty())
			str += stringf(" -port %s", log_id(entry.port));
		if (entry.portbit >= 0)
			str += stringf(" -portbit %d", entry.portbit);
		if (entry.ctrlbit >= 0)
			str += stringf(" -ctrlbit %d", entry.ctrlbit);
		if (!entry.wire.empty())
			str += stringf(" -wire %s", log_id(entry.wire));
		if (entry.wirebit >= 0)
			str += stringf(" -wirebit %d", entry.wirebit);
		for (auto &s : entry.src)
			str += stringf(" -src %s", s.c_str());
		if (filename.empty())
			log("%s\n", str.c_str());
		else
			fout << str << std::endl;
	}
}

SigSpec mutate_ctrl_sig(Module *module, IdString name, int width)
{
	Wire *ctrl_wire = module->wire(name);

	if (ctrl_wire == nullptr)
	{
		log("Adding ctrl port %s to module %s.\n", log_id(name), log_id(module));

		ctrl_wire = module->addWire(name, width);
		ctrl_wire->port_input = true;
		module->fixup_ports();

		for (auto mod : module->design->modules())
		for (auto cell : mod->cells())
		{
			if (cell->type != module->name)
				continue;

			SigSpec ctrl = mutate_ctrl_sig(mod, name, width);

			log("Connecting ctrl port to cell %s in module %s.\n", log_id(cell), log_id(mod));
			cell->setPort(name, ctrl);
		}
	}

	log_assert(GetSize(ctrl_wire) == width);
	return ctrl_wire;
}

SigBit mutate_ctrl(Module *module, const mutate_opts_t &opts)
{
	if (opts.ctrl_name.empty())
		return State::S1;

	SigSpec sig = mutate_ctrl_sig(module, opts.ctrl_name, opts.ctrl_width);
	return module->Eq(NEW_ID, sig, Const(opts.ctrl_value, GetSize(sig)));
}

SigSpec mutate_ctrl_mux(Module *module, const mutate_opts_t &opts, SigSpec unchanged_sig, SigSpec changed_sig)
{
	SigBit ctrl_bit = mutate_ctrl(module, opts);
	if (ctrl_bit == State::S0)
		return unchanged_sig;
	if (ctrl_bit == State::S1)
		return changed_sig;
	return module->Mux(NEW_ID, unchanged_sig, changed_sig, ctrl_bit);
}

void mutate_inv(Design *design, const mutate_opts_t &opts)
{
	Module *module = design->module(opts.module);
	Cell *cell = module->cell(opts.cell);

	SigBit bit = cell->getPort(opts.port)[opts.portbit];
	SigBit inbit, outbit;

	if (cell->input(opts.port))
	{
		log("Add input inverter at %s.%s.%s[%d].\n", log_id(module), log_id(cell), log_id(opts.port), opts.portbit);
		SigBit outbit = module->Not(NEW_ID, bit);
		bit = mutate_ctrl_mux(module, opts, bit, outbit);
	}
	else
	{
		log("Add output inverter at %s.%s.%s[%d].\n", log_id(module), log_id(cell), log_id(opts.port), opts.portbit);
		SigBit inbit = module->addWire(NEW_ID);
		SigBit outbit = module->Not(NEW_ID, inbit);
		module->connect(bit, mutate_ctrl_mux(module, opts, inbit, outbit));
		bit = inbit;
	}

	SigSpec s = cell->getPort(opts.port);
	s[opts.portbit] = bit;
	cell->setPort(opts.port, s);
}

void mutate_const(Design *design, const mutate_opts_t &opts, bool one)
{
	Module *module = design->module(opts.module);
	Cell *cell = module->cell(opts.cell);

	SigBit bit = cell->getPort(opts.port)[opts.portbit];
	SigBit inbit, outbit;

	if (cell->input(opts.port))
	{
		log("Add input constant %d at %s.%s.%s[%d].\n", one ? 1 : 0, log_id(module), log_id(cell), log_id(opts.port), opts.portbit);
		SigBit outbit = one ? State::S1 : State::S0;
		bit = mutate_ctrl_mux(module, opts, bit, outbit);
	}
	else
	{
		log("Add output constant %d at %s.%s.%s[%d].\n", one ? 1 : 0, log_id(module), log_id(cell), log_id(opts.port), opts.portbit);
		SigBit inbit = module->addWire(NEW_ID);
		SigBit outbit = one ? State::S1 : State::S0;
		module->connect(bit, mutate_ctrl_mux(module, opts, inbit, outbit));
		bit = inbit;
	}

	SigSpec s = cell->getPort(opts.port);
	s[opts.portbit] = bit;
	cell->setPort(opts.port, s);
}

void mutate_cnot(Design *design, const mutate_opts_t &opts, bool one)
{
	Module *module = design->module(opts.module);
	Cell *cell = module->cell(opts.cell);

	SigBit bit = cell->getPort(opts.port)[opts.portbit];
	SigBit ctrl = cell->getPort(opts.port)[opts.ctrlbit];
	SigBit inbit, outbit;

	if (cell->input(opts.port))
	{
		log("Add input cnot%d at %s.%s.%s[%d,%d].\n", one ? 1 : 0, log_id(module), log_id(cell), log_id(opts.port), opts.portbit, opts.ctrlbit);
		SigBit outbit = one ? module->Xor(NEW_ID, bit, ctrl) : module->Xnor(NEW_ID, bit, ctrl);
		bit = mutate_ctrl_mux(module, opts, bit, outbit);
	}
	else
	{
		log("Add output cnot%d at %s.%s.%s[%d,%d].\n", one ? 1 : 0, log_id(module), log_id(cell), log_id(opts.port), opts.portbit, opts.ctrlbit);
		SigBit inbit = module->addWire(NEW_ID);
		SigBit outbit = one ? module->Xor(NEW_ID, inbit, ctrl) : module->Xnor(NEW_ID, inbit, ctrl);
		module->connect(bit, mutate_ctrl_mux(module, opts, inbit, outbit));
		bit = inbit;
	}

	SigSpec s = cell->getPort(opts.port);
	s[opts.portbit] = bit;
	cell->setPort(opts.port, s);
}

struct MutatePass : public Pass {
	MutatePass() : Pass("mutate", "generate or apply design mutations") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    mutate -list N [options] [selection]\n");
		log("\n");
		log("Create a list of N mutations using an even sampling.\n");
		log("\n");
		log("    -o filename\n");
		log("        Write list to this file instead of console output\n");
		log("\n");
		log("    -s filename\n");
		log("        Write a list of all src tags found in the design to the specified file\n");
		log("\n");
		log("    -seed N\n");
		log("        RNG seed for selecting mutations\n");
		log("\n");
		log("    -none\n");
		log("        Include a \"none\" mutation in the output\n");
		log("\n");
		log("    -ctrl name width value\n");
		log("        Add -ctrl options to the output. Use 'value' for first mutation, then\n");
		log("        simply count up from there.\n");
		log("\n");
		log("    -mode name\n");
		log("    -module name\n");
		log("    -cell name\n");
		log("    -port name\n");
		log("    -portbit int\n");
		log("    -ctrlbit int\n");
		log("    -wire name\n");
		log("    -wirebit int\n");
		log("    -src string\n");
		log("        Filter list of mutation candidates to those matching\n");
		log("        the given parameters.\n");
		log("\n");
		log("    -cfg option int\n");
		log("        Set a configuration option. Options available:\n");
		log("          weight_pq_w weight_pq_b weight_pq_c weight_pq_s\n");
		log("          weight_pq_mw weight_pq_mb weight_pq_mc weight_pq_ms\n");
		log("          weight_cover pick_cover_prcnt\n");
		log("\n");
		log("\n");
		log("    mutate -mode MODE [options]\n");
		log("\n");
		log("Apply the given mutation.\n");
		log("\n");
		log("    -ctrl name width value\n");
		log("        Add a control signal with the given name and width. The mutation is\n");
		log("        activated if the control signal equals the given value.\n");
		log("\n");
		log("    -module name\n");
		log("    -cell name\n");
		log("    -port name\n");
		log("    -portbit int\n");
		log("    -ctrlbit int\n");
		log("        Mutation parameters, as generated by 'mutate -list N'.\n");
		log("\n");
		log("    -wire name\n");
		log("    -wirebit int\n");
		log("    -src string\n");
		log("        Ignored. (They are generated by -list for documentation purposes.)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		mutate_opts_t opts;
		string filename;
		string srcsfile;
		int N = -1;

		log_header(design, "Executing MUTATE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-list" && argidx+1 < args.size()) {
				N = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-o" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-s" && argidx+1 < args.size()) {
				srcsfile = args[++argidx];
				continue;
			}
			if (args[argidx] == "-seed" && argidx+1 < args.size()) {
				opts.seed = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-none") {
				opts.none = true;
				continue;
			}
			if (args[argidx] == "-mode" && argidx+1 < args.size()) {
				opts.mode = args[++argidx];
				continue;
			}
			if (args[argidx] == "-ctrl" && argidx+3 < args.size()) {
				opts.ctrl_name = RTLIL::escape_id(args[++argidx]);
				opts.ctrl_width = atoi(args[++argidx].c_str());
				opts.ctrl_value = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-module" && argidx+1 < args.size()) {
				opts.module = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-cell" && argidx+1 < args.size()) {
				opts.cell = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-port" && argidx+1 < args.size()) {
				opts.port = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-portbit" && argidx+1 < args.size()) {
				opts.portbit = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-ctrlbit" && argidx+1 < args.size()) {
				opts.ctrlbit = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-wire" && argidx+1 < args.size()) {
				opts.wire = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-wirebit" && argidx+1 < args.size()) {
				opts.wirebit = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-src" && argidx+1 < args.size()) {
				opts.src.insert(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-cfg" && argidx+2 < args.size()) {
				if (args[argidx+1] == "pick_cover_prcnt") {
					opts.pick_cover_prcnt = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_cover") {
					opts.weight_cover = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_w") {
					opts.weight_pq_w = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_b") {
					opts.weight_pq_b = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_c") {
					opts.weight_pq_c = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_s") {
					opts.weight_pq_s = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_mw") {
					opts.weight_pq_mw = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_mb") {
					opts.weight_pq_mb = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_mc") {
					opts.weight_pq_mc = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
				if (args[argidx+1] == "weight_pq_ms") {
					opts.weight_pq_ms = atoi(args[argidx+2].c_str());
					argidx += 2;
					continue;
				}
			}
			break;
		}
		extra_args(args, argidx, design);

		if (N >= 0) {
			mutate_list(design, opts, filename, srcsfile, N);
			return;
		}

		if (opts.mode == "none") {
			if (!opts.ctrl_name.empty()) {
				Module *topmod = opts.module.empty() ? design->top_module() : design->module(opts.module);
				if (topmod)
					mutate_ctrl_sig(topmod, opts.ctrl_name, opts.ctrl_width);
			}
			return;
		}

		if (opts.module.empty())
			log_cmd_error("Missing -module argument.\n");

		Module *module = design->module(opts.module);
		if (module == nullptr)
			log_cmd_error("Module %s not found.\n", log_id(opts.module));

		if (opts.cell.empty())
			log_cmd_error("Missing -cell argument.\n");

		Cell *cell = module->cell(opts.cell);
		if (cell == nullptr)
			log_cmd_error("Cell %s not found in module %s.\n", log_id(opts.cell), log_id(opts.module));

		if (opts.port.empty())
			log_cmd_error("Missing -port argument.\n");

		if (!cell->hasPort(opts.port))
			log_cmd_error("Port %s not found on cell %s.%s.\n", log_id(opts.port), log_id(opts.module), log_id(opts.cell));

		if (opts.portbit < 0)
			log_cmd_error("Missing -portbit argument.\n");

		if (GetSize(cell->getPort(opts.port)) <= opts.portbit)
			log_cmd_error("Out-of-range -portbit argument for port %s on cell %s.%s.\n", log_id(opts.port), log_id(opts.module), log_id(opts.cell));

		if (opts.mode == "inv") {
			mutate_inv(design, opts);
			return;
		}

		if (opts.mode == "const0" || opts.mode == "const1") {
			mutate_const(design, opts, opts.mode == "const1");
			return;
		}

		if (opts.ctrlbit < 0)
			log_cmd_error("Missing -ctrlbit argument.\n");

		if (GetSize(cell->getPort(opts.port)) <= opts.ctrlbit)
			log_cmd_error("Out-of-range -ctrlbit argument for port %s on cell %s.%s.\n", log_id(opts.port), log_id(opts.module), log_id(opts.cell));

		if (opts.mode == "cnot0" || opts.mode == "cnot1") {
			mutate_cnot(design, opts, opts.mode == "cnot1");
			return;
		}

		log_cmd_error("Invalid mode: %s\n", opts.mode.c_str());
	}
} MutatePass;

PRIVATE_NAMESPACE_END
