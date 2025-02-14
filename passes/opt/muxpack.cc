/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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

struct ExclusiveDatabase
{
	Module *module;
	const SigMap &sigmap;

	dict<SigBit, std::pair<SigSpec,std::vector<Const>>> sig_cmp_prev;

	ExclusiveDatabase(Module *module, const SigMap &sigmap, bool assume_excl, bool make_excl) : module(module), sigmap(sigmap)
	{
		if (assume_excl || make_excl) return;
		SigSpec const_sig, nonconst_sig;
		SigBit y_port;
		pool<Cell*> reduce_or;
		for (auto cell : module->cells()) {
			if (cell->type == ID($eq)) {
				nonconst_sig = sigmap(cell->getPort(ID::A));
				const_sig = sigmap(cell->getPort(ID::B));
				if (!const_sig.is_fully_const()) {
					if (!nonconst_sig.is_fully_const())
						continue;
					std::swap(nonconst_sig, const_sig);
				}
				y_port = sigmap(cell->getPort(ID::Y));
			}
			else if (cell->type == ID($logic_not)) {
				nonconst_sig = sigmap(cell->getPort(ID::A));
				const_sig = Const(State::S0, GetSize(nonconst_sig));
				y_port = sigmap(cell->getPort(ID::Y));
			}
			else if (cell->type == ID($reduce_or)) {
				reduce_or.insert(cell);
				continue;
			}
			else continue;

			log_assert(!nonconst_sig.empty());
			log_assert(!const_sig.empty());
			sig_cmp_prev[y_port] = std::make_pair(nonconst_sig,std::vector<Const>{const_sig.as_const()});
		}

		for (auto cell : reduce_or) {
			nonconst_sig = SigSpec();
			std::vector<Const> values;
			SigSpec a_port = sigmap(cell->getPort(ID::A));
			for (auto bit : a_port) {
				auto it = sig_cmp_prev.find(bit);
				if (it == sig_cmp_prev.end()) {
					nonconst_sig = SigSpec();
					break;
				}
				if (nonconst_sig.empty())
					nonconst_sig = it->second.first;
				else if (nonconst_sig != it->second.first) {
					nonconst_sig = SigSpec();
					break;
				}
				for (auto value : it->second.second)
					values.push_back(value);
			}
			if (nonconst_sig.empty())
				continue;
			y_port = sigmap(cell->getPort(ID::Y));
			sig_cmp_prev[y_port] = std::make_pair(nonconst_sig,std::move(values));
		}
	}

	bool query(const SigSpec &sig) const
	{
		SigSpec nonconst_sig;
		pool<Const> const_values;

		for (auto bit : sig) {
			auto it = sig_cmp_prev.find(bit);
			if (it == sig_cmp_prev.end())
				return false;

			if (nonconst_sig.empty())
				nonconst_sig = it->second.first;
			else if (nonconst_sig != it->second.first)
				return false;

			for (auto value : it->second.second)
				if (!const_values.insert(value).second)
					return false;
		}

		return true;
	}
};


struct MuxpackWorker
{
	Module *module;
	SigMap sigmap;

	int mux_count, pmux_count;

	pool<Cell*> remove_cells;
	// Driver data
	dict<SigBit, tuple<IdString, IdString, int>> bit_drivers_db;
	// Load data
	dict<SigBit, pool<tuple<IdString, IdString, int>>> bit_users_db;

	dict<SigSpec, Cell*> sig_chain_next;
	dict<SigSpec, Cell*> sig_chain_prev;
	pool<SigBit> sigbit_with_non_chain_users;
	pool<Cell*> chain_start_cells;
	pool<Cell*> candidate_cells;

	ExclusiveDatabase excl_db;

	void make_sig_chain_next_prev()
	{
		for (auto wire : module->wires())
		{
			if (wire->port_output || wire->get_bool_attribute(ID::keep)) {
				for (auto bit : sigmap(wire))
					sigbit_with_non_chain_users.insert(bit);
			}
		}

		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($mux), ID($pmux)) && !cell->get_bool_attribute(ID::keep))
			{
				SigSpec a_sig = sigmap(cell->getPort(ID::A));
				SigSpec b_sig;
				if (cell->type == ID($mux))
					b_sig = sigmap(cell->getPort(ID::B));
				SigSpec y_sig = sigmap(cell->getPort(ID::Y));
   
				if (sig_chain_next.count(a_sig))
					for (auto a_bit : a_sig)
						sigbit_with_non_chain_users.insert(a_bit);
				else {
					sig_chain_next[a_sig] = cell;
					candidate_cells.insert(cell);
				}

				if (!b_sig.empty()) {
					if (sig_chain_next.count(b_sig))
						for (auto b_bit : b_sig)
							sigbit_with_non_chain_users.insert(b_bit);
					else {
						sig_chain_next[b_sig] = cell;
						candidate_cells.insert(cell);
					}
				}

				sig_chain_prev[y_sig] = cell;
				continue;
			}

			for (auto conn : cell->connections())
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigbit_with_non_chain_users.insert(bit);
		}
	}

	void find_chain_start_cells(bool assume_excl)
	{
		for (auto cell : candidate_cells)
		{
			log("Considering %s (%s)\n", log_id(cell), log_id(cell->type));

			SigSpec a_sig = sigmap(cell->getPort(ID::A));
			if (cell->type == ID($mux)) {
				SigSpec b_sig = sigmap(cell->getPort(ID::B));
				if (sig_chain_prev.count(a_sig) + sig_chain_prev.count(b_sig) != 1)
					goto start_cell;

				if (!sig_chain_prev.count(a_sig))
					a_sig = b_sig;
			}
			else if (cell->type == ID($pmux)) {
				if (!sig_chain_prev.count(a_sig))
					goto start_cell;
			}
			else log_abort();

			for (auto bit : a_sig)
				if (sigbit_with_non_chain_users.count(bit))
					goto start_cell;

			{
				Cell *prev_cell = sig_chain_prev.at(a_sig);
				log_assert(prev_cell);
				SigSpec s_sig = sigmap(cell->getPort(ID::S));
				s_sig.append(sigmap(prev_cell->getPort(ID::S)));
				if (!assume_excl && !excl_db.query(s_sig))
					goto start_cell;
			}

			continue;

		start_cell:
			chain_start_cells.insert(cell);
		}
	}

	vector<Cell*> create_chain(Cell *start_cell)
	{
		vector<Cell*> chain;

		Cell *c = start_cell;
		while (c != nullptr)
		{
			chain.push_back(c);

			SigSpec y_sig = sigmap(c->getPort(ID::Y));

			if (sig_chain_next.count(y_sig) == 0)
				break;

			c = sig_chain_next.at(y_sig);
			if (chain_start_cells.count(c) != 0)
				break;
		}

		return chain;
	}

	void process_chain(vector<Cell*> &chain, bool make_excl)
	{
		if (GetSize(chain) < 2)
			return;

		int cursor = 0;
		while (cursor < GetSize(chain))
		{
			int cases = GetSize(chain) - cursor;

			Cell *first_cell = chain[cursor];
			dict<int, SigBit> taps_dict;

			if (cases < 2) {
				cursor++;
				continue;
			}

			Cell *last_cell = chain[cursor+cases-1];

			log("Converting %s.%s ... %s.%s to a pmux with %d cases.\n",
				log_id(module), log_id(first_cell), log_id(module), log_id(last_cell), cases);

			mux_count += cases;
			pmux_count += 1;

			first_cell->type = ID($pmux);
			SigSpec b_sig = first_cell->getPort(ID::B);
			SigSpec s_sig = first_cell->getPort(ID::S);

			for (int i = 1; i < cases; i++) {
				Cell* prev_cell = chain[cursor+i-1];
				Cell* cursor_cell = chain[cursor+i];
				Cell* cell = cursor_cell; // SILIMATE: Set cell to cursor cell for better naming
				if (sigmap(prev_cell->getPort(ID::Y)) == sigmap(cursor_cell->getPort(ID::A))) {
					b_sig.append(cursor_cell->getPort(ID::B));
					s_sig.append(cursor_cell->getPort(ID::S));
				}
				else {
					log_assert(cursor_cell->type == ID($mux));
					b_sig.append(cursor_cell->getPort(ID::A));
					s_sig.append(module->LogicNot(NEW_ID2_SUFFIX("sel"), cursor_cell->getPort(ID::S), false, cell->get_src_attribute())); // SILIMATE: Improve the naming
				}
				remove_cells.insert(cursor_cell);
			}

			if (make_excl) {
        /* Create the following one-hot select line decoder:
          	S0           S1             S2                S3   ...
          	|            |              |                 |
          	+--------+   +----------+   +-------------+   |
          	|       _|_  |         _|_  |            _|_  |
          	|       \_/  |         \_/  |            \_/  |
          	|        o   |          o   |             o   |
          	|        |   |          |   |      ___    |   |
          	|        +----------+   |   |     /   |   |   |
          	|        |   |      |___|   |    /    |___|   |
          	|        |___|      | & |  /    /     | & |   /     ...
          	|        | & |      \___/ /    /      \___/  /    / 
          	|        \___/        |   |   /         |   |    /
          	|          |          +------+          +-------+   
          	|          |          |   |             |   |
          	|          |          |___|             |___|
          	|          |          | & |             | & |
          	|          |          \___/             \___/
          	|          |            |                 |
          	S0       S0'S1       S0'S1'S2         S0'S1'S2'S3  ...
        */
				SigSpec decodedSelect;
				Cell *cell = last_cell;
				std::vector<RTLIL::SigBit> select_bits = s_sig.bits();
				RTLIL::SigBit prevSigNot = RTLIL::State::S1;
				RTLIL::SigBit prevSigAnd = RTLIL::State::S1;
				for (int i = (int) (select_bits.size() -1); i >= 0; i--) { 
					Yosys::RTLIL::SigBit sigbit = select_bits[i];
					if (i == (int) (select_bits.size() -1)) {
						decodedSelect.append(sigbit);
						Wire *not_y = module->addWire(NEW_ID2_SUFFIX("not_y"), 1);
						module->addNot(NEW_ID2_SUFFIX("not"), sigbit, not_y, false, last_cell->get_src_attribute());
						prevSigNot = not_y;
					} else if (i == (int) (select_bits.size() -2)) {
						Wire *and_y = module->addWire(NEW_ID2_SUFFIX("and_y"), 1);
						module->addAnd(NEW_ID2_SUFFIX("sel"), sigbit, prevSigNot, and_y, false, last_cell->get_src_attribute());
						decodedSelect.append(and_y);
						Wire *not_y = module->addWire(NEW_ID, 1);
						module->addNot(NEW_ID2_SUFFIX("not"), sigbit, not_y, false, last_cell->get_src_attribute());
						prevSigAnd = prevSigNot;
						prevSigNot = not_y;
					} else {
						Wire *and_y1 = module->addWire(NEW_ID2_SUFFIX("and_y1"), 1);
						module->addAnd(NEW_ID2_SUFFIX("sel"), prevSigAnd, prevSigNot, and_y1, false, last_cell->get_src_attribute());
						Wire *and_y2 = module->addWire(NEW_ID2_SUFFIX("and_y2"), 1);
						module->addAnd(NEW_ID2_SUFFIX("sel"), sigbit, and_y1, and_y2, false, last_cell->get_src_attribute());
						decodedSelect.append(and_y2);
						Wire *not_y = module->addWire(NEW_ID2_SUFFIX("not_y"), 1);
						module->addNot(NEW_ID2_SUFFIX("not"), sigbit, not_y, false, last_cell->get_src_attribute());
						prevSigAnd = and_y1;
						prevSigNot = not_y;
					}					
				}
				decodedSelect.reverse();
				first_cell->setPort(ID::S, decodedSelect);
			} else {
				first_cell->setPort(ID::S, s_sig);
			}
			first_cell->setPort(ID::B, b_sig);
			first_cell->setParam(ID::S_WIDTH, GetSize(s_sig));
			first_cell->setPort(ID::Y, last_cell->getPort(ID::Y));

			cursor += cases;
		}
	}

	void cleanup()
	{
		for (auto cell : remove_cells)
			module->remove(cell);

		remove_cells.clear();
		sig_chain_next.clear();
		sig_chain_prev.clear();
		chain_start_cells.clear();
		candidate_cells.clear();
	}

	MuxpackWorker(Module *module, bool assume_excl, bool make_excl) :
			module(module), sigmap(module), mux_count(0), pmux_count(0), excl_db(module, sigmap, assume_excl, make_excl)
	{

		// Build bit_drivers_db
		log("Building bit_drivers_db...\n");
		for (auto cell : module->cells()) {
			for (auto conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit(sigmap(conn.second[i]));
					bit_drivers_db[bit] = tuple<IdString, IdString, int>(cell->name, conn.first, i);
				}
			}
		}

		// Build bit_users_db
		log("Building bit_users_db...\n");
		for (auto cell : module->cells()) {
			for (auto conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit(sigmap(conn.second[i]));
					if (!bit_drivers_db.count(bit))
						continue;
					bit_users_db[bit].insert(
					  tuple<IdString, IdString, int>(cell->name, conn.first, i - std::get<2>(bit_drivers_db[bit])));
				}
			}
		}

		// Build bit_users_db for output ports
		log("Building bit_users_db for output ports...\n");
		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			SigSpec sig(sigmap(wire));
			for (int i = 0; i < GetSize(sig); i++) {
				SigBit bit(sig[i]);
				if (!bit_drivers_db.count(bit))
					continue;
				bit_users_db[bit].insert(
				  tuple<IdString, IdString, int>(wire->name, IdString(), i - std::get<2>(bit_drivers_db[bit])));
			}
		}

		make_sig_chain_next_prev();
		find_chain_start_cells(assume_excl);

		// Make the actual transform
		for (auto c : chain_start_cells) {
			vector<Cell *> chain = create_chain(c);
			process_chain(chain, make_excl);
		}
		// Clean up
		cleanup();
	}
};

struct MuxpackPass : public Pass {
	MuxpackPass() : Pass("muxpack", "$mux/$pmux cascades to $pmux") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    muxpack [options] [selection]\n");
		log("\n");
		log("This pass converts cascaded chains of $pmux cells (e.g. those create from case\n");
		log("constructs) and $mux cells (e.g. those created by if-else constructs) into\n");
		log("$pmux cells.\n");
		log("\n");
		log("This optimisation is conservative --- it will only pack $mux or $pmux cells\n");
		log("whose select lines are driven by '$eq' cells with other such cells if it can be\n");
		log("certain that their select inputs are mutually exclusive.\n");
		log("\n");
		log("    -assume_excl\n");
		log("        assume mutually exclusive constraint when packing (may result in inequivalence)\n");
		log("\n");
		log("    -make_excl\n");
		log("        Adds a one-hot decoder on the control signals\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool assume_excl = false;
		bool make_excl = false;

		log_header(design, "Executing MUXPACK pass ($mux cell cascades to $pmux).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-assume_excl") {
				assume_excl = true;
				continue;
			}
			if (args[argidx] == "-make_excl") {
				make_excl = true;
				assume_excl = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int mux_count = 0;
		int pmux_count = 0;

		for (auto module : design->selected_modules()) {
			MuxpackWorker worker(module, assume_excl, make_excl);
			mux_count += worker.mux_count;
			pmux_count += worker.pmux_count;
		}

		log("Converted %d (p)mux cells into %d pmux cells.\n", mux_count, pmux_count);
	}
} MuxpackPass;

PRIVATE_NAMESPACE_END
