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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BufnormPass : public Pass {
	BufnormPass() : Pass("bufnorm", "(experimental) convert design into buffered-normalized form") {
		experimental();
	}
	void help() override
	{
		log("\n");
		log("    bufnorm [options] [selection]\n");
		log("\n");
		log("Insert buffer cells into the design as needed, to make sure that each wire\n");
		log("has exactly one driving cell port, and aliasing wires are buffered using\n");
		log("buffer cells, than can be chained in a canonical order.\n");
		log("\n");
		log("Running 'bufnorm' on the whole design enters 'buffered-normalized mode'.\n");
		log("\n");
		log("    -buf\n");
		log("        Create $buf cells for all buffers. The default is to use $_BUF_ cells\n");
		log("        for sigle-bit buffers and $buf cells only for multi-bit buffers.\n");
		log("\n");
		log("    -chain\n");
		log("        Chain all alias wires. By default only wires with positive-valued\n");
		log("        'chain' or 'keep' attribute on them are chained.\n");
		log("\n");
		log("    -output\n");
		log("        Enable chaining of ouput ports wires.\n");
		log("\n");
		log("    -public\n");
		log("        Enable chaining of wires wth public names.\n");
		log("\n");
		log("    -nochain\n");
		log("        Disable chaining of wires with 'chain' attribute.\n");
		log("\n");
		log("    -nokeep\n");
		log("        Disable chaining of wires with 'keep' attribute.\n");
		log("\n");
		log("    -flat\n");
		log("        Alias for -nokeep and -nochain.\n");
		log("\n");
		log("    -nosticky\n");
		log("        Disable 'sticky' behavior of output ports already driving whole\n");
		log("        wires, and always enforce canonical sort order instead.\n");
		log("\n");
		log("    -alphasort\n");
		log("        Strictly use alphanumeric sort for chain-order. (Default is\n");
		log("        to chain 'keep' wires first, then ports in declaration order,\n");
		log("        and then the other wires in alphanumeric sort order.)\n");
		log("\n");
		// log("    -noinit\n");
		// log("        Do not move 'init' attributes to the wires on FF output ports.\n");
		// log("\n");
		log("Run 'bufnorm' with -pos, -bits, or -conn on the whole design to remove all\n");
		log("$buf buffer cells and exit 'buffered-normalized mode' again.\n");
		log("\n");
		log("    -pos\n");
		log("        Create (multi- and single-bit) $pos cells instead $buf and $_BUF_.\n");
		log("\n");
		log("    -bits\n");
		log("        Create arrays of $_BUF_ cells instead of multi-bit $buf cells.\n");
		log("\n");
		log("    -conn\n");
		log("        Create 'direct connections' instead of buffer cells.\n");
		log("\n");
		log("    -nomode\n");
		log("        Do not automatically enter or leave 'buffered-normalized mode'.\n");
		log("\n");
		log("The 'bufnorm' command can also be used to just switch in and out of\n");
		log("'buffered-normalized mode' and run the low-level re-normalizer.\n");
		log("\n");
		log("    -update\n");
		log("        Enter 'buffered-normalized mode' and (re-)normalize.\n");
		log("\n");
		log("    -reset\n");
		log("        Leave 'buffered-normalized mode' without changing the netlist.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool buf_mode = false;
		bool chain_mode = false;
		bool output_mode = false;
		bool public_mode = false;
		bool nochain_mode = false;
		bool nokeep_mode = false;
		bool nosticky_mode = false;
		bool alphasort_mode = false;
		// bool noinit_mode = false; // FIXME: Actually move init attributes
		bool nomode_mode = false;

		bool pos_mode = false;
		bool bits_mode = false;
		bool conn_mode = false;

		bool update_mode = false;
		bool reset_mode = false;
		bool got_non_update_reset_opt = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-buf") {
				buf_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-chain") {
				chain_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-output") {
				output_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-public") {
				public_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-nochain") {
				nochain_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-nokeep") {
				nokeep_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-flat") {
				nochain_mode = true;
				nokeep_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-nosticky") {
				nosticky_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-alphasort") {
				alphasort_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			// if (arg == "-noinit") {
			// 	noinit_mode = true;
			// 	got_non_update_reset_opt = true;
			// 	continue;
			// }
			if (arg == "-pos") {
				pos_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-bits") {
				bits_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-conn") {
				conn_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-nomode") {
				nomode_mode = true;
				got_non_update_reset_opt = true;
				continue;
			}
			if (arg == "-update") {
				update_mode = true;
				continue;
			}
			if (arg == "-reset") {
				reset_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (buf_mode && pos_mode)
			log_cmd_error("Options -buf and -pos are exclusive.\n");

		if (buf_mode && conn_mode)
			log_cmd_error("Options -buf and -conn are exclusive.\n");

		if (pos_mode && conn_mode)
			log_cmd_error("Options -pos and -conn are exclusive.\n");

		if (update_mode && reset_mode)
			log_cmd_error("Options -update and -reset are exclusive.\n");

		if (update_mode && got_non_update_reset_opt)
			log_cmd_error("Option -update can't be mixed with other options.\n");

		if (reset_mode && got_non_update_reset_opt)
			log_cmd_error("Option -reset can't be mixed with other options.\n");

		if (update_mode) {
			design->bufNormalize();
			return;
		}

		if (reset_mode) {
			design->bufNormalize(false);
			return;
		}

		log_header(design, "Executing BUFNORM pass (convert to buffer-normalized form).\n");

		int count_removed_buffers = 0;
		int count_updated_buffers = 0;
		int count_kept_buffers = 0;
		int count_created_buffers = 0;
		int count_updated_cellports = 0;

		if (!nomode_mode && (pos_mode || bits_mode || conn_mode)) {
			if (design->selection().full_selection)
				design->bufNormalize(false);
		}

		for (auto module : design->selected_modules())
		{
			log("Buffer-normalizing module %s.\n", log_id(module));

			SigMap sigmap(module);
			module->new_connections({});

			dict<pair<IdString, SigSpec>, Cell*> old_buffers;

			{
				vector<Cell*> old_dup_buffers;
				for (auto cell : module->cells())
				{
					if (!cell->type.in(ID($buf), ID($_BUF_)))
						continue;

					SigSpec insig = cell->getPort(ID::A);
					SigSpec outsig = cell->getPort(ID::Y);
					for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
						sigmap.add(insig[i], outsig[i]);

					pair<IdString,Wire*> key(cell->type, outsig.as_wire());
					if (old_buffers.count(key))
						old_dup_buffers.push_back(cell);
					else
						old_buffers[key] = cell;
				}
				for (auto cell : old_dup_buffers)
					module->remove(cell);
				count_removed_buffers += GetSize(old_dup_buffers);
			}

			dict<SigBit, pool<Wire*>> bit2wires;
			dict<SigSpec, pool<Wire*>> whole_wires;
			dict<SigBit, SigBit> mapped_bits;
			pool<Wire*> unmapped_wires;

			for (auto wire : module->wires())
			{
				SigSpec keysig = sigmap(wire);
				whole_wires[keysig].insert(wire);

				for (auto keybit : sigmap(wire))
					bit2wires[keybit].insert(wire);

				if (wire->port_input) {
					log("  primary input: %s\n", log_id(wire));
					for (auto bit : SigSpec(wire))
						mapped_bits[sigmap(bit)] = bit;
				} else {
					unmapped_wires.insert(wire);
				}
			}

			auto chain_this_wire_f = [&](Wire *wire)
			{
				if (chain_mode)
					return true;

				if (output_mode && wire->port_output)
					return true;

				if (public_mode && wire->name.isPublic())
					return true;

				if (!nokeep_mode && wire->get_bool_attribute(ID::keep))
					return true;

				if (!nochain_mode && wire->get_bool_attribute(ID::chain))
					return true;

				return false;
			};

			auto compare_wires_f = [&](Wire *a, Wire *b)
			{
				// Chaining wires first, then flat wires
				bool chain_a = chain_this_wire_f(a);
				bool chain_b = chain_this_wire_f(b);
				if (chain_a != chain_b) return chain_a;

				if (!alphasort_mode)
				{
					// Wires with 'chain' attribute first, high values before low values
					if (!nochain_mode) {
						int chain_a_val = a->attributes.at(ID::chain, Const(0)).as_int();
						int chain_b_val = b->attributes.at(ID::chain, Const(0)).as_int();
						if (chain_a_val != chain_b_val) return chain_a_val > chain_b_val;
					}

					// Then wires with 'keep' attribute
					if (!nokeep_mode) {
						bool keep_a = a->get_bool_attribute(ID::keep);
						bool keep_b = b->get_bool_attribute(ID::keep);
						if (keep_a != keep_b) return keep_a;
					}

					// Ports before non-ports
					if ((a->port_id != 0) != (b->port_id != 0))
						return a->port_id != 0;

					// Ports in declaration order
					if (a->port_id != b->port_id)
						return a->port_id < b->port_id;
				}

				// Nets with public names first
				if (a->name.isPublic() != b->name.isPublic())
					return a->name.isPublic();

				// Otherwise just sort by name alphanumerically
				return a->name.str() < b->name.str();
			};

			for (auto cell : module->cells())
			{
				if (cell->type.in(ID($buf), ID($_BUF_)))
					continue;

				for (auto &conn : cell->connections())
				{
					if (!cell->output(conn.first))
						continue;

					Wire *w = nullptr;

					if (!nosticky_mode && conn.second.is_wire())
						w = conn.second.as_wire();

					if (w == nullptr)
					{
						SigSpec keysig = sigmap(conn.second);
						auto it = whole_wires.find(keysig);
						if (it != whole_wires.end()) {
							it->second.sort(compare_wires_f);
							w = *(it->second.begin());
						} else {
							w = module->addWire(NEW_ID, GetSize(conn.second));
							for (int i = 0; i < GetSize(w); i++)
								sigmap.add(SigBit(w, i), keysig[i]);
						}
					}

					if (w->name.isPublic())
						log("  directly driven by cell %s port %s: %s\n",
								log_id(cell), log_id(conn.first), log_id(w));

					for (auto bit : SigSpec(w))
						mapped_bits[sigmap(bit)] = bit;
					unmapped_wires.erase(w);

					cell->setPort(conn.first, w);
				}
			}

			pool<Cell*> added_buffers;

			auto make_buffer_f = [&](const IdString &type, const SigSpec &src, const SigSpec &dst)
			{
				auto it = old_buffers.find(pair<IdString, SigSpec>(type, dst));

				if (it != old_buffers.end())
				{
					Cell *cell = it->second;
					old_buffers.erase(it);
					added_buffers.insert(cell);

					if (cell->getPort(ID::A) == src) {
						count_kept_buffers++;
					} else {
						cell->setPort(ID::A, src);
						count_updated_buffers++;
					}
					return;
				}

				Cell *cell = module->addCell(NEW_ID, type);
				added_buffers.insert(cell);

				cell->setPort(ID::A, src);
				cell->setPort(ID::Y, dst);
				cell->fixup_parameters();
				count_created_buffers++;
			};

			unmapped_wires.sort(compare_wires_f);
			for (auto wire : unmapped_wires)
			{
				bool chain_this_wire = chain_this_wire_f(wire);

				SigSpec keysig = sigmap(wire), insig = wire, outsig = wire;
				for (int i = 0; i < GetSize(insig); i++)
					insig[i] = mapped_bits.at(keysig[i], State::Sx);
				if (chain_this_wire) {
					for (int i = 0; i < GetSize(outsig); i++)
						mapped_bits[keysig[i]] = outsig[i];
				}

				log("  %s %s for %s -> %s\n",
						chain_this_wire ? "chaining" : "adding",
						conn_mode ? "connection" : "buffer",
						log_signal(insig), log_signal(outsig));

				if (conn_mode) {
					if (bits_mode) {
						for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
							module->connect(outsig[i], insig[i]);
					} else {
						module->connect(outsig, insig);
					}
				} else {
					if (bits_mode) {
						IdString celltype = pos_mode ? ID($pos) : buf_mode ? ID($buf) : ID($_BUF_);
						for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
							make_buffer_f(celltype, insig[i], outsig[i]);
					} else {
						IdString celltype = pos_mode ? ID($pos) : buf_mode ? ID($buf) :
								GetSize(outsig) == 1 ? ID($_BUF_) : ID($buf);
						make_buffer_f(celltype, insig, outsig);
					}
				}
			}

			for (auto &it : old_buffers)
				module->remove(it.second);
			count_removed_buffers += GetSize(old_buffers);

			for (auto cell : module->cells())
			{
				if (added_buffers.count(cell))
					continue;

				for (auto &conn : cell->connections())
				{
					if (cell->output(conn.first))
						continue;

					SigSpec newsig = conn.second;
					for (auto &bit : newsig)
						bit = mapped_bits[sigmap(bit)];

					if (conn.second != newsig) {
						log("  fixing input signal on cell %s port %s: %s\n",
								log_id(cell), log_id(conn.first), log_signal(newsig));
						cell->setPort(conn.first, newsig);
						count_updated_cellports++;
					}
				}
			}
		}

		log("Summary: removed %d, updated %d, kept %d, and created %d buffers, and updated %d cell ports.\n",
				count_removed_buffers, count_updated_buffers, count_kept_buffers,
				count_created_buffers, count_updated_cellports);

		if (!nomode_mode && !(pos_mode || bits_mode || conn_mode)) {
			if (design->selection().full_selection)
				design->bufNormalize(true);
		}
	}
} BufnormPass;

PRIVATE_NAMESPACE_END
