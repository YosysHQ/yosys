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

#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TribufConfig {
	bool merge_mode;
	bool logic_mode;
	bool formal_mode;
	bool propagate;
	bool force;

	TribufConfig()
	{
		merge_mode = false;
		logic_mode = false;
		formal_mode = false;
		propagate = false;
		force = false;
	}
};

struct TribufWorker {
	Module *module;
	SigMap sigmap;
	const TribufConfig &config;
	pool<SigBit> output_bits;

	TribufWorker(Module *module, const TribufConfig &config) : module(module), sigmap(module), config(config) {}

	static bool is_all_z(SigSpec sig)
	{
		for (auto bit : sig)
			if (bit != State::Sz)
				return false;
		return true;
	}

	// Sigbits that are input to mux cells or tri-state buffer cells
	dict<SigBit, pool<Cell *>> get_know_muxes()
	{
		dict<SigBit, pool<Cell *>> know_muxes;
		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID($mux), ID($_MUX_))) {
				for (auto bit : sigmap(cell->getPort(ID::A)))
					if (bit.wire != nullptr)
						know_muxes[bit].insert(cell);
				for (auto bit : sigmap(cell->getPort(ID::B)))
					if (bit.wire != nullptr)
						know_muxes[bit].insert(cell);
			}

			if (cell->type.in(ID($tribuf), ID($_TBUF_))) {
				for (auto bit : sigmap(cell->getPort(ID::A)))
					if (bit.wire != nullptr)
						know_muxes[bit].insert(cell);
			}
		}

		return know_muxes;
	}

	// all cells that drive a sigbit
	dict<SigBit, pool<Cell *>> get_driving_cells()
	{
		dict<SigBit, pool<Cell *>> driving_cells;
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second)) {
						if (bit.wire != nullptr)
							driving_cells[bit].insert(cell);
					}
				}
			}
		}
		return driving_cells;
	}

	// check if tribuf_signals is still consistent.
	void check_tribuf_signals_consistency(pool<SigBit> const &tribuf_signals)
	{
#ifndef NDEBUG
		auto const driving_cells = get_driving_cells();
		for (auto bit : tribuf_signals) {
			log_assert(sigmap(bit) == bit);

			if (driving_cells.count(bit) == 0) {
				log_error("Signal %s is in tribuf_signals, but is not in driving_cells\n", log_signal(bit));
			}
			for (auto cell : driving_cells.at(bit)) {
				if (cell->type.in(ID($tribuf), ID($_TBUF_))) {
					goto has_tribuf_driver;
				}
			}

			log("There is no tri-state buffer driving %s\n", log_signal(bit));
			for (auto cell : driving_cells.at(bit)) {
				log("  %s (%s)\n", log_id(cell->name), log_id(cell->type));
			}
			log_flush();
			log_error("There is no tri-state buffer driving %s\n", log_signal(bit));

		has_tribuf_driver:;
			// ok
		}
#endif
	}

	void run()
	{
		// SigSpecs that are outputs of tri-state buffers
		pool<SigBit> tribuf_signals;

		// find all SigBits that are output ports
		if (config.logic_mode || config.formal_mode)
			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						output_bits.insert(bit);

		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID($tribuf), ID($_TBUF_))) {
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					tribuf_signals.insert(bit);
			}

			if (cell->type.in(ID($mux), ID($_MUX_))) {
				IdString en_port = cell->type == ID($mux) ? ID::EN : ID::E;
				IdString tri_type = cell->type == ID($mux) ? ID($tribuf) : ID($_TBUF_);

				bool is_a_all_z = is_all_z(cell->getPort(ID::A));
				bool is_b_all_z = is_all_z(cell->getPort(ID::B));

				if (is_a_all_z && is_b_all_z) {
					module->remove(cell);
					continue;
				}

				if (is_a_all_z) {
					cell->setPort(ID::A, cell->getPort(ID::B));
					cell->setPort(en_port, cell->getPort(ID::S));
					cell->unsetPort(ID::B);
					cell->unsetPort(ID::S);
					cell->type = tri_type;
					for (auto bit : sigmap(cell->getPort(ID::Y)))
						tribuf_signals.insert(bit);
					module->design->scratchpad_set_bool("tribuf.added_something", true);
					continue;
				}

				if (is_b_all_z) {
					cell->setPort(en_port, module->Not(NEW_ID, cell->getPort(ID::S)));
					cell->unsetPort(ID::B);
					cell->unsetPort(ID::S);
					cell->type = tri_type;
					for (auto bit : sigmap(cell->getPort(ID::Y)))
						tribuf_signals.insert(bit);
					module->design->scratchpad_set_bool("tribuf.added_something", true);
					continue;
				}
			}
		}

		check_tribuf_signals_consistency(tribuf_signals);

		if (config.propagate) {
			// SigSpecs that are driven by tri-state buffers and still need to
			// be checked for propagation
			pool<SigBit> added_tribufs;

			for (auto &it : tribuf_signals) {
				added_tribufs.insert(it);
			}
			pool<SigBit> current_tribufs;

			while (!added_tribufs.empty()) {
				log("Propagating tri-state buffers through muxes: %d signals left.\n", int(added_tribufs.size()));
				std::swap(added_tribufs, current_tribufs);
				added_tribufs.clear();

				for (auto it : current_tribufs) {
					// PERF: this two calls are traversing the whole design, per tribuf modification. A more efficient way would
					// be to update these values as the module is modified, but doing that in a naive way is too repetitive and
					// error prone.
					auto know_muxes = get_know_muxes();
					auto driving_cells = get_driving_cells();

					check_tribuf_signals_consistency(tribuf_signals);

					if (know_muxes.count(it) == 0)
						continue;

					// check that all driving cells are tri-state buffers
					bool is_all_tribufs = true;
					for (const auto &cell : driving_cells.at(it)) {
						if (cell->type != ID($tribuf) && cell->type != ID($_TBUF_)) {
							log_debug("There is a non-tri-state buffer driving %s\n", log_signal(it));
							is_all_tribufs = false;
							break;
						}
					}
					if (!is_all_tribufs)
						continue;

					if (driving_cells.at(it).size() > 1) {
						if (config.merge_mode) {
							merge(it, driving_cells, &tribuf_signals, false, false);
							driving_cells = get_driving_cells();
							log_assert(driving_cells.at(it).size() == 1);
							check_tribuf_signals_consistency(tribuf_signals);
						} else {
							log_debug("There is more than one tri-state buffer driving %s\n", log_signal(it));
							continue;
						}
					}

					if (tribuf_signals.count(it) != 1) {
						log_warning("No tribuf for %s\n", log_signal(it));
						continue;
					}

					log_assert(driving_cells.at(it).size() == 1);
					RTLIL::Cell *tribuf = *driving_cells.at(it).begin();
					tribuf_signals.erase(it);

					IdString en1_port = tribuf->type == ID($tribuf) ? ID::EN : ID::E;

					// propagates the tribuf that drives this signal through all
					// muxes/tribufs that this signal drives
					for (auto cell : know_muxes.at(it)) {
						// only propagate trough selected cells
						if (!module->design->selected(module, cell))
							continue;

						if (cell->type == ID($mux) || cell->type == ID($_MUX_)) {
							IdString en2_port = cell->type == ID($mux) ? ID::EN : ID::E;
							IdString tri_type = cell->type == ID($mux) ? ID($tribuf) : ID($_TBUF_);

							bool is_a;
							if (sigmap(cell->getPort(ID::A)).extract(it).size() > 0) {
								// convert: $tribuf(X, E, Y) -> $mux(Y, B, S, Y2)
								//      to:                     $mux(X, B, S, Y3) -> $tribuf(Y3, E || S, Y2)
								is_a = true;
							} else if (sigmap(cell->getPort(ID::B)).extract(it).size() > 0) {
								// convert: $tribuf(X, E, Y) -> $mux(A, Y, S, Y2)
								//      to:                     $mux(A, X, S, Y3) -> $tribuf(Y3, E || ~S, Y2)
								is_a = false;
							} else {
								log_error("Mux %s is not driven by %s, but %s or %s\n", log_id(cell), log_signal(it),
									  log_signal(cell->getPort(ID::A)), log_signal(cell->getPort(ID::B)));
								continue;
							}

							auto output_y = sigmap(tribuf->getPort(ID::Y));
							auto input_y = sigmap(cell->getPort(is_a ? ID::A : ID::B));
							auto x = sigmap(tribuf->getPort(ID::A));

							// get the intersection between input and output
							auto extracted_y = output_y.extract(input_y);
							auto extracted_x = output_y.extract(input_y, &x);

							auto y2 = cell->getPort(ID::Y);
							RTLIL::SigSpec extracted_y2 = input_y.extract(extracted_y, &y2);

							RTLIL::Wire *y3 = module->addWire(NEW_ID, GetSize(extracted_y));

							if (extracted_y.size() == input_y.size()) {
								// just modify the mux
								cell->setPort(is_a ? ID::A : ID::B, extracted_x);
								cell->setPort(ID::Y, y3);

							} else {
								log_debug("splitting %s into (%s, %s) and (%s, %s)\n", log_id(cell->name),
									  log_signal(extracted_x), log_signal(extracted_y), log_signal(input_y),
									  log_signal(extracted_y2));
								// split the mux
								auto a = cell->getPort(ID::A);
								auto b = cell->getPort(ID::B);

								auto extracted_a = input_y.extract(extracted_y, &a);
								auto extracted_b = input_y.extract(extracted_y, &b);

								a.remove(extracted_a);
								b.remove(extracted_b);
								y2.remove(extracted_y2);

								cell->setPort(ID::A, a);
								cell->setPort(ID::B, b);
								cell->setPort(ID::Y, y2);
								cell->setParam(ID::WIDTH, GetSize(extracted_y));

								module->addMux(NEW_ID, is_a ? extracted_x : extracted_a,
									       is_a ? extracted_b : extracted_x, cell->getPort(ID::S), y3);
							}
							RTLIL::SigSpec or_y;
							if (!is_a) {
								or_y = module->Or(NEW_ID, tribuf->getPort(en1_port),
										  module->Not(NEW_ID, cell->getPort(ID::S)));
							} else {
								or_y = module->Or(NEW_ID, tribuf->getPort(en1_port), cell->getPort(ID::S));
							}
							module->addTribuf(NEW_ID, y3, or_y, extracted_y2);

							for (auto bit : sigmap(extracted_y2)) {
								tribuf_signals.insert(bit);
								added_tribufs.insert(bit);
							}
						}
						if (cell->type == ID($tribuf) || cell->type == ID($_TBUF_)) {
							// convert: $tribuf(A, E1, Y) -> $tribuf(Y, E2, Y2)
							//      to:                      $tribuf(A, E1 && E2, Y2)
							IdString en2_port = cell->type == ID($tribuf) ? ID::EN : ID::E;

							auto output = sigmap(tribuf->getPort(ID::Y));
							auto input = sigmap(cell->getPort(ID::A));

							// get only the input signals that are driven by the tribuf
							auto extracted_y = input.extract(output);

							log_debug("extracted %s from %s and %s\n", log_signal(extracted_y), log_signal(output),
								  log_signal(input));
							log_assert(extracted_y.size() > 0);

							auto extracted_a = output.extract(input, &tribuf->getPort(ID::A));
							if (extracted_y == input) {
								log_assert(extracted_a.size() == extracted_y.size());

								// just replace the second tribuf
								cell->setPort(ID::A, extracted_a);
								cell->setPort(
								  en2_port, module->And(NEW_ID, tribuf->getPort(en1_port), cell->getPort(en2_port)));
							} else {
								// split the second tribuf. A new tribuf cell will be created, with the signals
								// extracted from `cell`.
								auto a2 = cell->getPort(ID::A);
								auto y2 = cell->getPort(ID::Y);

								auto extracted_a2 = input.extract(extracted_y, &a2);
								auto extracted_y2 = input.extract(extracted_y, &y2);

								a2.remove(extracted_a2);
								y2.remove(extracted_y2);

								log_debug("splitting %s into (%s, %s) and (%s, %s)\n", log_id(cell->name),
									  log_signal(a2), log_signal(y2), log_signal(extracted_a2),
									  log_signal(extracted_y2));

								cell->setPort(ID::A, a2);
								cell->setPort(ID::Y, y2);
								cell->setParam(ID::WIDTH, GetSize(a2));

								module->addTribuf(
								  NEW_ID, extracted_y,
								  module->And(NEW_ID, tribuf->getPort(en1_port), cell->getPort(en2_port)),
								  extracted_y2);

								for (auto bit : sigmap(extracted_y2)) {
									tribuf_signals.insert(bit);
									added_tribufs.insert(bit);
								}
							}
						}
					}
				}
			}
		}

		check_tribuf_signals_consistency(tribuf_signals);

		if (config.merge_mode || config.logic_mode || config.formal_mode) {
			for (auto it : tribuf_signals) {
				auto const driving_cells = get_driving_cells();

				if (driving_cells.count(it) == 0) {
					// already merged it with some previous one
					continue;
				}

				auto drivers = driving_cells.at(it);

				// if there is only one driver, we don't need to merge it
				if (!config.logic_mode && !config.formal_mode && GetSize(drivers) <= 1) {
					tribuf_signals.erase(it);
					continue;
				}

				// check that all driving cells are tri-state buffers
				for (const auto &cell : drivers) {
					if (cell->type != ID($tribuf) && cell->type != ID($_TBUF_)) {
						log_warning("There is a non-tri-state buffer driving %s\n", log_signal(it));
						tribuf_signals.erase(it);
						goto skip_signal;
					}
				}
				merge(it, driving_cells, nullptr, config.logic_mode, config.formal_mode);
			skip_signal:;
			}
		}
	}

	void merge(RTLIL::SigBit sig, dict<SigBit, pool<Cell *>> const &driving_cells, pool<SigBit> *tribuf_signals, bool logic_mode,
		   bool formal_mode)
	{
		// sigmap.set(module);
		bool no_tribuf = false;

		if (logic_mode && !formal_mode) {
			no_tribuf = true;
			if (!config.force && output_bits.count(sig))
				no_tribuf = false;
		}

		if (formal_mode)
			no_tribuf = true;

		pool<Cell *> cells = driving_cells.at(sig);

		if (GetSize(cells) <= 1 && !no_tribuf)
			return;

		// check if all driving cells are tri-state buffers
		for (const auto &cell : cells) {
			if (cell->type != ID($tribuf) && cell->type != ID($_TBUF_)) {
				log("There is a non-tri-state buffer driving %s\n", log_signal(sig));
				return;
			}
		}

		// find all signals that the driving cells of this signal are also driving
		pool<SigBit> siblings;
		for (const auto &cell : cells) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			for (auto bit : y) {
				siblings.insert(bit);
			}
		}

		// find all cells driving one of the siblings signals
		pool<Cell *> drivers;
		for (const auto bit : siblings) {
			pool<Cell *> this_cells = driving_cells.at(bit);
			for (auto cell : this_cells)
				if (cell->type != ID($tribuf) && cell->type != ID($_TBUF_)) {
					log("There is a non-tri-state buffer driving %s\n", log_signal(bit));
					return;
				}
			drivers.insert(this_cells.begin(), this_cells.end());
		}

		// partition the cells by the enabled signal. If they share the enabled signal, they can be merged.
		dict<SigBit, pool<Cell *>> partitions;
		for (const auto cell : drivers) {
			IdString en_port = cell->type == ID($tribuf) ? ID::EN : ID::E;
			SigSpec e = sigmap(cell->getPort(en_port));
			partitions[e.as_bit()].insert(cell);
		}

		// get the partitions that driven this sigbit
		pool<SigBit> en_driving_this;
		for (auto &pair : partitions) {
			for (auto cell : cells) {
				if (pair.second.count(cell) > 0) {
					en_driving_this.insert(pair.first);
					break;
				}
			}
		}

		// considering the set of sigbits drived by each partition, find the set-intersection of them.
		dict<SigBit, pool<SigBit>> partitions_sigbits;
		for (auto sigbit : en_driving_this) {
			pool<Cell *> this_cells = partitions.at(sigbit);
			pool<SigBit> bits;
			for (auto cell : this_cells) {
				SigSpec e = sigmap(cell->getPort(ID::Y));
				bits.insert(e.begin(), e.end());
			}
			partitions_sigbits[sigbit] = bits;
		}

		pool<SigBit> intersection;
		for (SigBit bit : siblings) {
			bool has_in_all = true;
			for (auto &pair : partitions_sigbits) {
				if (pair.second.count(bit) == 0) {
					has_in_all = false;
					break;
				}
			}
			if (has_in_all)
				intersection.insert(bit);
		}
		SigSpec intersection_sig(intersection);

		// now, for each tribuf, split them, or merge them, depending on the intersection
		cells.clear();
		for (auto en : en_driving_this) {
			pool<Cell *> to_be_merged;
			for (auto cell : partitions.at(en)) {
				std::vector<int> matching_sigbits;
				SigSpec output = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(output); i++) {
					if (intersection.count(output[i]) > 0) {
						matching_sigbits.push_back(i);
					}
				}
				if ((int)matching_sigbits.size() == output.size() && matching_sigbits.size() == intersection.size()) {
					// all bits of the tribuf matched, so we don't need to split or merge it.
					to_be_merged.insert(cell);
				} else if ((int)matching_sigbits.size() == output.size()) {
					// all bits of the tribuf matched, so we don't need to split it.
					to_be_merged.insert(cell);
				} else if (matching_sigbits.size() == 0) {
					log_error("No matching bits?!\n");
				} else {
					// some of the bits matched, so we need to split the tribuf in two, one with matching bits and another with
					// the non-matching ones. The matching tribuf will be merged with other cells in this partition.
					SigSpec extracted_a;
					SigSpec extracted_y;
					SigSpec port_a = cell->getPort(ID::A);
					SigSpec port_y = cell->getPort(ID::Y);
					for (int i = GetSize(port_a) - 1; i >= 0; i--) {
						if (matching_sigbits[matching_sigbits.size() - 1] == i) {
							extracted_a.append(port_a.extract(i));
							extracted_y.append(port_y.extract(i));
							port_a.remove(i);
							port_y.remove(i);
							matching_sigbits.pop_back();
							if (matching_sigbits.size() == 0)
								break;
						}
					}

					log_assert(!port_a.empty() && !port_y.empty() && !extracted_y.empty() && !extracted_a.empty());
					log_assert(cell->type.in(ID($tribuf), ID($_TBUF_)));

					cell->setPort(ID::A, port_a);
					cell->setPort(ID::Y, port_y);
					cell->setParam(ID::WIDTH, GetSize(port_a));

					RTLIL::Cell *new_tribuf = module->addTribuf(NEW_ID, extracted_a, en, extracted_y);
					to_be_merged.insert(new_tribuf);
				}
			}
			SigSpec merged_a;
			SigSpec merged_y;
			for (auto cell : to_be_merged) {
				merged_a.append(cell->getPort(ID::A));
				merged_y.append(cell->getPort(ID::Y));
				if (tribuf_signals) {
					if (cell->type.in(ID($tribuf), ID($_TBUF_)))
						for (auto bit : sigmap(cell->getPort(ID::Y)))
							tribuf_signals->erase(bit);
				}
				module->remove(cell);
			}

			RTLIL::Cell *new_tribuf = module->addTribuf(NEW_ID, merged_a, en, merged_y);
			cells.insert(new_tribuf);
			if (tribuf_signals) {
				for (auto bit : sigmap(merged_y))
					tribuf_signals->insert(bit);
			}
		}

		if (formal_mode && GetSize(cells) >= 2) {
			for (auto cell : cells) {
				SigSpec others_s;

				for (auto other_cell : cells) {
					if (other_cell == cell)
						continue;
					else if (other_cell->type == ID($tribuf))
						others_s.append(other_cell->getPort(ID::EN));
					else
						others_s.append(other_cell->getPort(ID::E));
				}

				auto cell_s = cell->type == ID($tribuf) ? cell->getPort(ID::EN) : cell->getPort(ID::E);

				auto other_s = module->ReduceOr(NEW_ID, others_s);

				auto conflict = module->And(NEW_ID, cell_s, other_s);

				std::string name = stringf("$tribuf_conflict$%s", log_id(cell->name));
				auto assert_cell = module->addAssert(name, module->Not(NEW_ID, conflict), SigSpec(true));

				assert_cell->set_src_attribute(cell->get_src_attribute());
				assert_cell->set_bool_attribute(ID::keep);

				module->design->scratchpad_set_bool("tribuf.added_something", true);
			}
		}

		SigSpec pmux_b, pmux_s;
		for (auto cell : cells) {
			if (cell->type == ID($tribuf))
				pmux_s.append(cell->getPort(ID::EN));
			else
				pmux_s.append(cell->getPort(ID::E));
			pmux_b.append(cell->getPort(ID::A));

			if (tribuf_signals) {
				if (cell->type.in(ID($tribuf), ID($_TBUF_)))
					for (auto bit : sigmap(cell->getPort(ID::Y)))
						tribuf_signals->erase(bit);
			}
			module->remove(cell);
		}
		cells.clear();

		SigSpec muxout;
		if (GetSize(pmux_s) > 1) {
			muxout = module->Pmux(NEW_ID, SigSpec(State::Sx, GetSize(intersection_sig)), pmux_b, pmux_s);
		} else {
			muxout = pmux_b;
		};

		if (no_tribuf) {
			module->connect(intersection_sig, muxout);
		} else {
			module->addTribuf(NEW_ID, muxout, module->ReduceOr(NEW_ID, pmux_s), intersection_sig);
			if (tribuf_signals) {
				for (auto bit : sigmap(intersection_sig))
					tribuf_signals->insert(bit);
			}
			module->design->scratchpad_set_bool("tribuf.added_something", true);
		}
	}
};

struct TribufPass : public Pass {
	TribufPass() : Pass("tribuf", "infer tri-state buffers") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    tribuf [options] [selection]\n");
		log("\n");
		log("This pass transforms $mux cells with 'z' inputs to tristate buffers.\n");
		log("\n");
		log("    -merge\n");
		log("        merge multiple tri-state buffers driving the same net\n");
		log("        into a single buffer.\n");
		log("\n");
		log("    -logic\n");
		log("        convert tri-state buffers that do not drive output ports\n");
		log("        to non-tristate logic. this option implies -merge.\n");
		log("\n");
		log("    -formal\n");
		log("        convert all tri-state buffers to non-tristate logic and\n");
		log("        add a formal assertion that no two buffers are driving the\n");
		log("        same net simultaneously. this option implies -merge.\n");
		log("\n");
		log("    -propagate\n");
		log("        propagate the tribuffer through mux cells. Basically converts\n");
		log("        `x ? (y ? a : 1'bz) : b` into `y || ~x ? (x ? a : b) : 1'bz`,\n");
		log("        etc. this option implies -merge\n");
		log("\n");
		log("    -force\n");
		log("        convert tri-state buffers to non-tristate logic, even if\n");
		log("        they are output ports. this option depends on -logic or -formal.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		TribufConfig config;

		log_header(design, "Executing TRIBUF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-merge") {
				config.merge_mode = true;
				continue;
			}
			if (args[argidx] == "-logic") {
				config.logic_mode = true;
				continue;
			}
			if (args[argidx] == "-formal") {
				config.formal_mode = true;
				continue;
			}
			if (args[argidx] == "-propagate") {
				config.propagate = true;
				config.merge_mode = true;
				continue;
			}
			if (args[argidx] == "-force") {
				config.force = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			TribufWorker worker(module, config);
			worker.run();
		}
	}
} TribufPass;

PRIVATE_NAMESPACE_END
