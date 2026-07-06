/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Silimate Inc.
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

#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <algorithm>
#include <map>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Strip a leading RTLIL "\" escape from an IdString's text.
static std::string unescape(const std::string &s) { return (!s.empty() && s[0] == '\\') ? s.substr(1) : s; }

// A buffer/inverter has exactly one input and one output pin (a 2-port cell). Synthesis
// only ever inserts such pass-throughs (drive-strength buffers/inverters) on the single
// net between a train top port and its surrounding flop, so hopping over them reaches the
// real boundary flop regardless of how many were added; any flop/gate has >2 ports.
static bool is_passthrough(Cell *cell)
{
	int n_in = 0, n_out = 0;
	for (auto &conn : cell->connections()) {
		if (cell->input(conn.first)) {
			if (++n_in > 1)
				return false;
		} else if (cell->output(conn.first)) {
			if (++n_out > 1)
				return false;
		}
	}
	return n_in == 1 && n_out == 1;
}

// True if a port's trailing "_<pin>" segment names a clock (clk/clock, case-insensitive),
// so shared/per-cell clock ports aren't treated as data inputs.
static bool is_clock_pin(const std::string &pin)
{
	std::string p;
	for (char c : pin)
		p += std::tolower((unsigned char)c);
	return p.find("clk") != std::string::npos || p.find("clock") != std::string::npos;
}

// True if a flop input pin is an (a)synchronous set/reset/clear/preset/load control pin
// (case-insensitive). Such pins are not the data (D) input, so they must be skipped when
// finding the captured-data pin: an async set/reset flop (e.g. ASYNC_DFFHx1 with pins
// D/RESET/SET/CLK, used by adff_surround) would otherwise let a RESET/SET net (the shared
// arst) be mistaken for the data pin, tying the carved cell's output to arst.
static bool is_set_reset_pin(const std::string &pin)
{
	std::string p;
	for (char c : pin)
		p += std::tolower((unsigned char)c);
	for (const char *k : {"reset", "set", "clr", "clear", "arst", "srst", "aload", "sload"})
		if (p.find(k) != std::string::npos)
			return true;
	return false;
}

// Map a carved cell's port-base name to the Preqorsor dataset naming convention: carved
// cells come in as slow_<enc>/fast_<enc> and OpenIP designs as slow_design_<enc>/
// fast_design_<enc>, but downstream parsing/decryption expects <enc> and design_<speed>_
// <enc>. The design_ rewrites run first so "slow_"/"fast_" can't clip them.
static std::string pq_rename(const std::string &base)
{
	if (base.rfind("slow_design_", 0) == 0)
		return "design_slow_" + base.substr(12);
	if (base.rfind("fast_design_", 0) == 0)
		return "design_fast_" + base.substr(12);
	if (base.rfind("slow_", 0) == 0)
		return base.substr(5);
	if (base.rfind("fast_", 0) == 0)
		return base.substr(5);
	return base;
}

struct BoundaryRec {
	std::string speed, driving_cell, driving_pin, load_cell, load_pin;
};

struct CarveNetlistPass : public Pass {
	CarveNetlistPass()
	    : Pass("carvenetlist", "carve surround-with-flops cells into per-cell modules and record their flop boundary")
	{
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    carvenetlist\n");
		log("\n");
		log("Carve each surround-with-flops cell-under-test out of the flat 'train' module into\n");
		log("its own flop-free module and record the surrounding flops as that cell's boundary\n");
		log("conditions.\n");
		log("\n");
		log("The training netlist is one giant flat module (\"train\") of independent\n");
		log("cells-under-test, each surrounded by flip-flops (see ml.dataset.surround_with_flops):\n");
		log("every data input is driven by a launch flop's Q and every data output is captured\n");
		log("by a load flop's D, with two shared clocks (fast_clk/slow_clk). This pass carves\n");
		log("each cell-under-test out into its own flop-free module (named after the dataset\n");
		log("cell) and records the surrounding flops as \\pq_* string attributes on the carved\n");
		log("module (\\pq_speed, \\pq_driving_cell, \\pq_driving_pin, \\pq_load_cell,\n");
		log("\\pq_load_pin), so OpenSTA can re-impose them (set_driving_cell on the inputs,\n");
		log("set_load resolved from the load flop's data pin on the outputs).\n");
		log("\n");
		log("Anchored on the train top-level ports (the only structure guaranteed to survive\n");
		log("synthesis), grouped by cell base name \"<base>_<pin>\":\n");
		log("\n");
		log("  - launch flop  = hop forward from each data input port through any\n");
		log("                   drive-strength buffers/inverters (1-in/1-out cells) to the\n");
		log("                   first >2-port cell;\n");
		log("  - capture flop = the mirror backward hop from each data output port;\n");
		log("  - cell-under-test = the logic cone walked forward from the launch flops'\n");
		log("                      outputs, excluding the boundary flops; tagged \\submod and\n");
		log("                      carved by submod.\n");
		log("\n");
		log("The shared clock network (fast_clk/slow_clk and their buffer tree) is treated as\n");
		log("a hard boundary: cones never expand through it, so a carve can't leak across the\n");
		log("clock into another cell's surrounding flops.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing CARVENETLIST pass (carve surround-with-flops cells into "
				   "per-cell modules and record their flop boundary).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		Module *train = design->module(ID(train));
		if (train == nullptr) {
			log_warning("No 'train' module found; nothing to carve.\n");
			return;
		}

		// Marks the zero-area $_BUF_ cells we insert at the capture-flop boundary (below) so
		// they can be turned back into plain assigns after carving.
		const IdString PQ_PASS = RTLIL::escape_id("pq_passthrough");

		// Marks the reconstructed per-pin output bus wire ("__pqcarve.<base>_<pin>") so the
		// port-name cleanup can tell it apart from a colliding stale "__pqo" cone-output
		// fragment (which must be demoted to an internal net, not aliased onto the output).
		const IdString PQ_CARVE_OUT = RTLIL::escape_id("pq_carve_out");

		SigMap sigmap(train);

		// Re-root *only* fused feed-through net groups toward their launch-side (input) net.
		// A feed-through output bit (Y[i] = some input) lets synthesis fuse the launch-flop
		// input net ("..._<pin>__pqi[j]") and the capture-flop output net
		// ("..._<pin>__pqo[i]") into one SigMap group. Whichever bit SigMap happens to elect
		// as the group rep is the net the carve reads and reconstructs from; if it elects the
		// "__pqo" output fragment, that fragment is only *driven* by the launch flop (a
		// boundary cell carved away), so the cone reads it but nothing drives it -> floating
		// bit + inout output bus. Promote the "__pqi" bit, but ONLY for groups that also hold
		// a "__pqo" bit (true feed-throughs). Promoting every "__pqi" net would re-root the
		// rep of ordinary input groups too, churning internal net names across nearly every
		// carved cell (and needlessly invalidating their cached power VCDs).
		{
			dict<SigBit, SigBit> pqi_bit_of_group; // group rep -> a "__pqi" bit in that group
			pool<SigBit> groups_with_pqo;          // group reps that contain a "__pqo" bit
			for (auto wire : train->wires()) {
				std::string nm = unescape(wire->name.str());
				bool is_pqi = nm.find("__pqi") != std::string::npos;
				bool is_pqo = nm.find("__pqo") != std::string::npos;
				if (!is_pqi && !is_pqo)
					continue;
				for (auto bit : SigSpec(wire)) {
					SigBit r = sigmap(bit);
					if (r.wire == nullptr)
						continue;
					if (is_pqi && !pqi_bit_of_group.count(r))
						pqi_bit_of_group[r] = bit;
					if (is_pqo)
						groups_with_pqo.insert(r);
				}
			}
			for (auto &it : pqi_bit_of_group)
				if (groups_with_pqo.count(it.first))
					sigmap.add(it.second);
		}

		// Instance-level driver/load maps over canonicalized nets. Keyed by net bit so the
		// surrounding flops can be found by topology and excluded from the carve.
		dict<SigBit, std::pair<Cell *, IdString>> driver;             // net -> (cell, out pin)
		dict<SigBit, std::vector<std::pair<Cell *, IdString>>> loads; // net -> [(cell, in pin)]
		dict<Cell *, std::vector<SigBit>> cell_out_bits, cell_in_bits;
		for (auto cell : train->cells()) {
			for (auto &conn : cell->connections()) {
				bool is_out = cell->output(conn.first);
				bool is_in = cell->input(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr)
						continue; // skip constants
					if (is_out) {
						driver[bit] = {cell, conn.first};
						cell_out_bits[cell].push_back(bit);
					}
					if (is_in) {
						loads[bit].push_back({cell, conn.first});
						cell_in_bits[cell].push_back(bit);
					}
				}
			}
		}

		// Identify the shared clock distribution network. Every cell-under-test is driven
		// by the same two top-level clocks (fast_clk/slow_clk, named so by
		// ml.dataset.surround_with_flops), so the clock tree is the one net set that
		// connects otherwise-independent cells: its leaf nets fan out to the CLK pin of
		// every flop across every cell/design. Seed from the clock top ports and propagate
		// forward only through pass-through clock buffers (stopping at flops). Excluding
		// these nets from the cone below keeps each carve bounded by data connectivity
		// alone, so it can never leak across the shared clock into a neighbor's flops.
		pool<SigBit> clk_nets;
		{
			std::vector<SigBit> wl;
			for (auto wire : train->wires()) {
				if (!wire->port_input && !wire->port_output)
					continue;
				std::string name = unescape(wire->name.str());
				auto us = name.rfind('_');
				std::string pin = (us == std::string::npos) ? name : name.substr(us + 1);
				if (!is_clock_pin(pin))
					continue;
				for (auto bit : sigmap(SigSpec(wire)))
					if (bit.wire)
						wl.push_back(bit);
			}
			while (!wl.empty()) {
				SigBit b = wl.back();
				wl.pop_back();
				if (clk_nets.count(b))
					continue;
				clk_nets.insert(b);
				auto it = loads.find(b);
				if (it == loads.end())
					continue;
				for (auto &pr : it->second) {
					if (!is_passthrough(pr.first))
						continue; // stop at flops; only follow clock buffers
					for (auto ob : cell_out_bits[pr.first])
						wl.push_back(ob);
				}
			}
		}

		// Group top-level data ports by cell base name (skip clock ports). out_wires keeps the
		// actual output port wires (not just their sigmapped bits) so the carved output bus
		// can be rebuilt one clean port per pin at the capture-flop boundary below.
		struct Group {
			std::vector<SigBit> ins, outs;
			std::vector<Wire *> in_wires, out_wires;
		};
		std::map<std::string, Group> groups;
		for (auto wire : train->wires()) {
			if (!wire->port_input && !wire->port_output)
				continue;
			std::string name = unescape(wire->name.str());
			auto us = name.rfind('_');
			if (us == std::string::npos || us == 0)
				continue;
			std::string pin = name.substr(us + 1);
			std::string base = name.substr(0, us);
			if (base.empty() || is_clock_pin(pin))
				continue;
			Group &g = groups[base];
			if (wire->port_output)
				g.out_wires.push_back(wire);
			else
				g.in_wires.push_back(wire);
			for (auto bit : sigmap(SigSpec(wire))) {
				if (bit.wire == nullptr)
					continue;
				if (wire->port_input)
					g.ins.push_back(bit);
				else
					g.outs.push_back(bit);
			}
		}

		// Forward-hop from an input-port net through buffers to the launch flop (or null)
		auto hop_fwd = [&](SigBit bit) -> Cell * {
			pool<Cell *> seen;
			while (true) {
				if (clk_nets.count(bit))
					return nullptr; // never walk into the shared clock network
				auto it = loads.find(bit);
				if (it == loads.end())
					return nullptr;
				Cell *c = nullptr;
				for (auto &pr : it->second) {
					if (c && pr.first != c)
						return nullptr; // fork: no clean single boundary
					c = pr.first;
				}
				if (c == nullptr || seen.count(c))
					return nullptr;
				seen.insert(c);
				if (!is_passthrough(c))
					return c;
				auto &outs = cell_out_bits[c];
				if (outs.size() != 1)
					return nullptr;
				bit = outs[0];
			}
		};
		// Backward-hop from an output-port net through buffers to the capture flop (or null)
		auto hop_back = [&](SigBit bit) -> Cell * {
			pool<Cell *> seen;
			while (true) {
				if (clk_nets.count(bit))
					return nullptr; // never walk into the shared clock network
				auto it = driver.find(bit);
				if (it == driver.end())
					return nullptr;
				Cell *c = it->second.first;
				if (seen.count(c))
					return nullptr;
				seen.insert(c);
				if (!is_passthrough(c))
					return c;
				auto &ins = cell_in_bits[c];
				if (ins.size() != 1)
					return nullptr;
				bit = ins[0];
			}
		};

		std::map<std::string, BoundaryRec> boundary;
		std::map<std::string, std::string> final_of_base; // carved module name -> the base it came from
		int tagged_total = 0;
		for (auto &grp : groups) {
			const std::string &base = grp.first;
			Group &g = grp.second;

			// Launch flops drive the inputs; hop through buffers, seed the cone from the
			// flop output that drives the cell, and record (type, out-pin) as the driver.
			pool<Cell *> launch, capture, boundary_cells;
			pool<SigBit> seed;
			std::string drv_cell, drv_pin;
			for (auto bit : g.ins) {
				Cell *flop = hop_fwd(bit);
				if (flop == nullptr)
					continue;
				launch.insert(flop);
				for (auto ob : cell_out_bits[flop]) {
					if (clk_nets.count(ob))
						continue; // a launch flop's data output, never a generated clock
					if (!loads.count(ob))
						continue; // only the flop output that actually drives the cell
					if (drv_cell.empty()) {
						drv_cell = unescape(flop->type.str());
						drv_pin = unescape(driver[ob].second.str());
					}
					seed.insert(ob);
				}
			}
			// Capture flops load the outputs; hop back through buffers to the real flop.
			for (auto bit : g.outs) {
				Cell *flop = hop_back(bit);
				if (flop != nullptr)
					capture.insert(flop);
			}
			boundary_cells = launch;
			for (auto c : capture)
				boundary_cells.insert(c);

			// Walk the logic cone forward from the launch outputs, excluding boundary flops
			pool<Cell *> logic;
			pool<SigBit> driven = seed;
			std::vector<SigBit> stack(seed.begin(), seed.end());
			while (!stack.empty()) {
				SigBit k = stack.back();
				stack.pop_back();
				if (clk_nets.count(k))
					continue; // hard boundary: never expand through the shared clock tree
				auto it = loads.find(k);
				if (it == loads.end())
					continue;
				for (auto &pr : it->second) {
					Cell *c = pr.first;
					if (boundary_cells.count(c) || logic.count(c))
						continue;
					logic.insert(c);
					for (auto ob : cell_out_bits[c]) {
						if (clk_nets.count(ob))
							continue; // don't follow a cell's generated/forwarded clock
						driven.insert(ob);
						stack.push_back(ob);
					}
				}
			}

			// Redirect cone-cell inputs that physically read a fused feed-through "__pqo"
			// fragment to that group's launch-side rep (an input net, after the promotion
			// above). The "__pqo" fragment is driven only by the launch flop, which is carved
			// away as a boundary cell, so a cone cell left wired to it would read a floating
			// net. Restrict the rewrite to bits whose wire is "__pqo"-named so ordinary cone
			// reads keep their original net (no cosmetic net-name churn across cells).
			for (auto c : logic) {
				dict<IdString, SigSpec> rewire;
				for (auto &conn : c->connections()) {
					if (!c->input(conn.first))
						continue;
					SigSpec cs = conn.second;
					bool changed = false;
					for (auto &bit : cs) {
						if (bit.wire == nullptr ||
						    unescape(bit.wire->name.str()).find("__pqo") == std::string::npos)
							continue;
						SigBit r = sigmap(bit);
						if (r != bit) {
							bit = r;
							changed = true;
						}
					}
					if (changed)
						rewire[conn.first] = cs;
				}
				for (auto &r : rewire)
					c->setPort(r.first, r.second);
			}

			// Tag the cell logic for submod.
			std::string final = pq_rename(base);
			// pq_rename strips the "slow_"/"fast_" speed prefix off plain cells, so a train
			// holding both "slow_<enc>" and "fast_<enc>" would map both to "<enc>" -- carving
			// two different cells into one module and silently overwriting the first cell's
			// \pq_* boundary record with the second. Refuse rather than emit a wrong netlist.
			if (final_of_base.count(final))
				log_error("carvenetlist: cell groups '%s' and '%s' both map to carved module "
					  "name '%s'; cannot carve two cells into one module.\n",
					  final_of_base.at(final).c_str(), base.c_str(), final.c_str());
			final_of_base[final] = base;
			for (auto c : logic)
				c->set_string_attribute(RTLIL::escape_id("submod"), final);
			tagged_total += GetSize(logic);

			// A DESIGN cell-under-test (slow_design_/fast_design_) is a whole sequential design,
			// not a single mapped cell; flag it so the self-containment pass below also rebuilds
			// its launch-flop input boundary (step (1)), which a single-cell carve never needs.
			bool is_design = base.rfind("slow_design_", 0) == 0 || base.rfind("fast_design_", 0) == 0;

			// Speed comes from the pre-rename base's "<speed>_" prefix ("fast_" covers both
			// "fast_<enc>" and "fast_design_<enc>"). The post-rename `final` can't be used:
			// pq_rename strips the speed prefix off plain cells, so `final` carries no speed.
			std::string speed = base.rfind("fast_", 0) == 0 ? "fast" : "slow";

			// Rebuild the output boundary at the capture flops. submod can only export a
			// clean output port for a net driven *inside* the carve and read *outside* it.
			// After synthesis the bit a capture flop captures often is not such a net: a
			// degenerate cell (shifter/mod/div in const or var mode) collapses an output into
			// a bare copy of an input (Y=A -- the flop reads the launch-flop net directly), a
			// routed input bit, or a constant driven by an abc-mapped tie cell the forward
			// cone walk can never reach. Left alone that output bit has no in-cone driver and
			// drags its whole bus to inout, or the port vanishes. So, per output-port pin,
			// build one fresh bus `cw` driven by a per-bit tagged $_BUF_ copying whatever the
			// capture flop reads, then rewire the flop to read `cw`. The buffer's source sets
			// the input side: an in-cone net stays internal, a launch-flop/boundary net
			// becomes a clean input port, a constant stays constant, and an otherwise
			// unreachable source cell (a tie) is cloned into the cell so its (tiny) power is
			// characterized rather than stranded in the deleted train module. The carve wire
			// is named "__pqcarve.<base>_<pin>" so the trailing port cleanup (which drops the
			// scope-dot prefix) recovers the clean "<base>_<pin>" port name.
			std::string load_cell, load_pin;
			for (auto pw : g.out_wires) {
				Wire *cw = train->addWire(
				    RTLIL::escape_id("__pqcarve." + unescape(pw->name.str())), pw->width);
				cw->set_bool_attribute(PQ_CARVE_OUT);
				for (int i = 0; i < pw->width; i++) {
					Cell *fc = hop_back(sigmap(SigBit(pw, i)));
					if (fc == nullptr || !capture.count(fc))
						continue;
					// Locate the flop's data pin (the lone input that is neither a clock nor a
					// set/reset/clear control pin -- an async set/reset flop like ASYNC_DFFHx1
					// also exposes RESET/SET inputs that must not be mistaken for D).
					IdString dpin;
					int dpos = -1;
					SigBit draw;
					for (auto &conn : fc->connections()) {
						if (!fc->input(conn.first) || is_clock_pin(unescape(conn.first.str())) ||
						    is_set_reset_pin(unescape(conn.first.str())))
							continue;
						const SigSpec &s = conn.second;
						for (int j = 0; j < GetSize(s); j++) {
							if (clk_nets.count(sigmap(s[j])))
								continue;
							dpin = conn.first, dpos = j, draw = s[j];
							break;
						}
						if (dpos >= 0)
							break;
					}
					if (dpos < 0)
						continue;
					if (load_cell.empty()) {
						load_cell = unescape(fc->type.str());
						load_pin = unescape(dpin.str());
					}
					// Pick the buffer's source: clone an otherwise-unreachable constant/source
					// cell (e.g. a tie) into the cell so the output bit gains an in-cone
					// driver; otherwise copy the net the flop reads as-is.
					SigBit src = sigmap(draw);
					if (src.wire != nullptr) {
						auto dit = driver.find(src);
						if (dit != driver.end()) {
							Cell *dc = dit->second.first;
							IdString opin = dit->second.second;
							bool is_source = !cell_in_bits.count(dc) || cell_in_bits.at(dc).empty();
							// A genuine constant source (a tie): 0 data inputs, single-bit
							// output, unreachable by the forward cone. Clone it into the cell
							// (rather than steal the shared original) so the output bit gets an
							// in-cone driver and the tie's power is characterized.
							if (is_source && GetSize(dc->getPort(opin)) == 1 &&
							    !logic.count(dc) && !boundary_cells.count(dc)) {
								Cell *clone = train->addCell(NEW_ID, dc->type);
								clone->parameters = dc->parameters;
								// Copy every port (e.g. a $lut's zero-width A pin must exist for
								// the cell to pass check) before redirecting the output to a
								// fresh net.
								for (auto &cc : dc->connections())
									clone->setPort(cc.first, cc.second);
								Wire *tn = train->addWire(NEW_ID, 1);
								clone->setPort(opin, SigSpec(tn));
								clone->set_string_attribute(RTLIL::escape_id("submod"), final);
								src = SigBit(tn);
							}
						}
					}
					Cell *buf = train->addBufGate(NEW_ID, src, SigBit(cw, i));
					buf->set_string_attribute(RTLIL::escape_id("submod"), final);
					buf->set_string_attribute(PQ_PASS, "1");
					// Keep the $_BUF_ alive through submod's internal clean (it would
					// otherwise re-alias Y to A, re-merging the boundary); converted to a
					// plain assign after the carve.
					buf->set_bool_attribute(ID::keep);
					std::vector<SigBit> dbits = fc->getPort(dpin).bits();
					dbits[dpos] = SigBit(cw, i);
					fc->setPort(dpin, SigSpec(dbits));
				}
			}

			// Self-containment repair, in two parts. A single mapped cell's cone is seeded from
			// its launch-flop inputs and needs only part (2); a DESIGN cell-under-test
			// (slow_design_<enc>/fast_design_<enc>) is a whole sequential design and also needs
			// part (1). Left unrepaired, either leaks bogus top-level *input* ports out of the
			// carved module (internal flattened nets, constants, clock-gate scan pins, undriven
			// opt artifacts, ...), which both mis-drives the gate-level power testbench and escapes
			// char.sdc's "slow_*"/"fast_*" data-port matching.
			//   (1) Primary-input naming: after flatten the launch-flop output net (the carve's
			//       data input) can keep an internal flattened name ("u0_key", "n_1598636") that
			//       won SigMap election over the "<base>_<pin>__pqi" boundary name. Per input pin,
			//       build a fresh "__pqcarve.<base>_<pin>" bus, copy the launch-flop output into it
			//       with a train-side (boundary) buffer, and rewire the cone to read it, so submod
			//       exports the input under the clean "<base>_<pin>" name. A whole design renames
			//       every input; a plain cell's boundary usually survives clean already, so it only
			//       reconstructs a pin whose seed lost its "__pqi" name (the mirror of the output
			//       reconstruction below, which already runs for every cell).
			//   (2) ALL cells -- self-containment: a cone-cell input that reads a net driven from
			//       *outside* the cone leaks out as a spurious input port (submod can only export a
			//       port for a net driven inside the carve). The forward walk never reaches a
			//       constant/tie source (0-input cell, e.g. an async flop's inactive SET/RESET), an
			//       undriven internal net (inserted scan/"test" pin, opt artifact), or a gate fed
			//       only by such constants. Per cone-cell input: fold a name-recoverable tie
			//       (logic_0/logic_1 net) to a literal for a plain cell (area-neutral -- keeps a
			//       sequential cell at a single mapped instance), clone the source otherwise and
			//       for design cells (so a shared global tie can't drag in a neighbour's cone and
			//       the tie's tiny power is characterized in-cone), tie an undriven net to 0, and
			//       pull a forward-walk-missed gate into the cone.
			//
			// KNOWN LIMITATION (~3.6% of carved cells): a launch-flop seed that lost its "__pqi"
			// name can still leak as a bare "n_<num>" input port even after part (1) rebuilds the
			// clean "__pqcarve.<base>_<pin>" bus -- the reconstructed port does not survive to the
			// final module (the cone re-reads the flattened seed net). It concentrates in the WIDE
			// cells (multi-bit shifters sshl/shl/sshr/shr, mul, mem, and the wider add/sub/div/mod)
			// plus the fast aes/aes_inv key (a QN-output DFFHQNx1 launch flop, where the whole
			// 128-bit key leaks). Triage narrowed it down:
			//   - it is deterministic, and the cone walk DOES reach the seed (launch flop found,
			//     output seeded, reader in the cone -- so it is NOT a cone-walk exclusion);
			//   - part (1) builds cwi and rewires the cone, but cwi is re-merged/dropped, so the
			//     final module still exports the "n_<num>" seed.
			// Pinpointing the exact step still needs instrumentation of the reconstruction REWRITE
			// and the post-submod cleanup (not just the cone walk) to trace the cwi lifecycle. Such
			// cells fall back to the model rather than a clean gate-level testbench. See
			// docs/dev/carvenetlist_dev.md.
			const IdString SUBMOD = RTLIL::escape_id("submod");
			dict<SigBit, SigBit> in_remap; // launch-flop output bit -> clean input-port bit
			// (1) Reconstruct clean input ports at the launch-flop boundary. A whole design's
			// launch-flop outputs all keep internal flattened names and are always renamed; a
			// plain cell's "__pqi" boundary name usually survives SigMap election, so only a pin
			// whose seed net lost it (and would otherwise leak as a bare "n_<num>" input port,
			// the mirror of the output reconstruction below which already runs for every cell) is
			// reconstructed. The clean majority is left untouched -- no net-name churn, and no
			// risk to the QN-launch-flop cells whose reconstruction is known not to survive.
			{
				for (auto pw : g.in_wires) {
					Wire *cwi = nullptr;
					for (int i = 0; i < pw->width; i++) {
						Cell *fc = hop_fwd(sigmap(SigBit(pw, i)));
						if (fc == nullptr || !launch.count(fc))
							continue;
						SigBit qi;
						bool found = false;
						for (auto ob : cell_out_bits[fc]) {
							if (clk_nets.count(ob) || !loads.count(ob))
								continue; // the launch flop's data output that drives the cone
							qi = ob;
							found = true;
							break;
						}
						if (!found)
							continue;
						if (!is_design) {
							std::string qn = qi.wire ? unescape(qi.wire->name.str()) : "";
							if (qn.find("__pqi") != std::string::npos ||
							    qn.find(base) != std::string::npos)
								continue; // seed already recovers a clean port name: leave it
						}
						if (cwi == nullptr)
							cwi = train->addWire(
							    RTLIL::escape_id("__pqcarve." + unescape(pw->name.str())), pw->width);
						// Copy the launch-flop seed into the clean carve wire with a boundary buffer
						// that stays in 'train' (untagged), so cwi is driven from outside the cone and
						// submod exports it as the clean "<base>_<pin>" input port. The buffer MUST be
						// kept: submod runs opt_clean before extraction, and opt_clean dissolves a
						// plain $_BUF_ (aliasing Y=A) -- that would collapse cwi back onto the
						// flattened "n_<num>" seed net, so submod would then name the port after the
						// seed (the leak). The capture-flop OUTPUT reconstruction keeps its buffer for
						// the identical reason. The buffer is untagged, so it is dropped with 'train'
						// after the carve; the carved cell keeps only its real gate(s) -- no area hit.
						Cell *ib = train->addBufGate(NEW_ID, qi, SigBit(cwi, i));
						ib->set_bool_attribute(ID::keep);
						in_remap[qi] = SigBit(cwi, i);
					}
				}
			}

			// (2) Self-containment (runs for EVERY carved cell): one rewrite pass over the
			// (growing) cone. For a design cell in_remap also applies part (1); for a plain cell
			// in_remap is empty, so this only folds constants/ties, ties undriven nets to 0, and
			// pulls in forward-walk-missed gates -- a no-op on an already-clean cone.
			{
				std::vector<Cell *> proc(logic.begin(), logic.end());
				pool<Cell *> queued = logic;
				while (!proc.empty()) {
					Cell *c = proc.back();
					proc.pop_back();
					dict<IdString, SigSpec> rewire;
					for (auto &conn : c->connections()) {
						if (!c->input(conn.first))
							continue;
						SigSpec cs = conn.second;
						bool changed = false;
						for (auto &bit : cs) {
							if (bit.wire == nullptr)
								continue; // already a constant literal
							SigBit s = sigmap(bit);
							auto rm = in_remap.find(s);
							if (rm != in_remap.end()) {
								bit = rm->second; // clean primary input
								changed = true;
								continue;
							}
							if (s.wire == nullptr || clk_nets.count(s) || driven.count(s))
								continue; // constant / shared clock / produced in-cone: fine
							auto dit = driver.find(s);
							if (dit != driver.end() && boundary_cells.count(dit->second.first))
								continue; // launch-flop output the remap above missed: keep as input
							if (dit == driver.end()) {
								// Undriven internal net (inserted scan/test pin, etc.): tie to 0.
								bit = State::S0;
								changed = true;
								continue;
							}
							Cell *dc = dit->second.first;
							IdString opin = dit->second.second;
							bool is_source = !cell_in_bits.count(dc) || cell_in_bits.at(dc).empty();
							if (is_source && GetSize(dc->getPort(opin)) == 1) {
								// Pure constant/tie source read from outside the cone. For a plain
								// cell fold it to a literal using the synth's logic_0/logic_1 tie-net
								// naming (area-neutral -- keeps a sequential cell at a single mapped
								// instance). Otherwise (design cell, or an unrecognizable value)
								// clone the source into the carve rather than steal a possibly-shared
								// original, so the cone bit gains an in-cone driver and the tie's
								// (tiny) power is characterized here.
								std::string wn = s.wire ? unescape(s.wire->name.str()) : "";
								if (!is_design && wn.find("logic_1") != std::string::npos) {
									bit = State::S1;
								} else if (!is_design && wn.find("logic_0") != std::string::npos) {
									bit = State::S0;
								} else {
									Cell *clone = train->addCell(NEW_ID, dc->type);
									clone->parameters = dc->parameters;
									for (auto &cc : dc->connections())
										clone->setPort(cc.first, cc.second);
									Wire *tn = train->addWire(NEW_ID, 1);
									clone->setPort(opin, SigSpec(tn));
									clone->set_string_attribute(SUBMOD, final);
									logic.insert(clone);
									driven.insert(SigBit(tn));
									bit = SigBit(tn);
								}
								changed = true;
							} else if (!queued.count(dc)) {
								// A non-source cell the forward walk missed (only constant-fed):
								// pull it into the carve and process its inputs too.
								dc->set_string_attribute(SUBMOD, final);
								logic.insert(dc);
								queued.insert(dc);
								proc.push_back(dc);
								for (auto ob : cell_out_bits[dc])
									driven.insert(ob);
							}
						}
						if (changed)
							rewire[conn.first] = cs;
					}
					for (auto &r : rewire)
						c->setPort(r.first, r.second);
				}
			}

			boundary[final] = {speed, drv_cell, drv_pin, load_cell, load_pin};
		}

		log("Carved %d cells (%d logic cells tagged)\n", GetSize(boundary), tagged_total);

		// Carve every tagged cell into its own module (submod names it "train.<final>");
		// the untagged flops/clock-network cells stay in 'train'.
		Pass::call(design, "submod -separator .");

		// Strip the "train." prefix off the carved module names
		std::string mprefix = "\\train.";
		for (auto mod : design->modules().to_vector()) {
			std::string n = mod->name.str();
			if (n.rfind(mprefix, 0) == 0)
				design->rename(mod, RTLIL::escape_id(n.substr(mprefix.size())));
		}

		// Map every design module to its instantiations so that renaming a module's
		// port wires below can keep the matching port-connection keys on its instances
		// in sync (Module::rename only touches the wire, not the instance connections).
		dict<IdString, std::vector<Cell *>> insts_by_type;
		for (auto mod : design->modules())
			for (auto cell : mod->cells())
				if (design->module(cell->type) != nullptr)
					insts_by_type[cell->type].push_back(cell);

		// Clean up the carved cell port names, updating each instance's port-connection key
		// to match the renamed port (Module::rename only touches the wire). Two fixups:
		//   1. Strip leftover __pqi/__pqo boundary suffixes (present when synthesis kept the
		//      carved net names; harmless no-op otherwise).
		//   2. Drop the flatten instance-scope prefix (everything up to and including the
		//      first '.') so a port recovers its clean train top-port name, e.g.
		//      "slow_<enc>.slow_<enc>_A" -> "slow_<enc>_A", then collapse any remaining dots
		//      (e.g. exposed clock-gate pins like "slow_<enc>.CG_INST.enable") to '_'. The
		//      flatten earlier scope-prefixes every inlined net with a '.', which OpenSTA
		//      tolerates but the cocotb/iverilog power flow cannot (it can't access a port
		//      whose name contains '.', treating the dot as a hierarchy separator).
		for (auto mod : design->modules()) {
			if (mod->name == ID(train))
				continue;
			bool stripped = false;
			// Process the reconstructed capture-flop output buses ("__pqcarve.<base>_<pin>",
			// tagged PQ_CARVE_OUT) first. They collapse to the clean "<base>_<pin>" output
			// port and are the authoritative output. A degenerate output bus (const-shift /
			// feed-through / self-referential cell) can leave a stale "<base>_<pin>__pqo"
			// cone-output fragment that cleans to the same name; whoever is renamed first
			// wins the collision below, so the reconstructed bus must go first or the carved
			// cell loses its output port (degenerating to input/inout with the result
			// stranded). See the collision handling below for how the stale fragment is
			// then demoted to an internal net rather than aliased onto the output.
			std::vector<Wire *> wires_ordered = mod->wires().to_vector();
			std::stable_partition(wires_ordered.begin(), wires_ordered.end(), [](Wire *w) {
				return unescape(w->name.str()).rfind("__pqcarve.", 0) == 0;
			});
			for (auto wire : wires_ordered) {
				if (!wire->port_input && !wire->port_output)
					continue;
				std::string wn = unescape(wire->name.str());
				std::string nn = wn;
				for (const char *suf : {"__pqi", "__pqo"}) {
					size_t pos;
					while ((pos = nn.find(suf)) != std::string::npos)
						nn.erase(pos, strlen(suf));
				}
				size_t dot = nn.find('.');
				if (dot != std::string::npos)
					nn = nn.substr(dot + 1);
				std::replace(nn.begin(), nn.end(), '.', '_');
				if (nn == wn)
					continue;
				IdString oldid = wire->name;
				IdString newid = RTLIL::escape_id(nn);
				// Two boundary wires can clean up to the same per-pin name. This happens
				// when synthesis splits one logical cell-input bus across more than one net
				// -- e.g. a drive-strength buffer inserted on a subset of the bits, so the
				// flattened submodule reads {buffered_bits, flop_bits}. flatten then leaves
				// both the train-side "<base>_<pin>__pqi" (carrying the directly-read bits)
				// and the scope-prefixed "<base>.<base>_<pin>__pqi" (carrying the buffered
				// bits), and submod exports each as its own port. They are the same logical
				// pin, so fold the fragments onto one bus port instead of uniquifying (a
				// phantom second port the OpenSTA/cocotb flows could not drive): alias the
				// loser onto the already-renamed winner -- a no-op on bits they share, and on
				// the disjoint bits it wires the winner's otherwise-dangling bit to the
				// loser's reader (the in-cone buffer) -- and drop the loser's port flag so the
				// trailing clean collapses it away.
				if (Wire *ex = mod->wire(newid); ex != nullptr && ex != wire) {
					// The reconstructed capture-flop output bus (cw, tagged PQ_CARVE_OUT,
					// processed first above so it always wins the name) is the authoritative
					// clean output port. The colliding wire is then a stale cone-output
					// fragment ("<base>_<pin>__pqo") that the per-bit buffers already *source*
					// from -- aliasing it onto cw would turn every buffer into Y[i]=Y[i] (a
					// combinational self-loop) and strand the real gate/feed-through/tie
					// drivers. So demote the fragment to an internal net (leaving it driven
					// in-cone and read by the buffers); the later __pqo neutralization renames
					// it. Do NOT connect it to cw.
					if (ex->get_bool_attribute(PQ_CARVE_OUT)) {
						wire->port_input = false;
						wire->port_output = false;
						stripped = true;
						continue;
					}
					if (ex->width == wire->width) {
						log("carvenetlist: unifying split boundary port '%s' into '%s' in "
						    "module %s\n", log_id(oldid), log_id(newid), log_id(mod->name));
						wire->port_input = false;
						wire->port_output = false;
						mod->connect(SigSpec(wire), SigSpec(ex));
						stripped = true;
						continue;
					}
					log_warning("carvenetlist: cannot unify boundary port '%s' -> '%s' in "
						    "module %s (widths %d vs %d differ); leaving original name.\n",
						    log_id(oldid), log_id(newid), log_id(mod->name), wire->width,
						    ex->width);
					continue;
				}
				mod->rename(wire, newid);
				stripped = true;
				for (auto inst : insts_by_type[mod->name]) {
					if (!inst->hasPort(oldid))
						continue;
					SigSpec sig = inst->getPort(oldid);
					inst->unsetPort(oldid);
					inst->setPort(newid, sig);
				}
			}
			// Drop the internal carve-output marker now that collisions are resolved so it
			// does not leak into the emitted netlist.
			for (auto wire : mod->wires())
				if (wire->get_bool_attribute(PQ_CARVE_OUT))
					wire->attributes.erase(PQ_CARVE_OUT);
			if (stripped)
				mod->fixup_ports();
		}

		// Simplify away the wire-to-wire aliases left by flatten and by the split-port
		// unification above, dropping each redundant copy down to the single surviving
		// (port-named) net so every carved boundary becomes exactly one clean port.
		Pass::call(design, "clean -purge");

		// Turn the temporary passthrough buffers back into plain assigns (zero-area
		// feed-throughs) now that submod has given each its own clean input/output port.
		// Done after the final clean so the assign isn't re-collapsed back into one net.
		for (auto mod : design->modules()) {
			if (mod->name == ID(train))
				continue;
			for (auto cell : mod->cells().to_vector()) {
				if (cell->type != ID($_BUF_) || !cell->has_attribute(PQ_PASS))
					continue;
				SigSpec a = cell->getPort(ID::A);
				SigSpec y = cell->getPort(ID::Y);
				mod->remove(cell);
				mod->connect(y, a);
			}
		}

		// Neutralize any __pqi/__pqo token left on an *internal* net. Every output bit is
		// now driven through a capture-flop-boundary buffer whose source is the in-cone net
		// the flop used to read -- that net keeps its original "<base>_<pin>__pqo" boundary
		// name but is no longer a port (the buffer's fresh carve wire is). The leftover name
		// is purely cosmetic for an internal net, but strip the token (uniquifying on
		// collision) so no boundary marker survives the carve.
		for (auto mod : design->modules()) {
			if (mod->name == ID(train))
				continue;
			for (auto wire : mod->wires().to_vector()) {
				if (wire->port_input || wire->port_output)
					continue;
				std::string wn = unescape(wire->name.str());
				if (wn.find("__pqi") == std::string::npos && wn.find("__pqo") == std::string::npos)
					continue;
				std::string nn = wn;
				for (const char *suf : {"__pqi", "__pqo"}) {
					size_t pos;
					while ((pos = nn.find(suf)) != std::string::npos)
						nn.erase(pos, strlen(suf));
				}
				IdString newid = RTLIL::escape_id(nn);
				mod->rename(wire, (nn.empty() || mod->wire(newid) != nullptr) ? NEW_ID : newid);
			}
		}

		// Replace a REDUNDANT SINGLE-FANOUT 1-input/1-output cell (a lone drive-strength buffer
		// or a cell->capture-flop output buffer sitting on top of a real in-cone gate) with a
		// direct wire: its one load simply moves to the upstream driver, so delay/power are
		// unchanged, and the cone still carves to its one real gate (matching the normal flow).
		// Dropping such an inverter's inversion is fine -- cells are characterized for PPA, not
		// function, and toggle activity (hence power) is polarity-independent.
		//
		// KEEP a passthrough that is the cone's BOUNDARY GATE -- one whose input is not driven by
		// another in-cone cell (it reads a primary input / launch-flop boundary net). It is the
		// cell-under-test's only logic, not a redundant re-driver, so shorting it would replace
		// the whole cone with a bare wire: nothing left to characterize, and for an inverter the
		// inversion is silently dropped (the carved cell no longer matches the RTL).
		//
		// KEEP a passthrough whose output has FANOUT > 1. Such a buffer/inverter is a fanout
		// (re-drive) buffer -- e.g. a wide multiplier/adder's input and adder-tree buffer trees,
		// where a single input bit fans out to hundreds of partial-product gates. Shorting it
		// dumps its whole fanout onto the upstream driver; since characterization drives the
		// boundary with set_driving_cell, STA then charges a single flop driving that entire
		// fanout, massively inflating the measured delay. (no_inv_delay_calc excludes the buffer's
		// own stage delay, but NOT the loading it removes.) So fanout buffers are load-bearing for
		// delay and must be kept.
		//
		// EXCEPTION: a passthrough on a flop's feedback path (e.g. the QN -> INV -> D loop that
		// implements the hold of a scan-flop-based enable flop like dffe/sdffce) must be kept --
		// shorting it would tie the flop's D onto its own Q/QN and turn a hold into a toggle.
		// Detect this as "the cell driving the passthrough's input also reads its output".
		//
		// DESIGN CELLS (design_slow_<enc>/design_fast_<enc>) are exempted entirely: a whole
		// sequential design is characterized for its real function, not just PPA, so its logic
		// inverters carry genuine inversions. Shorting them (out=in) would drop every inversion
		// and make the carved design inequivalent to RTL (its testbench fails).
		for (auto mod : design->modules()) {
			if (mod->name == ID(train))
				continue;
			std::string mn = unescape(mod->name.str());
			if (mn.rfind("design_slow_", 0) == 0 || mn.rfind("design_fast_", 0) == 0)
				continue;
			// Original-topology driver/reader maps (net bit -> output cell / input cells) plus a
			// per-net load count (input-pin occurrences) and the output-port bit set, so a
			// passthrough's output fanout (loads + whether it drives a module output) is known.
			SigMap sm(mod);
			dict<SigBit, Cell *> drv;
			dict<SigBit, pool<Cell *>> rdr;
			dict<SigBit, int> load_cnt;
			for (auto cell : mod->cells())
				for (auto &conn : cell->connections())
					for (auto bit : sm(conn.second)) {
						if (bit.wire == nullptr)
							continue;
						if (cell->output(conn.first))
							drv[bit] = cell;
						if (cell->input(conn.first)) {
							rdr[bit].insert(cell);
							load_cnt[bit]++;
						}
					}
			pool<SigBit> outport_bits;
			for (auto w : mod->wires())
				if (w->port_output)
					for (auto bit : sm(SigSpec(w)))
						if (bit.wire)
							outport_bits.insert(bit);
			for (auto cell : mod->cells().to_vector()) {
				if (!is_passthrough(cell))
					continue;
				SigSpec in, out;
				for (auto &conn : cell->connections()) {
					if (cell->input(conn.first))
						in = conn.second;
					else if (cell->output(conn.first))
						out = conn.second;
				}
				if (GetSize(in) != 1 || GetSize(out) != 1)
					continue;
				SigBit ib = sm(in[0]), ob = sm(out[0]);
				// Keep the cone's boundary gate: a passthrough whose input has no in-cone driver
				// (reads a primary input / boundary net) is the cell-under-test's only logic, so
				// shorting it would strand the cone as a bare wire (dropping the gate, and for an
				// inverter its inversion). Only redundant re-drivers stacked on a real in-cone
				// gate -- whose input IS driven by another cell -- may be shorted away.
				if (!drv.count(ib))
					continue;
				// Keep fanout>1 passthroughs: a fanout (re-drive) buffer/inverter whose removal
				// would dump its load onto the upstream driver and inflate its characterized delay.
				int fanout = (load_cnt.count(ob) ? load_cnt.at(ob) : 0) +
					     (outport_bits.count(ob) ? 1 : 0);
				if (fanout > 1)
					continue;
				// Feedback guard: the cell driving this passthrough's input also reads its output.
				auto dit = drv.find(ib);
				if (dit != drv.end() && dit->second != cell && rdr.count(ob) &&
				    rdr.at(ob).count(dit->second))
					continue;
				mod->remove(cell);
				mod->connect(out, in);
			}
		}
		// Drop the now-dangling internal nets and fold the wire-to-wire aliases left behind.
		Pass::call(design, "clean");

		// Record each carved cell's surround boundary as \pq_* string attributes on its
		// module, so the Python flow can re-impose the launch/capture flops during OpenSTA
		// characterization without a separate boundary side file.
		for (auto mod : design->modules()) {
			if (mod->name == ID(train))
				continue;
			auto it = boundary.find(unescape(mod->name.str()));
			if (it == boundary.end())
				continue;
			const BoundaryRec &r = it->second;
			mod->set_string_attribute(RTLIL::escape_id("pq_speed"), r.speed);
			mod->set_string_attribute(RTLIL::escape_id("pq_driving_cell"), r.driving_cell);
			mod->set_string_attribute(RTLIL::escape_id("pq_driving_pin"), r.driving_pin);
			mod->set_string_attribute(RTLIL::escape_id("pq_load_cell"), r.load_cell);
			mod->set_string_attribute(RTLIL::escape_id("pq_load_pin"), r.load_pin);
		}

		// Drop the flop-bearing train module
		if (Module *t = design->module(ID(train)))
			design->remove(t);
	}
} CarveNetlistPass;

PRIVATE_NAMESPACE_END
