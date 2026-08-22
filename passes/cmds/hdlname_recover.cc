/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  hdlname_recover -- restore cell provenance lost during synthesis
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

// WHY THIS PASS EXISTS
// --------------------
// After synthesis, essentially no cell can be traced back to the RTL that
// produced it. Measured on a 70k-cell xc7 design (yosys 0.62, synth_xilinx
// -flatten), grouping the cells that lack `hdlname` by the pass that created
// them:
//
//     blifparse.cc (abc)   41809
//     ff.cc                27614
//     hierarchical           423
//     alumacc.cc              33
//     iopadmap                29
//     clkbufmap.cc             1
//
// Only 2 real cells in the whole design carry `hdlname`. (A `hdlname` count
// taken from the JSON looks like 1657, but every one of those is a $scopeinfo
// marker rather than a cell -- worth knowing before using that number as a
// success criterion.)
//
// `src` survives but is useless for attribution: techmap overwrites it with its
// own file, so all 19406 LUT6s in that design share
// "techlibs/xilinx/lut_map.v:43".
//
// Cell NAMES cannot substitute either, being pass-internal counters:
//
//     $abc$493613$auto$blifparse.cc:557:parse_blif$493614
//
// Two modules differing by one unrelated gate share ZERO cell names, because the
// ABC counter shifts and renames everything including untouched cells.
//
// The consequence is that any consumer wanting to act per-RTL-module --
// floorplanning, region constraints, incremental P&R, per-module timing
// attribution -- has nothing to key on.
//
// The proper fix is for each pass to propagate `hdlname` when it creates a cell
// from existing ones. That touches many passes. This is the pragmatic
// alternative: net NAMES survive flattening, because flatten encodes the
// hierarchy into them, so a cell's scope can be recovered from the nets it
// touches. Self-contained, and it changes nothing about how synthesis runs.
//
//     \odocrypt_gpio_wrapper_inst.g_miner[0].miner_top_inst.miner.worker.crypt.
//         crypter.round0.sboxes.sbox0inst.mem$rdreg[0]$d
//
// Validated as a Python prototype on that design: 100% of cells resolved
// (69975/69975), with round-level groups coming out uniform at ~2427 cells for
// 21 identical pipeline rounds, cross-checked against an independent derivation.

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// The leading run of RTL-derived components of a net name.
//
// Stops at the first generated component. A yosys net name is a dotted path
// whose parts are either RTL identifiers ('crypter', 'round14', 'g_miner[0]')
// or generated fragments carrying a counter ('$auto$alumacc.cc:512:...$58344').
// Everything from the first generated part onwards says where a pass put
// something, not where the designer did, so it is dropped -- and it is unstable
// across edits, which defeats the purpose.
static std::vector<std::string> rtl_scope(const std::string &name)
{
	std::vector<std::string> out;
	if (name.empty() || name[0] != '\\')
		return out; // not a public name: nothing RTL-derived to recover
	std::string s = name.substr(1);
	size_t pos = 0;
	while (pos <= s.size()) {
		size_t dot = s.find('.', pos);
		if (dot == std::string::npos)
			dot = s.size();
		std::string part = s.substr(pos, dot - pos);
		if (part.empty() || part.find('$') != std::string::npos)
			break;
		out.push_back(part);
		if (dot == s.size())
			break;
		pos = dot + 1;
	}
	// The last component is the signal itself, not a scope.
	if (!out.empty())
		out.pop_back();
	return out;
}

struct HdlnameRecoverPass : public Pass {
	HdlnameRecoverPass() : Pass("hdlname_recover", "recover cell hdlname attributes from net names") {}

	void help() override
	{
		log("\n");
		log("    hdlname_recover [options] [selection]\n");
		log("\n");
		log("Set the 'hdlname' attribute on cells that have lost it during synthesis,\n");
		log("deriving each cell's RTL scope from the names of the nets it connects to.\n");
		log("\n");
		log("Cells created by technology mapping and by abc carry no provenance, so\n");
		log("downstream tools cannot act per RTL module -- floorplanning, region\n");
		log("constraints and per-module timing attribution all need it. Net names survive\n");
		log("flattening, so the scope can be recovered from them.\n");
		log("\n");
		log("    -overwrite\n");
		log("        also set the attribute on cells that already have one.\n");
		log("        Default is to leave existing hdlname untouched.\n");
		log("\n");
		log("A cell's scope is taken from its OUTPUT nets where possible: the output\n");
		log("names what the cell computes, whereas an input may belong to the previous\n");
		log("stage and would attribute the cell backwards.\n");
		log("\n");
		log("Nets whose name resolves to more than one scope at the same depth are\n");
		log("ignored. Those are global signals threaded through every instance, and they\n");
		log("attribute cells essentially at random -- in one measured design a single\n");
		log("such net pulled 8786 unrelated cells into one scope.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool overwrite = false;

		log_header(design, "Executing HDLNAME_RECOVER pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-overwrite") {
				overwrite = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);

			// bit -> scope, keeping only bits whose scope is unambiguous.
			dict<RTLIL::SigBit, std::vector<std::string>> bit_scope;
			pool<RTLIL::SigBit> ambiguous;

			for (auto wire : module->wires()) {
				auto scope = rtl_scope(wire->name.str());
				if (scope.empty())
					continue;
				for (auto bit : sigmap(RTLIL::SigSpec(wire))) {
					if (!bit.wire)
						continue;
					if (ambiguous.count(bit))
						continue;
					auto it = bit_scope.find(bit);
					if (it == bit_scope.end()) {
						bit_scope[bit] = scope;
						continue;
					}
					if (it->second == scope)
						continue;
					// One scope may be an ancestor of the other, in which case
					// the deeper one is simply more specific and is kept.
					const auto &a = it->second;
					const auto &b = scope;
					const auto &shorter = a.size() < b.size() ? a : b;
					const auto &longer = a.size() < b.size() ? b : a;
					bool prefix = true;
					for (size_t i = 0; i < shorter.size(); i++)
						if (shorter[i] != longer[i]) {
							prefix = false;
							break;
						}
					if (prefix) {
						it->second = longer;
					} else {
						// Genuinely conflicting: a global signal named inside
						// several unrelated scopes. It carries no usable
						// attribution, so drop the bit entirely.
						bit_scope.erase(bit);
						ambiguous.insert(bit);
					}
				}
			}

			int set_from_output = 0, set_from_input = 0, unresolved = 0, skipped = 0;

			for (auto cell : module->selected_cells()) {
				if (!overwrite && cell->has_attribute(ID::hdlname)) {
					skipped++;
					continue;
				}

				const std::vector<std::string> *best = nullptr;
				bool from_output = false;

				// Output ports first.
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first))
						continue;
					for (auto bit : sigmap(conn.second)) {
						auto it = bit_scope.find(bit);
						if (it == bit_scope.end())
							continue;
						if (best == nullptr || it->second.size() > best->size()) {
							best = &it->second;
							from_output = true;
						}
					}
				}
				if (best == nullptr) {
					for (auto &conn : cell->connections()) {
						if (cell->output(conn.first))
							continue;
						for (auto bit : sigmap(conn.second)) {
							auto it = bit_scope.find(bit);
							if (it == bit_scope.end())
								continue;
							if (best == nullptr || it->second.size() > best->size())
								best = &it->second;
						}
					}
				}

				if (best == nullptr) {
					unresolved++;
					continue;
				}

				cell->set_hdlname_attribute(*best);
				if (from_output)
					set_from_output++;
				else
					set_from_input++;
			}

			log("Module %s: set hdlname on %d cell(s) (%d from an output net, %d from an input net).\n",
			    log_id(module), set_from_output + set_from_input, set_from_output, set_from_input);
			if (unresolved)
				log("  %d cell(s) touch no net with a recoverable scope.\n", unresolved);
			if (skipped)
				log("  %d cell(s) already had hdlname and were left alone.\n", skipped);
			if (!ambiguous.empty())
				log("  %d net bit(s) named in conflicting scopes were ignored.\n", int(ambiguous.size()));
		}
	}
} HdlnameRecoverPass;

PRIVATE_NAMESPACE_END
