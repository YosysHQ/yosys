/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                      Eddie Hung <eddie@fpgeh.com>
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

// [[CITE]] The AIGER And-Inverter Graph (AIG) Format Version 20071012
// Armin Biere. The AIGER And-Inverter Graph (AIG) Format Version 20071012. Technical Report 07/1, October 2011, FMV Reports Series, Institute for Formal Models and Verification, Johannes Kepler University, Altenbergerstr. 69, 4040 Linz, Austria.
// http://fmv.jku.at/papers/Biere-FMV-TR-07-1.pdf

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "aigerparse.h"

YOSYS_NAMESPACE_BEGIN

#define log_debug log

void parse_aiger(RTLIL::Design *design, std::istream &f, std::string clk_name)
{
    std::string header;
    f >> header;
    if (header != "aag") {
        log_error("Unsupported AIGER file!\n");
        return;
    }

    int M, I, L, O, A;
    int B=0, C=0, J=0, F=0; // Optional in AIGER 1.9
    if (!(f >> M >> I >> L >> O >> A)) {
        log_error("Invalid AIGER header\n");
        return;
    }
    for (auto &i : std::array<std::reference_wrapper<int>,4>{B, C, J, F}) {
        if (f.peek() != ' ') break;
        if (!(f >> i)) {
            log_error("Invalid AIGER header\n");
            return;
        }
    }

    std::string line;
    std::getline(f, line); // Ignore up to start of next ine, as standard
                           // says anything that follows could be used for
                           // optional sections
    
    log_debug("M=%d I=%d L=%d O=%d A=%d B=%d C=%d J=%d F=%d\n", M, I, L, O, A, B, C, J, F);

    int line_count = 1;
    std::stringstream ss;

    auto module = new RTLIL::Module;
    module->name = RTLIL::escape_id("aig"); // TODO: Name?
    if (design->module(module->name))
        log_error("Duplicate definition of module %s in line %d!\n", log_id(module->name), line_count);
    design->add(module);

    auto createWireIfNotExists = [module](int literal) {
        const int variable = literal >> 1;
        const bool invert = literal & 1;
        RTLIL::IdString wire_name(stringf("\\n%d%s", variable, invert ? "_inv" : "")); // FIXME: is "_inv" the right suffix?
        RTLIL::Wire *wire = module->wire(wire_name);
        if (wire) return wire;
        log_debug("Creating %s\n", wire_name.c_str());
        wire = module->addWire(wire_name);
        if (!invert) return wire;
        RTLIL::IdString wire_inv_name(stringf("\\n%d", variable));
        RTLIL::Wire *wire_inv = module->wire(wire_inv_name); 
        if (wire_inv) {
            if (module->cell(wire_inv_name)) return wire;
        } 
        else {
            log_debug("Creating %s\n", wire_inv_name.c_str());
            wire_inv = module->addWire(wire_inv_name);
        }

        log_debug("Creating %s = ~%s\n", wire_name.c_str(), wire_inv_name.c_str());
        RTLIL::Cell *inv = module->addCell(stringf("\\n%d_not", variable), "$_NOT_"); // FIXME: is "_not" the right suffix?
        inv->setPort("\\A", wire_inv);
        inv->setPort("\\Y", wire);

        return wire;
    };

    int l1, l2, l3;

    // Parse inputs
    for (int i = 0; i < I; ++i, ++line_count) {
        if (!(f >> l1)) {
            log_error("Line %d cannot be interpreted as an input!\n", line_count);
            return;
        }
        log_debug("%d is an input\n", l1);
        log_assert(!(l1 & 1)); // TODO: Inputs can't be inverted?
        RTLIL::Wire *wire = createWireIfNotExists(l1);
        wire->port_input = true;
    }

    // Parse latches
    for (int i = 0; i < L; ++i, ++line_count) {
        if (!(f >> l1 >> l2)) {
            log_error("Line %d cannot be interpreted as a latch!\n", line_count);
            return;
        }
        log_debug("%d %d is a latch\n", l1, l2);
        log_assert(!(l1 & 1)); // TODO: Latch outputs can't be inverted?
        RTLIL::Wire *q_wire = createWireIfNotExists(l1);
        RTLIL::Wire *d_wire = createWireIfNotExists(l2);
        RTLIL::IdString clk_id = RTLIL::escape_id(clk_name.c_str());
        RTLIL::Wire *clk_wire = module->wire(clk_id);
        if (!clk_wire) {
            log_debug("Creating %s\n", clk_id.c_str());
            clk_wire = module->addWire(clk_id);
            clk_wire->port_input = true;
        }

        module->addDff(NEW_ID, clk_wire, d_wire, q_wire);
        // AIGER latches are assumed to be initialized to zero
        q_wire->attributes["\\init"] = RTLIL::Const(0);
    }

    // Parse outputs
    for (int i = 0; i < O; ++i, ++line_count) {
        if (!(f >> l1)) {
            log_error("Line %d cannot be interpreted as an output!\n", line_count);
            return;
        }

        log_debug("%d is an output\n", l1);
        RTLIL::Wire *wire = createWireIfNotExists(l1);
        wire->port_output = true;
    }
    std::getline(f, line); // Ignore up to start of next line
    
    // TODO: Parse bad state properties
    for (int i = 0; i < B; ++i, ++line_count)
        std::getline(f, line); // Ignore up to start of next line

    // TODO: Parse invariant constraints
    for (int i = 0; i < C; ++i, ++line_count)
        std::getline(f, line); // Ignore up to start of next line

    // TODO: Parse justice properties
    for (int i = 0; i < J; ++i, ++line_count)
        std::getline(f, line); // Ignore up to start of next line

    // TODO: Parse fairness constraints
    for (int i = 0; i < F; ++i, ++line_count)
        std::getline(f, line); // Ignore up to start of next line

    // Parse AND
    for (int i = 0; i < A; ++i, ++line_count) {
        if (!(f >> l1 >> l2 >> l3)) {
            log_error("Line %d cannot be interpreted as an AND!\n", line_count);
            return;
        }

        log_debug("%d %d %d is an AND\n", l1, l2, l3);
        log_assert(!(l1 & 1)); // TODO: Output of ANDs can't be inverted?
        RTLIL::Wire *o_wire = createWireIfNotExists(l1);
        RTLIL::Wire *i1_wire = createWireIfNotExists(l2);
        RTLIL::Wire *i2_wire = createWireIfNotExists(l3);

		RTLIL::Cell *and_cell = module->addCell(NEW_ID, "$_AND_");
		and_cell->setPort("\\A", i1_wire);
		and_cell->setPort("\\B", i2_wire);
		and_cell->setPort("\\Y", o_wire);
    }

    module->fixup_ports();
}

struct AigerFrontend : public Frontend {
	AigerFrontend() : Frontend("aiger", "read AIGER file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_aiger [options] [filename]\n");
		log("\n");
		log("Load modules from an AIGER file into the current design.\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing AIGER frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			break;
		}
		extra_args(f, filename, args, argidx);

		parse_aiger(design, *f);
	}
} AigerFrontend;

YOSYS_NAMESPACE_END
