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

#ifndef _WIN32
#include <libgen.h>
#endif
#include <array>

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "aigerparse.h"

YOSYS_NAMESPACE_BEGIN

AigerReader::AigerReader(RTLIL::Design *design, std::istream &f, RTLIL::IdString module_name, RTLIL::IdString clk_name)
	: design(design), f(f), clk_name(clk_name)
{
	module = new RTLIL::Module;
	module->name = module_name;
	if (design->module(module->name))
		log_error("Duplicate definition of module %s!\n", log_id(module->name));
}

void AigerReader::parse_aiger()
{
	std::string header;
	f >> header;
	if (header != "aag" && header != "aig")
		log_error("Unsupported AIGER file!\n");

	// Parse rest of header
	if (!(f >> M >> I >> L >> O >> A))
		log_error("Invalid AIGER header\n");

	// Optional values
	B = C = J = F = 0;
	if (f.peek() != ' ') goto end_of_header;
	if (!(f >> B)) log_error("Invalid AIGER header\n");
	if (f.peek() != ' ') goto end_of_header;
	if (!(f >> C)) log_error("Invalid AIGER header\n");
	if (f.peek() != ' ') goto end_of_header;
	if (!(f >> J)) log_error("Invalid AIGER header\n");
	if (f.peek() != ' ') goto end_of_header;
	if (!(f >> F)) log_error("Invalid AIGER header\n");
end_of_header:

	std::string line;
	std::getline(f, line); // Ignore up to start of next line, as standard
	// says anything that follows could be used for
	// optional sections

	log_debug("M=%u I=%u L=%u O=%u A=%u B=%u C=%u J=%u F=%u\n", M, I, L, O, A, B, C, J, F);

	line_count = 1;

	if (header == "aag")
		parse_aiger_ascii();
	else if (header == "aig")
		parse_aiger_binary();
	else
		log_abort();

	RTLIL::Wire* n0 = module->wire("\\n0");
	if (n0)
		module->connect(n0, RTLIL::S0);

	for (unsigned i = 0; i < outputs.size(); ++i) {
		RTLIL::Wire *wire = outputs[i];
		if (wire->port_input) {
			RTLIL::Wire *o_wire = module->addWire(wire->name.str() + "_o");
			o_wire->port_output = true;
			wire->port_output = false;
			module->connect(o_wire, wire);
			outputs[i] = o_wire;
		}
	}

	// Parse footer (symbol table, comments, etc.)
	unsigned l1;
	std::string s;
	for (int c = f.peek(); c != EOF; c = f.peek(), ++line_count) {
		if (c == 'i' || c == 'l' || c == 'o' || c == 'b') {
			f.ignore(1);
			if (!(f >> l1 >> s))
				log_error("Line %u cannot be interpreted as a symbol entry!\n", line_count);

			if ((c == 'i' && l1 > inputs.size()) || (c == 'l' && l1 > latches.size()) || (c == 'o' && l1 > outputs.size()))
				log_error("Line %u has invalid symbol position!\n", line_count);

			RTLIL::Wire* wire;
			if (c == 'i') wire = inputs[l1];
			else if (c == 'l') wire = latches[l1];
			else if (c == 'o') wire = outputs[l1];
			else if (c == 'b') wire = bad_properties[l1];
			else log_abort();

			module->rename(wire, stringf("\\%s", s.c_str()));
		}
		else if (c == 'j' || c == 'f') {
			// TODO
		}
		else if (c == 'c') {
			f.ignore(1);
			if (f.peek() == '\n')
				break;
			// Else constraint (TODO)
		}
		else
			log_error("Line %u: cannot interpret first character '%c'!\n", line_count, c);
		std::getline(f, line); // Ignore up to start of next line
	}

	module->fixup_ports();
	design->add(module);
}

static RTLIL::Wire* createWireIfNotExists(RTLIL::Module *module, unsigned literal)
{
	const unsigned variable = literal >> 1;
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
	module->addNotGate(stringf("\\n%d_not", variable), wire_inv, wire); // FIXME: is "_not" the right suffix?

	return wire;
}

void AigerReader::parse_aiger_ascii()
{
	std::string line;
	std::stringstream ss;

	unsigned l1, l2, l3;

	// Parse inputs
	for (unsigned i = 1; i <= I; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as an input!\n", line_count);
		log_debug("%d is an input\n", l1);
		log_assert(!(l1 & 1)); // TODO: Inputs can't be inverted?
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_input = true;
		inputs.push_back(wire);
	}

	// Parse latches
	RTLIL::Wire *clk_wire = nullptr;
	if (L > 0) {
		clk_wire = module->wire(clk_name);
		log_assert(!clk_wire);
		log_debug("Creating %s\n", clk_name.c_str());
		clk_wire = module->addWire(clk_name);
		clk_wire->port_input = true;
	}
	for (unsigned i = 0; i < L; ++i, ++line_count) {
		if (!(f >> l1 >> l2))
			log_error("Line %u cannot be interpreted as a latch!\n", line_count);
		log_debug("%d %d is a latch\n", l1, l2);
		log_assert(!(l1 & 1)); // TODO: Latch outputs can't be inverted?
		RTLIL::Wire *q_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *d_wire = createWireIfNotExists(module, l2);

		module->addDffGate(NEW_ID, clk_wire, d_wire, q_wire);

		// Reset logic is optional in AIGER 1.9
		if (f.peek() == ' ') {
			if (!(f >> l3))
				log_error("Line %u cannot be interpreted as a latch!\n", line_count);

			if (l3 == 0)
				q_wire->attributes["\\init"] = RTLIL::S0;
			else if (l3 == 1)
				q_wire->attributes["\\init"] = RTLIL::S1;
			else if (l3 == l1) {
				//q_wire->attributes["\\init"] = RTLIL::Const(RTLIL::State::Sx);
			}
			else
				log_error("Line %u has invalid reset literal for latch!\n", line_count);
		}
		else {
			// AIGER latches are assumed to be initialized to zero
			q_wire->attributes["\\init"] = RTLIL::S0;
		}
		latches.push_back(q_wire);
	}

	// Parse outputs
	for (unsigned i = 0; i < O; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as an output!\n", line_count);

		log_debug("%d is an output\n", l1);
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_output = true;
		outputs.push_back(wire);
	}

	// Parse bad properties
	for (unsigned i = 0; i < B; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as a bad state property!\n", line_count);

		log_debug("%d is a bad state property\n", l1);
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_output = true;
		bad_properties.push_back(wire);
	}

	// TODO: Parse invariant constraints
	for (unsigned i = 0; i < C; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// TODO: Parse justice properties
	for (unsigned i = 0; i < J; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// TODO: Parse fairness constraints
	for (unsigned i = 0; i < F; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// Parse AND
	for (unsigned i = 0; i < A; ++i) {
		if (!(f >> l1 >> l2 >> l3))
			log_error("Line %u cannot be interpreted as an AND!\n", line_count);

		log_debug("%d %d %d is an AND\n", l1, l2, l3);
		log_assert(!(l1 & 1)); // TODO: Output of ANDs can't be inverted?
		RTLIL::Wire *o_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *i1_wire = createWireIfNotExists(module, l2);
		RTLIL::Wire *i2_wire = createWireIfNotExists(module, l3);
		module->addAndGate(NEW_ID, i1_wire, i2_wire, o_wire);
	}
	std::getline(f, line); // Ignore up to start of next line
}

static unsigned parse_next_delta_literal(std::istream &f, unsigned ref)
{
	unsigned x = 0, i = 0;
	unsigned char ch;
	while ((ch = f.get()) & 0x80)
		x |= (ch & 0x7f) << (7 * i++);
	return ref - (x | (ch << (7 * i)));
}

void AigerReader::parse_aiger_binary()
{
	unsigned l1, l2, l3;
	std::string line;

	// Parse inputs
	for (unsigned i = 1; i <= I; ++i) {
		RTLIL::Wire *wire = createWireIfNotExists(module, i << 1);
		wire->port_input = true;
		inputs.push_back(wire);
	}

	// Parse latches
	RTLIL::Wire *clk_wire = nullptr;
	if (L > 0) {
		clk_wire = module->wire(clk_name);
		log_assert(!clk_wire);
		log_debug("Creating %s\n", clk_name.c_str());
		clk_wire = module->addWire(clk_name);
		clk_wire->port_input = true;
	}
	l1 = (I+1) * 2;
	for (unsigned i = 0; i < L; ++i, ++line_count, l1 += 2) {
		if (!(f >> l2))
			log_error("Line %u cannot be interpreted as a latch!\n", line_count);
		log_debug("%d %d is a latch\n", l1, l2);
		RTLIL::Wire *q_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *d_wire = createWireIfNotExists(module, l2);

		module->addDff(NEW_ID, clk_wire, d_wire, q_wire);

		// Reset logic is optional in AIGER 1.9
		if (f.peek() == ' ') {
			if (!(f >> l3))
				log_error("Line %u cannot be interpreted as a latch!\n", line_count);

			if (l3 == 0)
				q_wire->attributes["\\init"] = RTLIL::S0;
			else if (l3 == 1)
				q_wire->attributes["\\init"] = RTLIL::S1;
			else if (l3 == l1) {
				//q_wire->attributes["\\init"] = RTLIL::Const(RTLIL::State::Sx);
			}
			else
				log_error("Line %u has invalid reset literal for latch!\n", line_count);
		}
		else {
			// AIGER latches are assumed to be initialized to zero
			q_wire->attributes["\\init"] = RTLIL::S0;
		}
		latches.push_back(q_wire);
	}

	// Parse outputs
	for (unsigned i = 0; i < O; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as an output!\n", line_count);

		log_debug("%d is an output\n", l1);
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_output = true;
		outputs.push_back(wire);
	}
	std::getline(f, line); // Ignore up to start of next line

	// Parse bad properties
	for (unsigned i = 0; i < B; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as a bad state property!\n", line_count);

		log_debug("%d is a bad state property\n", l1);
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_output = true;
		bad_properties.push_back(wire);
	}
	if (B > 0)
		std::getline(f, line); // Ignore up to start of next line

	// TODO: Parse invariant constraints
	for (unsigned i = 0; i < C; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// TODO: Parse justice properties
	for (unsigned i = 0; i < J; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// TODO: Parse fairness constraints
	for (unsigned i = 0; i < F; ++i, ++line_count)
		std::getline(f, line); // Ignore up to start of next line

	// Parse AND
	l1 = (I+L+1) << 1;
	for (unsigned i = 0; i < A; ++i, ++line_count, l1 += 2) {
		l2 = parse_next_delta_literal(f, l1);
		l3 = parse_next_delta_literal(f, l2);

		log_debug("%d %d %d is an AND\n", l1, l2, l3);
		log_assert(!(l1 & 1)); // TODO: Output of ANDs can't be inverted?
		RTLIL::Wire *o_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *i1_wire = createWireIfNotExists(module, l2);
		RTLIL::Wire *i2_wire = createWireIfNotExists(module, l3);

		RTLIL::Cell *and_cell = module->addCell(NEW_ID, "$_AND_");
		and_cell->setPort("\\A", i1_wire);
		and_cell->setPort("\\B", i2_wire);
		and_cell->setPort("\\Y", o_wire);
	}
}

struct AigerFrontend : public Frontend {
	AigerFrontend() : Frontend("aiger", "read AIGER file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_aiger [options] [filename]\n");
		log("\n");
		log("Load module from an AIGER file into the current design.\n");
		log("\n");
		log("    -module_name <module_name>\n");
		log("        Name of module to be created (default: "
#ifdef _WIN32
				"top" // FIXME
#else
				"<filename>"
#endif
				")\n");
		log("\n");
		log("    -clk_name <wire_name>\n");
		log("        AIGER latches to be transformed into posedge DFFs clocked by wire of");
		log("        this name (default: clk)\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing AIGER frontend.\n");

		RTLIL::IdString clk_name = "\\clk";
		RTLIL::IdString module_name;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-module_name" && argidx+1 < args.size()) {
				module_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (arg == "-clk_name" && argidx+1 < args.size()) {
				clk_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (module_name.empty()) {
#ifdef _WIN32
			module_name = "top"; // FIXME: basename equivalent on Win32?
#else
			char* bn = strdup(filename.c_str());
			module_name = RTLIL::escape_id(bn);
			free(bn);
#endif
		}

		AigerReader reader(design, *f, module_name, clk_name);
		reader.parse_aiger();
	}
} AigerFrontend;

YOSYS_NAMESPACE_END
