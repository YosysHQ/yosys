/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung <eddie@fpgeh.com>
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

// https://stackoverflow.com/a/46137633
#ifdef _MSC_VER
#include <stdlib.h>
#define __builtin_bswap32 _byteswap_ulong
#elif defined(__APPLE__)
#include <libkern/OSByteOrder.h>
#define __builtin_bswap32 OSSwapInt32
#endif
#define __STDC_FORMAT_MACROS
#include <inttypes.h>

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "aigerparse.h"

YOSYS_NAMESPACE_BEGIN

inline int32_t from_big_endian(int32_t i32) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
	return __builtin_bswap32(i32);
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
	return i32;
#else
#error "Unknown endianness"
#endif
}

#define log_debug2(...) ;
//#define log_debug2(...) log_debug(__VA_ARGS__)

struct ConstEvalAig
{
	RTLIL::Module *module;
	dict<RTLIL::SigBit, RTLIL::State> values_map;
	dict<RTLIL::SigBit, RTLIL::Cell*> sig2driver;
	dict<SigBit, pool<RTLIL::SigBit>> sig2deps;

	ConstEvalAig(RTLIL::Module *module) : module(module)
	{
		for (auto &it : module->cells_) {
			if (!yosys_celltypes.cell_known(it.second->type))
				continue;
			for (auto &it2 : it.second->connections())
				if (yosys_celltypes.cell_output(it.second->type, it2.first)) {
					auto r YS_ATTRIBUTE(unused) = sig2driver.insert(std::make_pair(it2.second, it.second));
					log_assert(r.second);
				}
		}
	}

	void clear()
	{
		values_map.clear();
		sig2deps.clear();
	}

	void set(RTLIL::SigBit sig, RTLIL::State value)
	{
		auto it = values_map.find(sig);
#ifndef NDEBUG
		if (it != values_map.end()) {
			RTLIL::State current_val = it->second;
			log_assert(current_val == value);
		}
#endif
		if (it != values_map.end())
			it->second = value;
		else
			values_map[sig] = value;
	}

	void set_incremental(RTLIL::SigSpec sig, RTLIL::Const value)
	{
		log_assert(GetSize(sig) == GetSize(value));

		for (int i = 0; i < GetSize(sig); i++) {
			auto it = values_map.find(sig[i]);
			if (it != values_map.end()) {
				RTLIL::State current_val = it->second;
				if (current_val != value[i])
					for (auto dep : sig2deps[sig[i]])
						values_map.erase(dep);
				it->second = value[i];
			}
			else
				values_map[sig[i]] = value[i];
		}
	}

	void compute_deps(RTLIL::SigBit output, const pool<RTLIL::SigBit> &inputs)
	{
		sig2deps[output].insert(output);

		RTLIL::Cell *cell = sig2driver.at(output);
		RTLIL::SigBit sig_a = cell->getPort("\\A");
		sig2deps[sig_a].reserve(sig2deps[sig_a].size() + sig2deps[output].size()); // Reserve so that any invalidation
											   // that may occur does so here, and
											   // not mid insertion (below)
		sig2deps[sig_a].insert(sig2deps[output].begin(), sig2deps[output].end());
		if (!inputs.count(sig_a))
			compute_deps(sig_a, inputs);

		if (cell->type == "$_AND_") {
			RTLIL::SigSpec sig_b = cell->getPort("\\B");
			sig2deps[sig_b].reserve(sig2deps[sig_b].size() + sig2deps[output].size()); // Reserve so that any invalidation
												   // that may occur does so here, and
												   // not mid insertion (below)
			sig2deps[sig_b].insert(sig2deps[output].begin(), sig2deps[output].end());

			if (!inputs.count(sig_b))
				compute_deps(sig_b, inputs);
		}
		else if (cell->type == "$_NOT_") {
		}
		else log_abort();
	}

	bool eval(RTLIL::Cell *cell)
	{
		RTLIL::SigBit sig_y = cell->getPort("\\Y");
		if (values_map.count(sig_y))
			return true;

		RTLIL::SigBit sig_a = cell->getPort("\\A");
		if (!eval(sig_a))
			return false;

		RTLIL::State eval_ret = RTLIL::Sx;
		if (cell->type == "$_NOT_") {
			if (sig_a == State::S0) eval_ret = State::S1;
			else if (sig_a == State::S1) eval_ret = State::S0;
		}
		else if (cell->type == "$_AND_") {
			if (sig_a == State::S0) {
				eval_ret = State::S0;
				goto eval_end;
			}

			{
				RTLIL::SigBit sig_b = cell->getPort("\\B");
				if (!eval(sig_b))
					return false;
				if (sig_b == State::S0) {
					eval_ret = State::S0;
					goto eval_end;
				}

				if (sig_a != State::S1 || sig_b != State::S1)
					goto eval_end;

				eval_ret = State::S1;
			}
		}
		else log_abort();

eval_end:
		set(sig_y, eval_ret);
		return true;
	}

	bool eval(RTLIL::SigBit &sig)
	{
		auto it = values_map.find(sig);
		if (it != values_map.end()) {
			sig = it->second;
			return true;
		}

		RTLIL::Cell *cell = sig2driver.at(sig);
		if (!eval(cell))
			return false;

		it = values_map.find(sig);
		if (it != values_map.end()) {
			sig = it->second;
			return true;
		}

		return false;
	}
};

AigerReader::AigerReader(RTLIL::Design *design, std::istream &f, RTLIL::IdString module_name, RTLIL::IdString clk_name, std::string map_filename, bool wideports)
	: design(design), f(f), clk_name(clk_name), map_filename(map_filename), wideports(wideports)
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
	piNum = 0;
	flopNum = 0;

	if (header == "aag")
		parse_aiger_ascii();
	else if (header == "aig")
		parse_aiger_binary();
	else
		log_abort();

	RTLIL::Wire* n0 = module->wire("\\__0__");
	if (n0)
		module->connect(n0, State::S0);

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

	post_process();
}

static uint32_t parse_xaiger_literal(std::istream &f)
{
	uint32_t l;
	f.read(reinterpret_cast<char*>(&l), sizeof(l));
	if (f.gcount() != sizeof(l))
#if defined(_WIN32) && defined(__MINGW32__)
		log_error("Offset %I64d: unable to read literal!\n", static_cast<int64_t>(f.tellg()));
#else
		log_error("Offset %" PRId64 ": unable to read literal!\n", static_cast<int64_t>(f.tellg()));
#endif
	return from_big_endian(l);
}

static RTLIL::Wire* createWireIfNotExists(RTLIL::Module *module, unsigned literal)
{
	const unsigned variable = literal >> 1;
	const bool invert = literal & 1;
	RTLIL::IdString wire_name(stringf("\\__%d%s__", variable, invert ? "b" : ""));
	RTLIL::Wire *wire = module->wire(wire_name);
	if (wire) return wire;
	log_debug2("Creating %s\n", wire_name.c_str());
	wire = module->addWire(wire_name);
	wire->port_input = wire->port_output = false;
	if (!invert) return wire;
	RTLIL::IdString wire_inv_name(stringf("\\__%d__", variable));
	RTLIL::Wire *wire_inv = module->wire(wire_inv_name);
	if (wire_inv) {
		if (module->cell(wire_inv_name)) return wire;
	}
	else {
		log_debug2("Creating %s\n", wire_inv_name.c_str());
		wire_inv = module->addWire(wire_inv_name);
		wire_inv->port_input = wire_inv->port_output = false;
	}

	log_debug2("Creating %s = ~%s\n", wire_name.c_str(), wire_inv_name.c_str());
	module->addNotGate(stringf("\\__%d__$not", variable), wire_inv, wire);

	return wire;
}

void AigerReader::parse_xaiger(const dict<int,IdString> &box_lookup)
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

	std::string line;
	std::getline(f, line); // Ignore up to start of next line, as standard
	// says anything that follows could be used for
	// optional sections

	log_debug("M=%u I=%u L=%u O=%u A=%u\n", M, I, L, O, A);

	line_count = 1;
	piNum = 0;
	flopNum = 0;

	if (header == "aag")
		parse_aiger_ascii();
	else if (header == "aig")
		parse_aiger_binary();
	else
		log_abort();

	RTLIL::Wire* n0 = module->wire("\\__0__");
	if (n0)
		module->connect(n0, State::S0);

	// Parse footer (symbol table, comments, etc.)
	std::string s;
	bool comment_seen = false;
	for (int c = f.peek(); c != EOF; c = f.peek()) {
		if (comment_seen || c == 'c') {
			if (!comment_seen) {
				f.ignore(1);
				c = f.peek();
				comment_seen = true;
			}
			if (c == '\n')
				break;
			f.ignore(1);
			// XAIGER extensions
			if (c == 'm') {
				uint32_t dataSize YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				uint32_t lutNum = parse_xaiger_literal(f);
				uint32_t lutSize YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				log_debug("m: dataSize=%u lutNum=%u lutSize=%u\n", dataSize, lutNum, lutSize);
				ConstEvalAig ce(module);
				for (unsigned i = 0; i < lutNum; ++i) {
					uint32_t rootNodeID = parse_xaiger_literal(f);
					uint32_t cutLeavesM = parse_xaiger_literal(f);
					log_debug2("rootNodeID=%d cutLeavesM=%d\n", rootNodeID, cutLeavesM);
					RTLIL::Wire *output_sig = module->wire(stringf("\\__%d__", rootNodeID));
					uint32_t nodeID;
					RTLIL::SigSpec input_sig;
					for (unsigned j = 0; j < cutLeavesM; ++j) {
						nodeID = parse_xaiger_literal(f);
						log_debug2("\t%u\n", nodeID);
						RTLIL::Wire *wire = module->wire(stringf("\\__%d__", nodeID));
						log_assert(wire);
						input_sig.append(wire);
					}
					// TODO: Compute LUT mask from AIG in less than O(2 ** input_sig.size())
					ce.clear();
					ce.compute_deps(output_sig, input_sig.to_sigbit_pool());
					RTLIL::Const lut_mask(RTLIL::State::Sx, 1 << input_sig.size());
					for (int j = 0; j < (1 << cutLeavesM); ++j) {
						int gray = j ^ (j >> 1);
						ce.set_incremental(input_sig, RTLIL::Const{gray, static_cast<int>(cutLeavesM)});
						RTLIL::SigBit o(output_sig);
						bool success YS_ATTRIBUTE(unused) = ce.eval(o);
						log_assert(success);
						log_assert(o.wire == nullptr);
						lut_mask[gray] = o.data;
					}
					RTLIL::Cell *output_cell = module->cell(stringf("\\__%d__$and", rootNodeID));
					log_assert(output_cell);
					module->remove(output_cell);
					module->addLut(stringf("\\__%d__$lut", rootNodeID), input_sig, output_sig, std::move(lut_mask));
				}
			}
			else if (c == 'r') {
				uint32_t dataSize YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				flopNum = parse_xaiger_literal(f);
				log_assert(dataSize == (flopNum+1) * sizeof(uint32_t));
				f.ignore(flopNum * sizeof(uint32_t));
			}
			else if (c == 'n') {
				parse_xaiger_literal(f);
				f >> s;
				log_debug("n: '%s'\n", s.c_str());
			}
			else if (c == 'h') {
				f.ignore(sizeof(uint32_t));
				uint32_t version YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				log_assert(version == 1);
				uint32_t ciNum YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				log_debug("ciNum = %u\n", ciNum);
				uint32_t coNum YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				log_debug("coNum = %u\n", coNum);
				piNum = parse_xaiger_literal(f);
				log_debug("piNum = %u\n", piNum);
				uint32_t poNum YS_ATTRIBUTE(unused) = parse_xaiger_literal(f);
				log_debug("poNum = %u\n", poNum);
				uint32_t boxNum = parse_xaiger_literal(f);
				log_debug("boxNum = %u\n", boxNum);
				for (unsigned i = 0; i < boxNum; i++) {
					f.ignore(2*sizeof(uint32_t));
					uint32_t boxUniqueId = parse_xaiger_literal(f);
					log_assert(boxUniqueId > 0);
					uint32_t oldBoxNum = parse_xaiger_literal(f);
					RTLIL::Cell* cell = module->addCell(stringf("$__box%u__", oldBoxNum), box_lookup.at(boxUniqueId));
					boxes.emplace_back(cell);
				}
			}
			else if (c == 'a' || c == 'i' || c == 'o') {
				uint32_t dataSize = parse_xaiger_literal(f);
				f.ignore(dataSize);
			}
			else {
				break;
			}
		}
		else
			log_error("Line %u: cannot interpret first character '%c'!\n", line_count, c);
	}

	post_process();
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
		log_debug2("%d is an input\n", l1);
		log_assert(!(l1 & 1)); // Inputs can't be inverted
		RTLIL::Wire *wire = createWireIfNotExists(module, l1);
		wire->port_input = true;
		inputs.push_back(wire);
	}

	// Parse latches
	RTLIL::Wire *clk_wire = nullptr;
	if (L > 0) {
		log_assert(clk_name != "");
		clk_wire = module->wire(clk_name);
		log_assert(!clk_wire);
		log_debug2("Creating %s\n", clk_name.c_str());
		clk_wire = module->addWire(clk_name);
		clk_wire->port_input = true;
		clk_wire->port_output = false;
	}
	for (unsigned i = 0; i < L; ++i, ++line_count) {
		if (!(f >> l1 >> l2))
			log_error("Line %u cannot be interpreted as a latch!\n", line_count);
		log_debug2("%d %d is a latch\n", l1, l2);
		log_assert(!(l1 & 1));
		RTLIL::Wire *q_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *d_wire = createWireIfNotExists(module, l2);

		module->addDffGate(NEW_ID, clk_wire, d_wire, q_wire);

		// Reset logic is optional in AIGER 1.9
		if (f.peek() == ' ') {
			if (!(f >> l3))
				log_error("Line %u cannot be interpreted as a latch!\n", line_count);

			if (l3 == 0)
				q_wire->attributes["\\init"] = State::S0;
			else if (l3 == 1)
				q_wire->attributes["\\init"] = State::S1;
			else if (l3 == l1) {
				//q_wire->attributes["\\init"] = RTLIL::Sx;
			}
			else
				log_error("Line %u has invalid reset literal for latch!\n", line_count);
		}
		else {
			// AIGER latches are assumed to be initialized to zero
			q_wire->attributes["\\init"] = State::S0;
		}
		latches.push_back(q_wire);
	}

	// Parse outputs
	for (unsigned i = 0; i < O; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as an output!\n", line_count);

		log_debug2("%d is an output\n", l1);
		const unsigned variable = l1 >> 1;
		const bool invert = l1 & 1;
		RTLIL::IdString wire_name(stringf("\\__%d%s__", variable, invert ? "b" : "")); // FIXME: is "b" the right suffix?
		RTLIL::Wire *wire = module->wire(wire_name);
		if (!wire)
			wire = createWireIfNotExists(module, l1);
		else if (wire->port_input || wire->port_output) {
			RTLIL::Wire *new_wire = module->addWire(NEW_ID);
			module->connect(new_wire, wire);
			wire = new_wire;
		}
		wire->port_output = true;
		outputs.push_back(wire);
	}

	// Parse bad properties
	for (unsigned i = 0; i < B; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as a bad state property!\n", line_count);

		log_debug2("%d is a bad state property\n", l1);
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

		log_debug2("%d %d %d is an AND\n", l1, l2, l3);
		log_assert(!(l1 & 1));
		RTLIL::Wire *o_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *i1_wire = createWireIfNotExists(module, l2);
		RTLIL::Wire *i2_wire = createWireIfNotExists(module, l3);
		module->addAndGate(o_wire->name.str() + "$and", i1_wire, i2_wire, o_wire);
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
		log_debug2("%d is an input\n", i);
		RTLIL::Wire *wire = createWireIfNotExists(module, i << 1);
		wire->port_input = true;
		log_assert(!wire->port_output);
		inputs.push_back(wire);
	}

	// Parse latches
	RTLIL::Wire *clk_wire = nullptr;
	if (L > 0) {
		log_assert(clk_name != "");
		clk_wire = module->wire(clk_name);
		log_assert(!clk_wire);
		log_debug2("Creating %s\n", clk_name.c_str());
		clk_wire = module->addWire(clk_name);
		clk_wire->port_input = true;
		clk_wire->port_output = false;
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
				q_wire->attributes["\\init"] = State::S0;
			else if (l3 == 1)
				q_wire->attributes["\\init"] = State::S1;
			else if (l3 == l1) {
				//q_wire->attributes["\\init"] = RTLIL::Sx;
			}
			else
				log_error("Line %u has invalid reset literal for latch!\n", line_count);
		}
		else {
			// AIGER latches are assumed to be initialized to zero
			q_wire->attributes["\\init"] = State::S0;
		}
		latches.push_back(q_wire);
	}

	// Parse outputs
	for (unsigned i = 0; i < O; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as an output!\n", line_count);

		log_debug2("%d is an output\n", l1);
		const unsigned variable = l1 >> 1;
		const bool invert = l1 & 1;
		RTLIL::IdString wire_name(stringf("\\__%d%s__", variable, invert ? "b" : "")); // FIXME: is "_b" the right suffix?
		RTLIL::Wire *wire = module->wire(wire_name);
		if (!wire)
			wire = createWireIfNotExists(module, l1);
		else if (wire->port_input || wire->port_output) {
			RTLIL::Wire *new_wire = module->addWire(NEW_ID);
			module->connect(new_wire, wire);
			wire = new_wire;
		}
		wire->port_output = true;
		outputs.push_back(wire);
	}
	std::getline(f, line); // Ignore up to start of next line

	// Parse bad properties
	for (unsigned i = 0; i < B; ++i, ++line_count) {
		if (!(f >> l1))
			log_error("Line %u cannot be interpreted as a bad state property!\n", line_count);

		log_debug2("%d is a bad state property\n", l1);
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

		log_debug2("%d %d %d is an AND\n", l1, l2, l3);
		log_assert(!(l1 & 1));
		RTLIL::Wire *o_wire = createWireIfNotExists(module, l1);
		RTLIL::Wire *i1_wire = createWireIfNotExists(module, l2);
		RTLIL::Wire *i2_wire = createWireIfNotExists(module, l3);
		module->addAndGate(o_wire->name.str() + "$and", i1_wire, i2_wire, o_wire);
	}
}

void AigerReader::post_process()
{
	pool<IdString> seen_boxes;
	unsigned ci_count = 0, co_count = 0;
	for (auto cell : boxes) {
		RTLIL::Module* box_module = design->module(cell->type);
		log_assert(box_module);

		if (seen_boxes.insert(cell->type).second) {
			auto it = box_module->attributes.find("\\abc_carry");
			if (it != box_module->attributes.end()) {
				RTLIL::Wire *carry_in = nullptr, *carry_out = nullptr;
				auto carry_in_out = it->second.decode_string();
				auto pos = carry_in_out.find(',');
				if (pos == std::string::npos)
					log_error("'abc_carry' attribute on module '%s' does not contain ','.\n", log_id(cell->type));
				auto carry_in_name = RTLIL::escape_id(carry_in_out.substr(0, pos));
				carry_in = box_module->wire(carry_in_name);
				if (!carry_in || !carry_in->port_input)
					log_error("'abc_carry' on module '%s' contains '%s' which does not exist or is not an input port.\n", log_id(cell->type), carry_in_name.c_str());

				auto carry_out_name = RTLIL::escape_id(carry_in_out.substr(pos+1));
				carry_out = box_module->wire(carry_out_name);
				if (!carry_out || !carry_out->port_output)
					log_error("'abc_carry' on module '%s' contains '%s' which does not exist or is not an output port.\n", log_id(cell->type), carry_out_name.c_str());

				auto &ports = box_module->ports;
				for (auto jt = ports.begin(); jt != ports.end(); ) {
					RTLIL::Wire* w = box_module->wire(*jt);
					log_assert(w);
					if (w == carry_in || w == carry_out) {
						jt = ports.erase(jt);
						continue;
					}
					if (w->port_id > carry_in->port_id)
						--w->port_id;
					if (w->port_id > carry_out->port_id)
						--w->port_id;
					log_assert(w->port_input || w->port_output);
					log_assert(ports[w->port_id-1] == w->name);
					++jt;
				}
				ports.push_back(carry_in->name);
				carry_in->port_id = ports.size();
				ports.push_back(carry_out->name);
				carry_out->port_id = ports.size();
			}
		}

		// NB: Assume box_module->ports are sorted alphabetically
		//     (as RTLIL::Module::fixup_ports() would do)
		for (auto port_name : box_module->ports) {
			RTLIL::Wire* w = box_module->wire(port_name);
			log_assert(w);
			RTLIL::SigSpec rhs;
			RTLIL::Wire* wire = nullptr;
			for (int i = 0; i < GetSize(w); i++) {
				if (w->port_input) {
					log_assert(co_count < outputs.size());
					wire = outputs[co_count++];
					log_assert(wire);
					log_assert(wire->port_output);
					wire->port_output = false;
				}
				if (w->port_output) {
					log_assert((piNum + ci_count) < inputs.size());
					wire = inputs[piNum + ci_count++];
					log_assert(wire);
					log_assert(wire->port_input);
					wire->port_input = false;
				}
				rhs.append(wire);
			}
			cell->setPort(port_name, rhs);
		}
	}

	dict<RTLIL::IdString, int> wideports_cache;

	if (!map_filename.empty()) {
		std::ifstream mf(map_filename);
		std::string type, symbol;
		int variable, index;
		while (mf >> type >> variable >> index >> symbol) {
			RTLIL::IdString escaped_s = RTLIL::escape_id(symbol);
			if (type == "input") {
				log_assert(static_cast<unsigned>(variable) < inputs.size());
				RTLIL::Wire* wire = inputs[variable];
				log_assert(wire);
				log_assert(wire->port_input);

				if (index == 0) {
					// Cope with the fact that a CI might be identical
					// to a PI (necessary due to ABC); in those cases
					// simply connect the latter to the former
					RTLIL::Wire* existing = module->wire(escaped_s);
					if (!existing)
						module->rename(wire, escaped_s);
					else {
						wire->port_input = false;
						module->connect(wire, existing);
					}
				}
				else if (index > 0) {
					std::string indexed_name = stringf("%s[%d]", escaped_s.c_str(), index);
					RTLIL::Wire* existing = module->wire(indexed_name);
					if (!existing) {
						module->rename(wire, indexed_name);
						if (wideports)
							wideports_cache[escaped_s] = std::max(wideports_cache[escaped_s], index);
					}
					else {
						module->connect(wire, existing);
						wire->port_input = false;
					}
				}
			}
			else if (type == "output") {
				log_assert(static_cast<unsigned>(variable + co_count) < outputs.size());
				RTLIL::Wire* wire = outputs[variable + co_count];
				log_assert(wire);
				log_assert(wire->port_output);
				if (escaped_s == "$__dummy__") {
					wire->port_output = false;
					continue;
				}

				if (index == 0) {
					// Cope with the fact that a CO might be identical
					// to a PO (necessary due to ABC); in those cases
					// simply connect the latter to the former
					RTLIL::Wire* existing = module->wire(escaped_s);
					if (!existing) {
						if (escaped_s.ends_with("$inout.out")) {
							wire->port_output = false;
							RTLIL::Wire *in_wire = module->wire(escaped_s.substr(0, escaped_s.size()-10));
							log_assert(in_wire);
							log_assert(in_wire->port_input && !in_wire->port_output);
							in_wire->port_output = true;
							module->connect(in_wire, wire);
						}
						else
							module->rename(wire, escaped_s);
					}
					else {
						wire->port_output = false;
						module->connect(wire, existing);
					}
				}
				else if (index > 0) {
					std::string indexed_name = stringf("%s[%d]", escaped_s.c_str(), index);
					RTLIL::Wire* existing = module->wire(indexed_name);
					if (!existing) {
						if (escaped_s.ends_with("$inout.out")) {
							wire->port_output = false;
							RTLIL::Wire *in_wire = module->wire(stringf("%s[%d]", escaped_s.substr(0, escaped_s.size()-10).c_str(), index));
							log_assert(in_wire);
							log_assert(in_wire->port_input && !in_wire->port_output);
							in_wire->port_output = true;
							module->connect(in_wire, wire);
						}
						else {
							module->rename(wire, indexed_name);
							if (wideports)
								wideports_cache[escaped_s] = std::max(wideports_cache[escaped_s], index);
						}
					}
					else {
						module->connect(wire, existing);
						wire->port_output = false;
					}
				}
			}
			else if (type == "box") {
				RTLIL::Cell* cell = module->cell(stringf("$__box%d__", variable));
				if (cell) { // ABC could have optimised this box away
					module->rename(cell, escaped_s);
					for (const auto &i : cell->connections()) {
						RTLIL::IdString port_name = i.first;
						RTLIL::SigSpec rhs = i.second;
						int index = 0;
						for (auto bit : rhs.bits()) {
							RTLIL::Wire* wire = bit.wire;
							RTLIL::IdString escaped_s = RTLIL::escape_id(stringf("%s.%s", log_id(cell), log_id(port_name)));
							if (index == 0)
								module->rename(wire, escaped_s);
							else if (index > 0) {
								module->rename(wire, stringf("%s[%d]", escaped_s.c_str(), index));
								if (wideports)
									wideports_cache[escaped_s] = std::max(wideports_cache[escaped_s], index);
							}
							index++;
						}
					}
				}
			}
			else
				log_error("Symbol type '%s' not recognised.\n", type.c_str());
		}
	}

	for (auto &wp : wideports_cache) {
		auto name = wp.first;
		int width = wp.second + 1;

		RTLIL::Wire *wire = module->wire(name);
		if (wire)
			module->rename(wire, RTLIL::escape_id(stringf("%s[%d]", name.c_str(), 0)));

		// Do not make ports with a mix of input/output into
		// wide ports
		bool port_input = false, port_output = false;
		for (int i = 0; i < width; i++) {
			RTLIL::IdString other_name = name.str() + stringf("[%d]", i);
			RTLIL::Wire *other_wire = module->wire(other_name);
			if (other_wire) {
				port_input = port_input || other_wire->port_input;
				port_output = port_output || other_wire->port_output;
			}
		}

		wire = module->addWire(name, width);
		wire->port_input = port_input;
		wire->port_output = port_output;

		for (int i = 0; i < width; i++) {
			RTLIL::IdString other_name = name.str() + stringf("[%d]", i);
			RTLIL::Wire *other_wire = module->wire(other_name);
			if (other_wire) {
				other_wire->port_input = false;
				other_wire->port_output = false;
			}
			if (wire->port_input) {
				if (other_wire)
					module->connect(other_wire, SigSpec(wire, i));
			}
			else {
								  // Since we skip POs that are connected to Sx,
								  // re-connect them here
				module->connect(SigSpec(wire, i), other_wire ? other_wire : SigSpec(RTLIL::Sx));
			}
		}
	}

	module->fixup_ports();

	// Insert into a new (temporary) design so that "clean" will only
	// operate (and run checks on) this one module
	RTLIL::Design *mapped_design = new RTLIL::Design;
	mapped_design->add(module);
	Pass::call(mapped_design, "clean");
	mapped_design->modules_.erase(module->name);
	delete mapped_design;

	design->add(module);

	for (auto cell : module->cells().to_vector()) {
		if (cell->type != "$lut") continue;
		auto y_port = cell->getPort("\\Y").as_bit();
		if (y_port.wire->width == 1)
			module->rename(cell, stringf("%s$lut", y_port.wire->name.c_str()));
		else
			module->rename(cell, stringf("%s[%d]$lut", y_port.wire->name.c_str(), y_port.offset));
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
		log("        Name of module to be created (default: <filename>)\n");
		log("\n");
		log("    -clk_name <wire_name>\n");
		log("        AIGER latches to be transformed into posedge DFFs clocked by wire of");
		log("        this name (default: clk)\n");
		log("\n");
		log("    -map <filename>\n");
		log("        read file with port and latch symbols\n");
		log("\n");
		log("    -wideports\n");
		log("        Merge ports that match the pattern 'name[int]' into a single\n");
		log("        multi-bit port 'name'.\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing AIGER frontend.\n");

		RTLIL::IdString clk_name = "\\clk";
		RTLIL::IdString module_name;
		std::string map_filename;
		bool wideports = false;

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
			if (map_filename.empty() && arg == "-map" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
			if (arg == "-wideports") {
				wideports = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (module_name.empty()) {
#ifdef _WIN32
			char fname[_MAX_FNAME];
			_splitpath(filename.c_str(), NULL /* drive */, NULL /* dir */, fname, NULL /* ext */);
			module_name = fname;
#else
			char* bn = strdup(filename.c_str());
			module_name = RTLIL::escape_id(bn);
			free(bn);
#endif
		}

		AigerReader reader(design, *f, module_name, clk_name, map_filename, wideports);
		reader.parse_aiger();
	}
} AigerFrontend;

YOSYS_NAMESPACE_END
