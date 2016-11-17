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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/cellaigs.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

pool<string> used_names;
dict<IdString, string> namecache;
int autoid_counter;

string next_id()
{
	string new_id;

	while (1) {
		new_id = stringf("_%d", autoid_counter++);
		if (used_names.count(new_id) == 0) break;
	}

	used_names.insert(new_id);
	return new_id;
}

const char *make_id(IdString id)
{
	if (namecache.count(id) != 0)
		return namecache.at(id).c_str();

	string new_id = log_id(id);

	for (int i = 0; i < GetSize(new_id); i++)
	{
		char &ch = new_id[i];
		if ('a' <= ch && ch <= 'z') continue;
		if ('A' <= ch && ch <= 'Z') continue;
		if ('0' <= ch && ch <= '9' && i != 0) continue;
		if ('_' == ch) continue;
		ch = '_';
	}

	while (used_names.count(new_id) != 0)
		new_id += '_';

	namecache[id] = new_id;
	used_names.insert(new_id);
	return namecache.at(id).c_str();
}

struct FirrtlWorker
{
	Module *module;
	std::ostream &f;

	dict<SigBit, pair<string, int>> reverse_wire_map;
	string unconn_id;

	void register_reverse_wire_map(string id, SigSpec sig)
	{
		for (int i = 0; i < GetSize(sig); i++)
			reverse_wire_map[sig[i]] = make_pair(id, i);
	}

	FirrtlWorker(Module *module, std::ostream &f) : module(module), f(f)
	{
	}

	string make_expr(SigSpec sig)
	{
		string expr;

		for (auto chunk : sig.chunks())
		{
			string new_expr;

			if (chunk.wire == nullptr)
			{
				std::vector<RTLIL::State> bits = chunk.data;
				new_expr = stringf("UInt<%d>(\"h", GetSize(bits));

				while (GetSize(bits) % 4 != 0)
					bits.push_back(State::S0);

				for (int i = GetSize(bits)-4; i >= 0; i -= 4)
				{
					int val = 0;
					if (bits[i+0] == State::S1) val += 1;
					if (bits[i+1] == State::S1) val += 2;
					if (bits[i+2] == State::S1) val += 4;
					if (bits[i+3] == State::S1) val += 8;
					new_expr.push_back(val < 10 ? '0' + val : 'a' + val - 10);
				}

				new_expr += "\")";
			}
			else if (chunk.offset == 0 && chunk.width == chunk.wire->width)
			{
				new_expr = make_id(chunk.wire->name);
			}
			else
			{
				string wire_id = make_id(chunk.wire->name);
				new_expr = stringf("bits(%s, %d, %d)", wire_id.c_str(), chunk.offset + chunk.width - 1, chunk.offset);
			}

			if (expr.empty())
				expr = new_expr;
			else
				expr = "cat(" + new_expr + ", " + expr + ")";
		}

		return expr;
	}

	void run()
	{
		f << stringf("  module %s:\n", make_id(module->name));
		vector<string> port_decls, wire_decls, cell_exprs, wire_exprs;

		for (auto wire : module->wires())
		{
			if (wire->port_id)
			{
				if (wire->port_input && wire->port_output)
					log_error("Module port %s.%s is inout!\n", log_id(module), log_id(wire));
				port_decls.push_back(stringf("    %s %s: UInt<%d>\n", wire->port_input ? "input" : "output",
						make_id(wire->name), wire->width));
			}
			else
			{
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", make_id(wire->name), wire->width));
			}
		}

		for (auto cell : module->cells())
		{
			if (cell->type.in("$add", "$sub", "$xor"))
			{
				string y_id = make_id(cell->name);
				bool is_signed = cell->parameters.at("\\A_SIGNED").as_bool();
				int y_width =  cell->parameters.at("\\Y_WIDTH").as_int();
				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (is_signed) {
					a_expr = "asSInt(" + a_expr + ")";
					b_expr = "asSInt(" + b_expr + ")";
				}

				a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);
				b_expr = stringf("pad(%s, %d)", b_expr.c_str(), y_width);

				string primop;
				if (cell->type == "$add") primop = "add";
				if (cell->type == "$sub") primop = "sub";
				if (cell->type == "$xor") primop = "xor";

				string expr = stringf("%s(%s, %s)", primop.c_str(), a_expr.c_str(), b_expr.c_str());

				if ((is_signed && !cell->type.in("$xor")) || cell->type.in("$sub"))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}

			if (cell->type.in("$dff"))
			{
				bool clkpol = cell->parameters.at("\\CLK_POLARITY").as_bool();
				if (clkpol == false)
					log_error("Negative edge clock on FF %s.%s.\n", log_id(module), log_id(cell));

				string q_id = make_id(cell->name);
				int width = cell->parameters.at("\\WIDTH").as_int();
				string expr = make_expr(cell->getPort("\\D"));
				string clk_expr = "asClock(" + make_expr(cell->getPort("\\CLK")) + ")";

				wire_decls.push_back(stringf("    reg %s: UInt<%d>, %s\n", q_id.c_str(), width, clk_expr.c_str()));

				cell_exprs.push_back(stringf("    %s <= %s\n", q_id.c_str(), expr.c_str()));
				register_reverse_wire_map(q_id, cell->getPort("\\Q"));

				continue;
			}

			log_error("Cell type not supported: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
		}

		for (auto conn : module->connections())
		{
			string y_id = next_id();
			int y_width =  GetSize(conn.first);
			string expr = make_expr(conn.second);

			wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));
			cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
			register_reverse_wire_map(y_id, conn.first);
		}

		for (auto wire : module->wires())
		{
			string expr;

			if (wire->port_input)
				continue;

			int cursor = 0;
			bool is_valid = false;
			bool make_unconn_id = false;

			while (cursor < wire->width)
			{
				int chunk_width = 1;
				string new_expr;

				SigBit start_bit(wire, cursor);

				if (reverse_wire_map.count(start_bit))
				{
					pair<string, int> start_map = reverse_wire_map.at(start_bit);

					while (cursor+chunk_width < wire->width)
					{
						SigBit stop_bit(wire, cursor+chunk_width);

						if (reverse_wire_map.count(stop_bit) == 0)
							break;

						pair<string, int> stop_map = reverse_wire_map.at(stop_bit);
						stop_map.second -= chunk_width;

						if (start_map != stop_map)
							break;

						chunk_width++;
					}

					new_expr = stringf("bits(%s, %d, %d)", start_map.first.c_str(),
							start_map.second + chunk_width - 1, start_map.second);
					is_valid = true;
				}
				else
				{
					if (unconn_id.empty()) {
						unconn_id = next_id();
						make_unconn_id = true;
					}
					new_expr = unconn_id;
				}

				if (expr.empty())
					expr = new_expr;
				else
					expr = "cat(" + new_expr + ", " + expr + ")";

				cursor += chunk_width;
			}

			if (is_valid) {
				if (make_unconn_id) {
					wire_decls.push_back(stringf("    wire %s: UInt<1>\n", unconn_id.c_str()));
					cell_exprs.push_back(stringf("    %s is invalid\n", unconn_id.c_str()));
				}
				wire_exprs.push_back(stringf("    %s <= %s\n", make_id(wire->name), expr.c_str()));
			} else {
				if (make_unconn_id) {
					unconn_id.clear();
				}
				wire_exprs.push_back(stringf("    %s is invalid\n", make_id(wire->name)));
			}
		}

		for (auto str : port_decls)
			f << str;

		f << stringf("\n");

		for (auto str : wire_decls)
			f << str;

		f << stringf("\n");

		for (auto str : cell_exprs)
			f << str;

		f << stringf("\n");

		for (auto str : wire_exprs)
			f << str;
	}
};

struct FirrtlBackend : public Backend {
	FirrtlBackend() : Backend("firrtl", "write design to a FIRRTL file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_firrtl [options] [filename]\n");
		log("\n");
		log("Write a FIRRTL netlist of the current design.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-aig") {
			// 	aig_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		log_header(design, "Executing FIRRTL backend.\n");

		Module *top = design->top_module();

		if (top == nullptr)
			log_error("No top module found!\n");

		namecache.clear();
		autoid_counter = 0;

		for (auto module : design->modules()) {
			make_id(module->name);
			for (auto wire : module->wires())
				if (wire->port_id)
					make_id(wire->name);
		}

		*f << stringf("circuit %s:\n", make_id(top->name));

		for (auto module : design->modules())
		{
			FirrtlWorker worker(module, *f);
			worker.run();
		}

		namecache.clear();
		autoid_counter = 0;
	}
} FirrtlBackend;

PRIVATE_NAMESPACE_END
