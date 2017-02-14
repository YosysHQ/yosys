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
			if (cell->type.in("$not", "$logic_not", "$neg", "$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_bool", "$reduce_xnor"))
			{
				string y_id = make_id(cell->name);
				bool is_signed = cell->parameters.at("\\A_SIGNED").as_bool();
				int y_width =  cell->parameters.at("\\Y_WIDTH").as_int();
				string a_expr = make_expr(cell->getPort("\\A"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (cell->parameters.at("\\A_SIGNED").as_bool()) {
					a_expr = "asSInt(" + a_expr + ")";
				}

				a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);

				string primop;
                                bool always_uint = false;
				if (cell->type == "$not") primop = "not";
				if (cell->type == "$neg") primop = "neg";
				if (cell->type == "$logic_not") {
                                        primop = "eq";
                                        a_expr = stringf("%s, UInt(0)", a_expr.c_str());
                                }
				if (cell->type == "$reduce_and") primop = "andr";
				if (cell->type == "$reduce_or") primop = "orr";
				if (cell->type == "$reduce_xor") primop = "xorr";
				if (cell->type == "$reduce_xnor") {
                                        primop = "not";
                                        a_expr = stringf("xorr(%s)", a_expr.c_str());
                                }
				if (cell->type == "$reduce_bool") {
                                        primop = "neq";
                                        a_expr = stringf("%s, UInt(0)", a_expr.c_str());
                                }

				string expr = stringf("%s(%s)", primop.c_str(), a_expr.c_str());

				if ((is_signed && !always_uint))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}
			if (cell->type.in("$add", "$sub", "$mul", "$div", "$mod", "$xor", "$and", "$or", "$eq", "$eqx",
                                        "$gt", "$ge", "$lt", "$le", "$ne", "$nex", "$shr", "$sshr", "$sshl", "$shl",
                                        "$logic_and", "$logic_or"))
			{
				string y_id = make_id(cell->name);
				bool is_signed = cell->parameters.at("\\A_SIGNED").as_bool();
				int y_width =  cell->parameters.at("\\Y_WIDTH").as_int();
				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), y_width));

				if (cell->parameters.at("\\A_SIGNED").as_bool()) {
					a_expr = "asSInt(" + a_expr + ")";
				}
				if (cell->parameters.at("\\A_SIGNED").as_bool()  & (cell->type != "$shr")) {
					b_expr = "asSInt(" + b_expr + ")";
				}

				a_expr = stringf("pad(%s, %d)", a_expr.c_str(), y_width);

				if ((cell->type != "$shl") && (cell->type != "$sshl")) {
				        b_expr = stringf("pad(%s, %d)", b_expr.c_str(), y_width);
                                }

				if (cell->parameters.at("\\A_SIGNED").as_bool()  & (cell->type == "$shr")) {
					a_expr = "asUInt(" + a_expr + ")";
				}

				string primop;
                                bool always_uint = false;
				if (cell->type == "$add") primop = "add";
				if (cell->type == "$sub") primop = "sub";
				if (cell->type == "$mul") primop = "mul";
				if (cell->type == "$div") primop = "div";
				if (cell->type == "$mod") primop = "rem";
				if (cell->type == "$and") {
                                        primop = "and";
                                        always_uint = true;
                                }
				if (cell->type == "$or" ) {
                                        primop =  "or";
                                        always_uint = true;
                                }
				if (cell->type == "$xor") {
                                        primop = "xor";
                                        always_uint = true;
                                }
				if ((cell->type == "$eq") | (cell->type == "$eqx")) {
                                        primop = "eq";
                                        always_uint = true;
                                }
				if ((cell->type == "$ne") | (cell->type == "$nex")) {
                                        primop = "neq";
                                        always_uint = true;
                                }
				if (cell->type == "$gt") {
                                        primop = "gt";
                                        always_uint = true;
                                }
				if (cell->type == "$ge") {
                                        primop = "geq";
                                        always_uint = true;
                                }
				if (cell->type == "$lt") {
                                        primop = "lt";
                                        always_uint = true;
                                }
				if (cell->type == "$le") {
                                        primop = "leq";
                                        always_uint = true;
                                }
				if ((cell->type == "$shl") | (cell->type == "$sshl")) primop = "dshl";
				if ((cell->type == "$shr") | (cell->type == "$sshr")) primop = "dshr";
				if ((cell->type == "$logic_and")) {
                                        primop = "and";
                                        a_expr = "neq(" + a_expr + ", UInt(0))";
                                        b_expr = "neq(" + b_expr + ", UInt(0))";
                                        always_uint = true;
                                }
				if ((cell->type == "$logic_or")) {
                                        primop = "or";
                                        a_expr = "neq(" + a_expr + ", UInt(0))";
                                        b_expr = "neq(" + b_expr + ", UInt(0))";
                                        always_uint = true;
                                }

				if (!cell->parameters.at("\\B_SIGNED").as_bool()) {
					b_expr = "asUInt(" + b_expr + ")";
				}

				string expr = stringf("%s(%s, %s)", primop.c_str(), a_expr.c_str(), b_expr.c_str());

				if ((is_signed && !always_uint) || cell->type.in("$sub"))
					expr = stringf("asUInt(%s)", expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}

			if (cell->type.in("$mux"))
			{
				string y_id = make_id(cell->name);
				int width = cell->parameters.at("\\WIDTH").as_int();
				string a_expr = make_expr(cell->getPort("\\A"));
				string b_expr = make_expr(cell->getPort("\\B"));
				string s_expr = make_expr(cell->getPort("\\S"));
				wire_decls.push_back(stringf("    wire %s: UInt<%d>\n", y_id.c_str(), width));

				string expr = stringf("mux(%s, %s, %s)", s_expr.c_str(), b_expr.c_str(), a_expr.c_str());

				cell_exprs.push_back(stringf("    %s <= %s\n", y_id.c_str(), expr.c_str()));
				register_reverse_wire_map(y_id, cell->getPort("\\Y"));

				continue;
			}

			if (cell->type.in("$mem"))
			{
				string mem_id = make_id(cell->name);
				int abits = cell->parameters.at("\\ABITS").as_int();
				int width = cell->parameters.at("\\WIDTH").as_int();
				int size = cell->parameters.at("\\SIZE").as_int();
				int rd_ports = cell->parameters.at("\\RD_PORTS").as_int();
				int wr_ports = cell->parameters.at("\\WR_PORTS").as_int();

				Const initdata = cell->parameters.at("\\INIT");
				for (State bit : initdata.bits)
					if (bit != State::Sx)
						log_error("Memory with initialization data: %s.%s\n", log_id(module), log_id(cell));

				Const rd_clk_enable = cell->parameters.at("\\RD_CLK_ENABLE");
				Const wr_clk_enable = cell->parameters.at("\\WR_CLK_ENABLE");
				Const wr_clk_polarity = cell->parameters.at("\\WR_CLK_POLARITY");

				int offset = cell->parameters.at("\\OFFSET").as_int();
				if (offset != 0)
					log_error("Memory with nonzero offset: %s.%s\n", log_id(module), log_id(cell));

				cell_exprs.push_back(stringf("    mem %s:\n", mem_id.c_str()));
				cell_exprs.push_back(stringf("      data-type => UInt<%d>\n", width));
				cell_exprs.push_back(stringf("      depth => %d\n", size));

				for (int i = 0; i < rd_ports; i++)
					cell_exprs.push_back(stringf("      reader => r%d\n", i));

				for (int i = 0; i < wr_ports; i++)
					cell_exprs.push_back(stringf("      writer => w%d\n", i));

				cell_exprs.push_back(stringf("      read-latency => 0\n"));
				cell_exprs.push_back(stringf("      write-latency => 1\n"));
				cell_exprs.push_back(stringf("      read-under-write => undefined\n"));

				for (int i = 0; i < rd_ports; i++)
				{
					if (rd_clk_enable[i] != State::S0)
						log_error("Clocked read port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					SigSpec data_sig = cell->getPort("\\RD_DATA").extract(i*width, width);
					string addr_expr = make_expr(cell->getPort("\\RD_ADDR").extract(i*abits, abits));

					cell_exprs.push_back(stringf("    %s.r%d.addr <= %s\n", mem_id.c_str(), i, addr_expr.c_str()));
					cell_exprs.push_back(stringf("    %s.r%d.en <= UInt<1>(1)\n", mem_id.c_str(), i));
					cell_exprs.push_back(stringf("    %s.r%d.clk <= asClock(UInt<1>(0))\n", mem_id.c_str(), i));

					register_reverse_wire_map(stringf("%s.r%d.data", mem_id.c_str(), i), data_sig);
				}

				for (int i = 0; i < wr_ports; i++)
				{
					if (wr_clk_enable[i] != State::S1)
						log_error("Unclocked write port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					if (wr_clk_polarity[i] != State::S1)
						log_error("Negedge write port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					string addr_expr = make_expr(cell->getPort("\\WR_ADDR").extract(i*abits, abits));
					string data_expr = make_expr(cell->getPort("\\WR_DATA").extract(i*width, width));
					string clk_expr = make_expr(cell->getPort("\\WR_CLK").extract(i));

					SigSpec wen_sig = cell->getPort("\\WR_EN").extract(i*width, width);
					string wen_expr = make_expr(wen_sig[0]);

					for (int i = 1; i < GetSize(wen_sig); i++)
						if (wen_sig[0] != wen_sig[i])
							log_error("Complex write enable on port %d on memory %s.%s.\n", i, log_id(module), log_id(cell));

					cell_exprs.push_back(stringf("    %s.w%d.addr <= %s\n", mem_id.c_str(), i, addr_expr.c_str()));
					cell_exprs.push_back(stringf("    %s.w%d.data <= %s\n", mem_id.c_str(), i, data_expr.c_str()));
					cell_exprs.push_back(stringf("    %s.w%d.en <= %s\n", mem_id.c_str(), i, wen_expr.c_str()));
					cell_exprs.push_back(stringf("    %s.w%d.mask <= UInt<1>(1)\n", mem_id.c_str(), i));
					cell_exprs.push_back(stringf("    %s.w%d.clk <= asClock(%s)\n", mem_id.c_str(), i, clk_expr.c_str()));
				}

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
