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

#include "kernel/yosys.h"
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static std::string id(std::string internal_id)
{
	const char *str = internal_id.c_str();
	bool do_escape = false;

	if (*str == '\\')
		str++;

	if ('0' <= *str && *str <= '9')
		do_escape = true;

	for (int i = 0; str[i]; i++) {
		if ('0' <= str[i] && str[i] <= '9')
			continue;
		if ('a' <= str[i] && str[i] <= 'z')
			continue;
		if ('A' <= str[i] && str[i] <= 'Z')
			continue;
		if (str[i] == '_')
			continue;
		do_escape = true;
		break;
	}

	if (do_escape)
		return "\\" + std::string(str) + " ";
	return std::string(str);
}

static std::string idx(std::string str)
{
	if (str[0] == '\\')
		return str.substr(1);
	return str;
}

static std::string idy(std::string str1, std::string str2 = std::string(), std::string str3 = std::string())
{
	str1 = idx(str1);
	if (!str2.empty())
		str1 += "_" + idx(str2);
	if (!str3.empty())
		str1 += "_" + idx(str3);
	return id(str1);
}

static void autotest(std::ostream &f, RTLIL::Design *design, int num_iter, int seed)
{
	f << stringf("`ifndef outfile\n");
	f << stringf("\t`define outfile \"/dev/stdout\"\n");
	f << stringf("`endif\n");

	f << stringf("module testbench;\n\n");

	f << stringf("integer i;\n");
	f << stringf("integer file;\n\n");

	f << stringf("reg [31:0] xorshift128_x = 123456789;\n");
	f << stringf("reg [31:0] xorshift128_y = 362436069;\n");
	f << stringf("reg [31:0] xorshift128_z = 521288629;\n");
	f << stringf("reg [31:0] xorshift128_w = %u; // <-- seed value\n", seed ? seed : int(time(NULL)));
	f << stringf("reg [31:0] xorshift128_t;\n\n");
	f << stringf("task xorshift128;\n");
	f << stringf("begin\n");
	f << stringf("\txorshift128_t = xorshift128_x ^ (xorshift128_x << 11);\n");
	f << stringf("\txorshift128_x = xorshift128_y;\n");
	f << stringf("\txorshift128_y = xorshift128_z;\n");
	f << stringf("\txorshift128_z = xorshift128_w;\n");
	f << stringf("\txorshift128_w = xorshift128_w ^ (xorshift128_w >> 19) ^ xorshift128_t ^ (xorshift128_t >> 8);\n");
	f << stringf("end\n");
	f << stringf("endtask\n\n");

	for (auto it = design->modules_.begin(); it != design->modules_.end(); ++it)
	{
		std::map<std::string, int> signal_in;
		std::map<std::string, std::string> signal_const;
		std::map<std::string, int> signal_clk;
		std::map<std::string, int> signal_out;

		RTLIL::Module *mod = it->second;

		if (mod->get_bool_attribute("\\gentb_skip"))
			continue;

		int count_ports = 0;
		log("Generating test bench for module `%s'.\n", it->first.c_str());
		for (auto it2 = mod->wires_.begin(); it2 != mod->wires_.end(); ++it2) {
			RTLIL::Wire *wire = it2->second;
			if (wire->port_output) {
				count_ports++;
				signal_out[idy("sig", mod->name.str(), wire->name.str())] = wire->width;
				f << stringf("wire [%d:0] %s;\n", wire->width-1, idy("sig", mod->name.str(), wire->name.str()).c_str());
			} else if (wire->port_input) {
				count_ports++;
				bool is_clksignal = wire->get_bool_attribute("\\gentb_clock");
				for (auto it3 = mod->processes.begin(); it3 != mod->processes.end(); ++it3)
				for (auto it4 = it3->second->syncs.begin(); it4 != it3->second->syncs.end(); ++it4) {
					if ((*it4)->type == RTLIL::ST0 || (*it4)->type == RTLIL::ST1)
						continue;
					RTLIL::SigSpec &signal = (*it4)->signal;
					for (auto &c : signal.chunks())
						if (c.wire == wire)
							is_clksignal = true;
				}
				if (is_clksignal && wire->attributes.count("\\gentb_constant") == 0) {
					signal_clk[idy("sig", mod->name.str(), wire->name.str())] = wire->width;
				} else {
					signal_in[idy("sig", mod->name.str(), wire->name.str())] = wire->width;
					if (wire->attributes.count("\\gentb_constant") != 0)
						signal_const[idy("sig", mod->name.str(), wire->name.str())] = wire->attributes["\\gentb_constant"].as_string();
				}
				f << stringf("reg [%d:0] %s;\n", wire->width-1, idy("sig", mod->name.str(), wire->name.str()).c_str());
			}
		}
		f << stringf("%s %s(\n", id(mod->name.str()).c_str(), idy("uut", mod->name.str()).c_str());
		for (auto it2 = mod->wires_.begin(); it2 != mod->wires_.end(); ++it2) {
			RTLIL::Wire *wire = it2->second;
			if (wire->port_output || wire->port_input)
				f << stringf("\t.%s(%s)%s\n", id(wire->name.str()).c_str(),
						idy("sig", mod->name.str(), wire->name.str()).c_str(), --count_ports ? "," : "");
		}
		f << stringf(");\n\n");

		f << stringf("task %s;\n", idy(mod->name.str(), "reset").c_str());
		f << stringf("begin\n");
		int delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); ++it)
			f << stringf("\t%s <= #%d 0;\n", it->first.c_str(), ++delay_counter*2);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); ++it)
			f << stringf("\t%s <= #%d 0;\n", it->first.c_str(), ++delay_counter*2);
		f << stringf("\t#%d;\n", ((2*delay_counter+99)/100)*100);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); ++it) {
			f << stringf("\t#100; %s <= 1;\n", it->first.c_str());
			f << stringf("\t#100; %s <= 0;\n", it->first.c_str());
		}
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); ++it)
			f << stringf("\t%s <= #%d ~0;\n", it->first.c_str(), ++delay_counter*2);
		f << stringf("\t#%d;\n", ((2*delay_counter+99)/100)*100);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); ++it) {
			f << stringf("\t#100; %s <= 1;\n", it->first.c_str());
			f << stringf("\t#100; %s <= 0;\n", it->first.c_str());
		}
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); ++it) {
			if (signal_const.count(it->first) == 0)
				continue;
			f << stringf("\t%s <= #%d 'b%s;\n", it->first.c_str(), ++delay_counter*2, signal_const[it->first].c_str());
		}
		f << stringf("\t#%d;\n", ((2*delay_counter+99)/100)*100);
		f << stringf("end\n");
		f << stringf("endtask\n\n");

		f << stringf("task %s;\n", idy(mod->name.str(), "update_data").c_str());
		f << stringf("begin\n");
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); it++) {
			if (signal_const.count(it->first) > 0)
				continue;
			f << stringf("\txorshift128;\n");
			f << stringf("\t%s <= #%d { xorshift128_x, xorshift128_y, xorshift128_z, xorshift128_w };\n", it->first.c_str(), ++delay_counter*2);
		}
		f << stringf("\t#%d;\n", ((2*delay_counter+99)/100)*100);
		f << stringf("end\n");
		f << stringf("endtask\n\n");

		f << stringf("task %s;\n", idy(mod->name.str(), "update_clock").c_str());
		f << stringf("begin\n");
		if (signal_clk.size()) {
			f << stringf("\txorshift128;\n");
			f << stringf("\t{");
			int total_clock_bits = 0;
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
				f << stringf("%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
				total_clock_bits += it->second;
			}
			f << stringf(" } = {");
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++)
				f << stringf("%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
			f << stringf(" } ^ (%d'b1 << (xorshift128_w %% %d));\n", total_clock_bits, total_clock_bits + 1);
		}
		f << stringf("end\n");
		f << stringf("endtask\n\n");

		char shorthand = 'A';
		std::vector<std::string> header1;
		std::string header2 = "";

		f << stringf("task %s;\n", idy(mod->name.str(), "print_status").c_str());
		f << stringf("begin\n");
		f << stringf("\t$fdisplay(file, \"#OUT# %%b %%b %%b %%t %%d\", {");
		if (signal_in.size())
			for (auto it = signal_in.begin(); it != signal_in.end(); it++) {
				f << stringf("%s %s", it == signal_in.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				header2 += ", \"";
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header2 += "\"";
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand;
				shorthand = shorthand == 'Z' ? 'A' : shorthand+1;
			}
		else {
			f << stringf(" 1'bx");
			header2 += ", \"#\"";
		}
		f << stringf(" }, {");
		header2 += ", \" \"";
		if (signal_clk.size()) {
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
				f << stringf("%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				header2 += ", \"";
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header2 += "\"";
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand;
				shorthand = shorthand == 'Z' ? 'A' : shorthand+1;
			}
		} else {
			f << stringf(" 1'bx");
			header2 += ", \"#\"";
		}
		f << stringf(" }, {");
		header2 += ", \" \"";
		if (signal_out.size()) {
			for (auto it = signal_out.begin(); it != signal_out.end(); it++) {
				f << stringf("%s %s", it == signal_out.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				header2 += ", \"";
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header2 += "\"";
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand;
				shorthand = shorthand == 'Z' ? 'A' : shorthand+1;
			}
		} else {
			f << stringf(" 1'bx");
			header2 += ", \"#\"";
		}
		f << stringf(" }, $time, i);\n");
		f << stringf("end\n");
		f << stringf("endtask\n\n");

		f << stringf("task %s;\n", idy(mod->name.str(), "print_header").c_str());
		f << stringf("begin\n");
		f << stringf("\t$fdisplay(file, \"#OUT#\");\n");
		for (auto &hdr : header1)
			f << stringf("\t$fdisplay(file, \"#OUT#   %s\");\n", hdr.c_str());
		f << stringf("\t$fdisplay(file, \"#OUT#\");\n");
		f << stringf("\t$fdisplay(file, {\"#OUT# \"%s});\n", header2.c_str());
		f << stringf("end\n");
		f << stringf("endtask\n\n");

		f << stringf("task %s;\n", idy(mod->name.str(), "test").c_str());
		f << stringf("begin\n");
		f << stringf("\t$fdisplay(file, \"#OUT#\\n#OUT# ==== %s ====\");\n", idy(mod->name.str()).c_str());
		f << stringf("\t%s;\n", idy(mod->name.str(), "reset").c_str());
		f << stringf("\tfor (i=0; i<%d; i=i+1) begin\n", num_iter);
		f << stringf("\t\tif (i %% 20 == 0) %s;\n", idy(mod->name.str(), "print_header").c_str());
		f << stringf("\t\t#100; %s;\n", idy(mod->name.str(), "update_data").c_str());
		f << stringf("\t\t#100; %s;\n", idy(mod->name.str(), "update_clock").c_str());
		f << stringf("\t\t#100; %s;\n", idy(mod->name.str(), "print_status").c_str());
		f << stringf("\tend\n");
		f << stringf("end\n");
		f << stringf("endtask\n\n");
	}

	f << stringf("initial begin\n");
	f << stringf("\t// $dumpfile(\"testbench.vcd\");\n");
	f << stringf("\t// $dumpvars(0, testbench);\n");
	f << stringf("\tfile = $fopen(`outfile);\n");
	for (auto it = design->modules_.begin(); it != design->modules_.end(); ++it)
		if (!it->second->get_bool_attribute("\\gentb_skip"))
			f << stringf("\t%s;\n", idy(it->first.str(), "test").c_str());
	f << stringf("\t$fclose(file);\n");
	f << stringf("\t$finish;\n");
	f << stringf("end\n\n");

	f << stringf("endmodule\n");
}

struct TestAutotbBackend : public Backend {
	TestAutotbBackend() : Backend("=test_autotb", "generate simple test benches") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_autotb [options] [filename]\n");
		log("\n");
		log("Automatically create primitive Verilog test benches for all modules in the\n");
		log("design. The generated testbenches toggle the input pins of the module in\n");
		log("a semi-random manner and dumps the resulting output signals.\n");
		log("\n");
		log("This can be used to check the synthesis results for simple circuits by\n");
		log("comparing the testbench output for the input files and the synthesis results.\n");
		log("\n");
		log("The backend automatically detects clock signals. Additionally a signal can\n");
		log("be forced to be interpreted as clock signal by setting the attribute\n");
		log("'gentb_clock' on the signal.\n");
		log("\n");
		log("The attribute 'gentb_constant' can be used to force a signal to a constant\n");
		log("value after initialization. This can e.g. be used to force a reset signal\n");
		log("low in order to explore more inner states in a state machine.\n");
		log("\n");
		log("    -n <int>\n");
		log("        number of iterations the test bench should run (default = 1000)\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		int num_iter = 1000;
		int seed = 0;

		log_header(design, "Executing TEST_AUTOTB backend (auto-generate pseudo-random test benches).\n");

		int argidx;
		for (argidx = 1; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-n" && argidx+1 < GetSize(args)) {
				num_iter = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-seed" && argidx+1 < GetSize(args)) {
				seed = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}

		extra_args(f, filename, args, argidx);
		autotest(*f, design, num_iter, seed);
	}
} TestAutotbBackend;

PRIVATE_NAMESPACE_END

