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

#include "kernel/register.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_ITER 1000

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

static void autotest(FILE *f, RTLIL::Design *design)
{
	fprintf(f, "module testbench;\n\n");

	fprintf(f, "integer i;\n\n");

	fprintf(f, "reg [31:0] xorshift128_x = 123456789;\n");
	fprintf(f, "reg [31:0] xorshift128_y = 362436069;\n");
	fprintf(f, "reg [31:0] xorshift128_z = 521288629;\n");
	fprintf(f, "reg [31:0] xorshift128_w = 88675123;\n");
	fprintf(f, "reg [31:0] xorshift128_t;\n\n");
	fprintf(f, "task xorshift128;\n");
	fprintf(f, "begin\n");
	fprintf(f, "\txorshift128_t = xorshift128_x ^ (xorshift128_x << 11);\n");
	fprintf(f, "\txorshift128_x = xorshift128_y;\n");
	fprintf(f, "\txorshift128_y = xorshift128_z;\n");
	fprintf(f, "\txorshift128_z = xorshift128_w;\n");
	fprintf(f, "\txorshift128_w = xorshift128_w ^ (xorshift128_w >> 19) ^ xorshift128_t ^ (xorshift128_t >> 8);\n");
	fprintf(f, "end\n");
	fprintf(f, "endtask\n\n");

	for (auto it = design->modules.begin(); it != design->modules.end(); it++)
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
		for (auto it2 = mod->wires.begin(); it2 != mod->wires.end(); it2++) {
			RTLIL::Wire *wire = it2->second;
			if (wire->port_output) {
				count_ports++;
				signal_out[idy("sig", mod->name, wire->name)] = wire->width;
				fprintf(f, "wire [%d:0] %s;\n", wire->width-1, idy("sig", mod->name, wire->name).c_str());
			} else if (wire->port_input) {
				count_ports++;
				bool is_clksignal = wire->get_bool_attribute("\\gentb_clock");
				for (auto it3 = mod->processes.begin(); it3 != mod->processes.end(); it3++)
				for (auto it4 = it3->second->syncs.begin(); it4 != it3->second->syncs.end(); it4++) {
					if ((*it4)->type == RTLIL::ST0 || (*it4)->type == RTLIL::ST1)
						continue;
					RTLIL::SigSpec &signal = (*it4)->signal;
					for (auto &c : signal.chunks())
						if (c.wire == wire)
							is_clksignal = true;
				}
				if (is_clksignal && wire->attributes.count("\\gentb_constant") == 0) {
					signal_clk[idy("sig", mod->name, wire->name)] = wire->width;
				} else {
					signal_in[idy("sig", mod->name, wire->name)] = wire->width;
					if (wire->attributes.count("\\gentb_constant") != 0)
						signal_const[idy("sig", mod->name, wire->name)] = wire->attributes["\\gentb_constant"].as_string();
				}
				fprintf(f, "reg [%d:0] %s;\n", wire->width-1, idy("sig", mod->name, wire->name).c_str());
			}
		}
		fprintf(f, "%s %s(\n", id(mod->name).c_str(), idy("uut", mod->name).c_str());
		for (auto it2 = mod->wires.begin(); it2 != mod->wires.end(); it2++) {
			RTLIL::Wire *wire = it2->second;
			if (wire->port_output || wire->port_input)
				fprintf(f, "\t.%s(%s)%s\n", id(wire->name).c_str(),
						idy("sig", mod->name, wire->name).c_str(), --count_ports ? "," : "");
		}
		fprintf(f, ");\n\n");

		fprintf(f, "task %s;\n", idy(mod->name, "reset").c_str());
		fprintf(f, "begin\n");
		int delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); it++)
			fprintf(f, "\t%s <= #%d 0;\n", it->first.c_str(), ++delay_counter*2);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); it++)
			fprintf(f, "\t%s <= #%d 0;\n", it->first.c_str(), ++delay_counter*2);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
			fprintf(f, "\t#100; %s <= 1;\n", it->first.c_str());
			fprintf(f, "\t#100; %s <= 0;\n", it->first.c_str());
		}
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); it++)
			fprintf(f, "\t%s <= #%d ~0;\n", it->first.c_str(), ++delay_counter*2);
		for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
			fprintf(f, "\t#100; %s <= 1;\n", it->first.c_str());
			fprintf(f, "\t#100; %s <= 0;\n", it->first.c_str());
		}
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); it++) {
			if (signal_const.count(it->first) == 0)
				continue;
			fprintf(f, "\t%s <= #%d 'b%s;\n", it->first.c_str(), ++delay_counter*2, signal_const[it->first].c_str());
		}
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");

		fprintf(f, "task %s;\n", idy(mod->name, "update_data").c_str());
		fprintf(f, "begin\n");
		delay_counter = 0;
		for (auto it = signal_in.begin(); it != signal_in.end(); it++) {
			if (signal_const.count(it->first) > 0)
				continue;
			fprintf(f, "\txorshift128;\n");
			fprintf(f, "\t%s <= #%d { xorshift128_x, xorshift128_y, xorshift128_z, xorshift128_w };\n", it->first.c_str(), ++delay_counter*2);
		}
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");

		fprintf(f, "task %s;\n", idy(mod->name, "update_clock").c_str());
		fprintf(f, "begin\n");
		if (signal_clk.size()) {
			fprintf(f, "\txorshift128;\n");
			fprintf(f, "\t{");
			int total_clock_bits = 0;
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
				fprintf(f, "%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
				total_clock_bits += it->second;
			}
			fprintf(f, " } = {");
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++)
				fprintf(f, "%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
			fprintf(f, " } ^ (%d'b1 << (xorshift128_w %% %d));\n", total_clock_bits, total_clock_bits);
		}
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");

		char shorthand = 'A';
		std::vector<std::string> header1;
		std::string header2 = "";

		fprintf(f, "task %s;\n", idy(mod->name, "print_status").c_str());
		fprintf(f, "begin\n");
		fprintf(f, "\t$display(\"#OUT# %%b %%b %%b %%t %%d\", {");
		if (signal_in.size())
			for (auto it = signal_in.begin(); it != signal_in.end(); it++) {
				fprintf(f, "%s %s", it == signal_in.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand++;
			}
		else {
			fprintf(f, " 1'bx");
			header2 += "#";
		}
		fprintf(f, " }, {");
		header2 += " ";
		if (signal_clk.size()) {
			for (auto it = signal_clk.begin(); it != signal_clk.end(); it++) {
				fprintf(f, "%s %s", it == signal_clk.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand++;
			}
		} else {
			fprintf(f, " 1'bx");
			header2 += "#";
		}
		fprintf(f, " }, {");
		header2 += " ";
		if (signal_out.size()) {
			for (auto it = signal_out.begin(); it != signal_out.end(); it++) {
				fprintf(f, "%s %s", it == signal_out.begin() ? "" : ",", it->first.c_str());
				int len = it->second;
				if (len > 1)
					header2 += "/", len--;
				while (len > 1)
					header2 += "-", len--;
				if (len > 0)
					header2 += shorthand, len--;
				header1.push_back("    " + it->first);
				header1.back()[0] = shorthand++;
			}
		} else {
			fprintf(f, " 1'bx");
			header2 += "#";
		}
		fprintf(f, " }, $time, i);\n");
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");

		fprintf(f, "task %s;\n", idy(mod->name, "print_header").c_str());
		fprintf(f, "begin\n");
		fprintf(f, "\t$display(\"#OUT#\");\n");
		for (auto &hdr : header1)
			fprintf(f, "\t$display(\"#OUT#   %s\");\n", hdr.c_str());
		fprintf(f, "\t$display(\"#OUT#\");\n");
		fprintf(f, "\t$display(\"#OUT# %s\");\n", header2.c_str());
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");

		fprintf(f, "task %s;\n", idy(mod->name, "test").c_str());
		fprintf(f, "begin\n");
		fprintf(f, "\t$display(\"#OUT#\\n#OUT# ==== %s ====\");\n", idy(mod->name).c_str());
		fprintf(f, "\t%s;\n", idy(mod->name, "reset").c_str());
		fprintf(f, "\tfor (i=0; i<%d; i=i+1) begin\n", NUM_ITER);
		fprintf(f, "\t\tif (i %% 20 == 0) %s;\n", idy(mod->name, "print_header").c_str());
		fprintf(f, "\t\t#100; %s;\n", idy(mod->name, "update_data").c_str());
		fprintf(f, "\t\t#100; %s;\n", idy(mod->name, "update_clock").c_str());
		fprintf(f, "\t\t#100; %s;\n", idy(mod->name, "print_status").c_str());
		fprintf(f, "\tend\n");
		fprintf(f, "end\n");
		fprintf(f, "endtask\n\n");
	}

	fprintf(f, "initial begin\n");
	fprintf(f, "\t// $dumpfile(\"testbench.vcd\");\n");
	fprintf(f, "\t// $dumpvars(0, testbench);\n");
	for (auto it = design->modules.begin(); it != design->modules.end(); it++)
		if (!it->second->get_bool_attribute("\\gentb_skip"))
			fprintf(f, "\t%s;\n", idy(it->first, "test").c_str());
	fprintf(f, "\t$finish;\n");
	fprintf(f, "end\n\n");

	fprintf(f, "endmodule\n");
}

struct AutotestBackend : public Backend {
	AutotestBackend() : Backend("autotest", "generate simple test benches") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_autotest [filename]\n");
		log("\n");
		log("Automatically create primitive verilog test benches for all modules in the\n");
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
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing AUTOTEST backend (auto-generate pseudo-random test benches).\n");
		extra_args(f, filename, args, 1);
		autotest(f, design);
	}
} AutotestBackend;
 
