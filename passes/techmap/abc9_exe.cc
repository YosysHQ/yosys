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

// [[CITE]] ABC
// Berkeley Logic Synthesis and Verification Group, ABC: A System for Sequential Synthesis and Verification
// http://www.eecs.berkeley.edu/~alanmi/abc/

#include "kernel/register.h"
#include "kernel/log.h"

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

#ifdef YOSYS_LINK_ABC
extern "C" int Abc_RealMain(int argc, char *argv[]);
#endif

std::string fold_abc9_cmd(std::string str)
{
	std::string token, new_str = "          ";
	int char_counter = 10;

	for (size_t i = 0; i <= str.size(); i++) {
		if (i < str.size())
			token += str[i];
		if (i == str.size() || str[i] == ';') {
			if (char_counter + token.size() > 75)
				new_str += "\n              ", char_counter = 14;
			new_str += token, char_counter += token.size();
			token.clear();
		}
	}

	return new_str;
}

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

std::string add_echos_to_abc9_cmd(std::string str)
{
	std::string new_str, token;
	for (size_t i = 0; i < str.size(); i++) {
		token += str[i];
		if (str[i] == ';') {
			while (i+1 < str.size() && str[i+1] == ' ')
				i++;
			new_str += "echo + " + token + " " + token + " ";
			token.clear();
		}
	}

	if (!token.empty()) {
		if (!new_str.empty())
			new_str += "echo + " + token + "; ";
		new_str += token;
	}

	return new_str;
}

std::string replace_tempdir(std::string text, std::string tempdir_name, bool show_tempdir)
{
	if (show_tempdir)
		return text;

	while (1) {
		size_t pos = text.find(tempdir_name);
		if (pos == std::string::npos)
			break;
		text = text.substr(0, pos) + "<abc-temp-dir>" + text.substr(pos + GetSize(tempdir_name));
	}

	std::string  selfdir_name = proc_self_dirname();
	if (selfdir_name != "/") {
		while (1) {
			size_t pos = text.find(selfdir_name);
			if (pos == std::string::npos)
				break;
			text = text.substr(0, pos) + "<yosys-exe-dir>/" + text.substr(pos + GetSize(selfdir_name));
		}
	}

	return text;
}

struct abc9_output_filter
{
	bool got_cr;
	int escape_seq_state;
	std::string linebuf;
	std::string tempdir_name;
	bool show_tempdir;

	abc9_output_filter(std::string tempdir_name, bool show_tempdir) : tempdir_name(tempdir_name), show_tempdir(show_tempdir)
	{
		got_cr = false;
		escape_seq_state = 0;
	}

	void next_char(char ch)
	{
		if (escape_seq_state == 0 && ch == '\033') {
			escape_seq_state = 1;
			return;
		}
		if (escape_seq_state == 1) {
			escape_seq_state = ch == '[' ? 2 : 0;
			return;
		}
		if (escape_seq_state == 2) {
			if ((ch < '0' || '9' < ch) && ch != ';')
				escape_seq_state = 0;
			return;
		}
		escape_seq_state = 0;
		if (ch == '\r') {
			got_cr = true;
			return;
		}
		if (ch == '\n') {
			log("ABC: %s\n", replace_tempdir(linebuf, tempdir_name, show_tempdir).c_str());
			got_cr = false, linebuf.clear();
			return;
		}
		if (got_cr)
			got_cr = false, linebuf.clear();
		linebuf += ch;
	}

	void next_line(const std::string &line)
	{
		//int pi, po;
		//if (sscanf(line.c_str(), "Start-point = pi%d.  End-point = po%d.", &pi, &po) == 2) {
		//	log("ABC: Start-point = pi%d (%s).  End-point = po%d (%s).\n",
		//			pi, pi_map.count(pi) ? pi_map.at(pi).c_str() : "???",
		//			po, po_map.count(po) ? po_map.at(po).c_str() : "???");
		//	return;
		//}

		for (char ch : line)
			next_char(ch);
	}
};

void abc9_module(RTLIL::Design *design, std::string script_file, std::string exe_file,
		vector<int> lut_costs, bool dff_mode, std::string delay_target, std::string /*lutin_shared*/, bool fast_mode,
		bool show_tempdir, std::string box_file, std::string lut_file,
		std::string wire_delay, std::string tempdir_name
)
{
	std::string abc9_script;

	if (!lut_costs.empty())
		abc9_script += stringf("read_lut %s/lutdefs.txt; ", tempdir_name.c_str());
	else if (!lut_file.empty())
		abc9_script += stringf("read_lut %s; ", lut_file.c_str());
	else
		log_abort();

	log_assert(!box_file.empty());
	abc9_script += stringf("read_box %s; ", box_file.c_str());
	abc9_script += stringf("&read %s/input.xaig; &ps; ", tempdir_name.c_str());

	if (!script_file.empty()) {
		if (script_file[0] == '+') {
			for (size_t i = 1; i < script_file.size(); i++)
				if (script_file[i] == '\'')
					abc9_script += "'\\''";
				else if (script_file[i] == ',')
					abc9_script += " ";
				else
					abc9_script += script_file[i];
		} else
			abc9_script += stringf("source %s", script_file.c_str());
	} else if (!lut_costs.empty() || !lut_file.empty()) {
		abc9_script += fast_mode ? RTLIL::constpad.at("abc9.script.default.fast").substr(1,std::string::npos)
			: RTLIL::constpad.at("abc9.script.default").substr(1,std::string::npos);
	} else
		log_abort();

	for (size_t pos = abc9_script.find("{D}"); pos != std::string::npos; pos = abc9_script.find("{D}", pos))
		abc9_script = abc9_script.substr(0, pos) + delay_target + abc9_script.substr(pos+3);

	//for (size_t pos = abc9_script.find("{S}"); pos != std::string::npos; pos = abc9_script.find("{S}", pos))
	//	abc9_script = abc9_script.substr(0, pos) + lutin_shared + abc9_script.substr(pos+3);

	for (size_t pos = abc9_script.find("{W}"); pos != std::string::npos; pos = abc9_script.find("{W}", pos))
		abc9_script = abc9_script.substr(0, pos) + wire_delay + abc9_script.substr(pos+3);

	std::string C;
	if (design->scratchpad.count("abc9.if.C"))
		C = "-C " + design->scratchpad_get_string("abc9.if.C");
	for (size_t pos = abc9_script.find("{C}"); pos != std::string::npos; pos = abc9_script.find("{C}", pos))
		abc9_script = abc9_script.substr(0, pos) + C + abc9_script.substr(pos+3);

	std::string R;
	if (design->scratchpad.count("abc9.if.R"))
		R = "-R " + design->scratchpad_get_string("abc9.if.R");
	for (size_t pos = abc9_script.find("{R}"); pos != std::string::npos; pos = abc9_script.find("{R}", pos))
		abc9_script = abc9_script.substr(0, pos) + R + abc9_script.substr(pos+3);

	abc9_script += stringf("; &ps -l; &write -n %s/output.aig", tempdir_name.c_str());
	if (design->scratchpad_get_bool("abc9.verify")) {
		if (dff_mode)
			abc9_script += "; verify -s";
		else
			abc9_script += "; verify";
	}
	abc9_script += "; time";
	abc9_script = add_echos_to_abc9_cmd(abc9_script);

	for (size_t i = 0; i+1 < abc9_script.size(); i++)
		if (abc9_script[i] == ';' && abc9_script[i+1] == ' ')
			abc9_script[i+1] = '\n';

	FILE *f = fopen(stringf("%s/abc.script", tempdir_name.c_str()).c_str(), "wt");
	fprintf(f, "%s\n", abc9_script.c_str());
	fclose(f);

	std::string buffer;

	log_header(design, "Executing ABC9.\n");

	if (!lut_costs.empty()) {
		buffer = stringf("%s/lutdefs.txt", tempdir_name.c_str());
		f = fopen(buffer.c_str(), "wt");
		if (f == NULL)
			log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
		for (int i = 0; i < GetSize(lut_costs); i++)
			fprintf(f, "%d %d.00 1.00\n", i+1, lut_costs.at(i));
		fclose(f);
	}

	buffer = stringf("%s -s -f %s/abc.script 2>&1", exe_file.c_str(), tempdir_name.c_str());
	log("Running ABC command: %s\n", replace_tempdir(buffer, tempdir_name, show_tempdir).c_str());

#ifndef YOSYS_LINK_ABC
	abc9_output_filter filt(tempdir_name, show_tempdir);
	int ret = run_command(buffer, std::bind(&abc9_output_filter::next_line, filt, std::placeholders::_1));
#else
	// These needs to be mutable, supposedly due to getopt
	char *abc9_argv[5];
	string tmp_script_name = stringf("%s/abc.script", tempdir_name.c_str());
	abc9_argv[0] = strdup(exe_file.c_str());
	abc9_argv[1] = strdup("-s");
	abc9_argv[2] = strdup("-f");
	abc9_argv[3] = strdup(tmp_script_name.c_str());
	abc9_argv[4] = 0;
	int ret = Abc_RealMain(4, abc9_argv);
	free(abc9_argv[0]);
	free(abc9_argv[1]);
	free(abc9_argv[2]);
	free(abc9_argv[3]);
#endif
	if (ret != 0)
		log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);
}

struct Abc9ExePass : public Pass {
	Abc9ExePass() : Pass("abc9_exe", "use ABC9 for technology mapping") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9_exe [options]\n");
		log("\n");
		log(" \n");
		log("This pass uses the ABC tool [1] for technology mapping of the top module\n");
		log("(according to the (* top *) attribute or if only one module is currently selected)\n");
		log("to a target FPGA architecture.\n");
		log("\n");
		log("    -exe <command>\n");
#ifdef ABCEXTERNAL
		log("        use the specified command instead of \"" ABCEXTERNAL "\" to execute ABC.\n");
#else
		log("        use the specified command instead of \"<yosys-bindir>/yosys-abc\" to execute ABC.\n");
#endif
		log("        This can e.g. be used to call a specific version of ABC or a wrapper.\n");
		log("\n");
		log("    -script <file>\n");
		log("        use the specified ABC script file instead of the default script.\n");
		log("\n");
		log("        if <file> starts with a plus sign (+), then the rest of the filename\n");
		log("        string is interpreted as the command string to be passed to ABC. The\n");
		log("        leading plus sign is removed and all commas (,) in the string are\n");
		log("        replaced with blanks before the string is passed to ABC.\n");
		log("\n");
		log("        if no -script parameter is given, the following scripts are used:\n");
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default").substr(1,std::string::npos)).c_str());
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default.fast").substr(1,std::string::npos)).c_str());
		log("\n");
		log("    -D <picoseconds>\n");
		log("        set delay target. the string {D} in the default scripts above is\n");
		log("        replaced by this option when used, and an empty string otherwise\n");
		log("        (indicating best possible delay).\n");
		log("\n");
//		log("    -S <num>\n");
//		log("        maximum number of LUT inputs shared.\n");
//		log("        (replaces {S} in the default scripts above, default: -S 1)\n");
//		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -lut <w1>:<w2>\n");
		log("        generate netlist using luts of (max) the specified width <w2>. All\n");
		log("        luts with width <= <w1> have constant cost. for luts larger than <w1>\n");
		log("        the area cost doubles with each additional input bit. the delay cost\n");
		log("        is still constant for all lut widths.\n");
		log("\n");
		log("    -lut <file>\n");
		log("        pass this file with lut library to ABC.\n");
		log("\n");
		log("    -luts <cost1>,<cost2>,<cost3>,<sizeN>:<cost4-N>,..\n");
		log("        generate netlist using luts. Use the specified costs for luts with 1,\n");
		log("        2, 3, .. inputs.\n");
		log("\n");
		log("    -showtmp\n");
		log("        print the temp dir name in log. usually this is suppressed so that the\n");
		log("        command output is identical across runs.\n");
		log("\n");
		log("    -box <file>\n");
		log("        pass this file with box library to ABC.\n");
		log("\n");
		log("    -cwd <dir>\n");
		log("        use this as the current working directory, inside which the 'input.xaig'\n");
		log("        file is expected. temporary files will be created in this directory, and\n");
		log("        the mapped result will be written to 'output.aig'.\n");
		log("\n");
		log("Note that this is a logic optimization pass within Yosys that is calling ABC\n");
		log("internally. This is not going to \"run ABC on your design\". It will instead run\n");
		log("ABC on logic snippets extracted from your design. You will not get any useful\n");
		log("output when passing an ABC script that writes a file. Instead write your full\n");
		log("design as BLIF file with write_blif and then load that into ABC externally if\n");
		log("you want to use ABC to convert your design into another format.\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9_EXE pass (technology mapping using ABC9).\n");

#ifdef ABCEXTERNAL
		std::string exe_file = ABCEXTERNAL;
#else
		std::string exe_file = proc_self_dirname() + "yosys-abc";
#endif
		std::string script_file, clk_str, box_file, lut_file;
		std::string delay_target, lutin_shared = "-S 1", wire_delay;
		std::string tempdir_name;
		bool fast_mode = false, dff_mode = false;
		bool show_tempdir = false;
		vector<int> lut_costs;

#if 0
		cleanup = false;
		show_tempdir = true;
#endif

#ifdef _WIN32
#ifndef ABCEXTERNAL
		if (!check_file_exists(exe_file + ".exe") && check_file_exists(proc_self_dirname() + "..\\yosys-abc.exe"))
			exe_file = proc_self_dirname() + "..\\yosys-abc";
#endif
#endif

		std::string lut_arg, luts_arg;
		exe_file = design->scratchpad_get_string("abc9.exe", exe_file /* inherit default value if not set */);
		script_file = design->scratchpad_get_string("abc9.script", script_file);
		if (design->scratchpad.count("abc9.D")) {
			delay_target = "-D " + design->scratchpad_get_string("abc9.D");
		}
		lut_arg = design->scratchpad_get_string("abc9.lut", lut_arg);
		luts_arg = design->scratchpad_get_string("abc9.luts", luts_arg);
		fast_mode = design->scratchpad_get_bool("abc9.fast", fast_mode);
		dff_mode = design->scratchpad_get_bool("abc9.dff", dff_mode);
		show_tempdir = design->scratchpad_get_bool("abc9.showtmp", show_tempdir);
		box_file = design->scratchpad_get_string("abc9.box", box_file);
		if (design->scratchpad.count("abc9.W")) {
			wire_delay = "-W " + design->scratchpad_get_string("abc9.W");
		}

		size_t argidx;
		char pwd [PATH_MAX];
		if (!getcwd(pwd, sizeof(pwd))) {
			log_cmd_error("getcwd failed: %s\n", strerror(errno));
			log_abort();
		}
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exe" && argidx+1 < args.size()) {
				exe_file = args[++argidx];
				continue;
			}
			if (arg == "-script" && argidx+1 < args.size()) {
				script_file = args[++argidx];
				continue;
			}
			if (arg == "-D" && argidx+1 < args.size()) {
				delay_target = "-D " + args[++argidx];
				continue;
			}
			//if (arg == "-S" && argidx+1 < args.size()) {
			//	lutin_shared = "-S " + args[++argidx];
			//	continue;
			//}
			if (arg == "-lut" && argidx+1 < args.size()) {
				lut_arg = args[++argidx];
				continue;
			}
			if (arg == "-luts" && argidx+1 < args.size()) {
				lut_arg = args[++argidx];
				continue;
			}
			if (arg == "-fast") {
				fast_mode = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (arg == "-showtmp") {
				show_tempdir = true;
				continue;
			}
			if (arg == "-box" && argidx+1 < args.size()) {
				box_file = args[++argidx];
				continue;
			}
			if (arg == "-W" && argidx+1 < args.size()) {
				wire_delay = "-W " + args[++argidx];
				continue;
			}
			if (arg == "-cwd" && argidx+1 < args.size()) {
				tempdir_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		rewrite_filename(script_file);
		if (!script_file.empty() && !is_absolute_path(script_file) && script_file[0] != '+')
			script_file = std::string(pwd) + "/" + script_file;

		// handle -lut / -luts args
		if (!lut_arg.empty()) {
			string arg = lut_arg;
			if (arg.find_first_not_of("0123456789:,") == std::string::npos) {
				size_t pos = arg.find_first_of(':');
				int lut_mode = 0, lut_mode2 = 0;
				if (pos != string::npos) {
					lut_mode = atoi(arg.substr(0, pos).c_str());
					lut_mode2 = atoi(arg.substr(pos+1).c_str());
				} else {
					lut_mode = atoi(arg.c_str());
					lut_mode2 = lut_mode;
				}
				lut_costs.clear();
				for (int i = 0; i < lut_mode; i++)
					lut_costs.push_back(1);
				for (int i = lut_mode; i < lut_mode2; i++)
					lut_costs.push_back(2 << (i - lut_mode));
			}
			else {
				lut_file = arg;
				rewrite_filename(lut_file);
				if (!lut_file.empty() && !is_absolute_path(lut_file) && lut_file[0] != '+')
					lut_file = std::string(pwd) + "/" + lut_file;
			}
		}
		if (!luts_arg.empty()) {
			lut_costs.clear();
			for (auto &tok : split_tokens(luts_arg, ",")) {
				auto parts = split_tokens(tok, ":");
				if (GetSize(parts) == 0 && !lut_costs.empty())
					lut_costs.push_back(lut_costs.back());
				else if (GetSize(parts) == 1)
					lut_costs.push_back(atoi(parts.at(0).c_str()));
				else if (GetSize(parts) == 2)
					while (GetSize(lut_costs) < atoi(parts.at(0).c_str()))
						lut_costs.push_back(atoi(parts.at(1).c_str()));
				else
					log_cmd_error("Invalid -luts syntax.\n");
			}
		}

		if (box_file.empty())
			log_cmd_error("abc9_exe '-box' option is mandatory.\n");

		rewrite_filename(box_file);
		if (!box_file.empty() && !is_absolute_path(box_file) && box_file[0] != '+')
			box_file = std::string(pwd) + "/" + box_file;

		if (tempdir_name.empty())
			log_cmd_error("abc9_exe '-cwd' option is mandatory.\n");


		abc9_module(design, script_file, exe_file, lut_costs, dff_mode,
				delay_target, lutin_shared, fast_mode, show_tempdir,
				box_file, lut_file, wire_delay, tempdir_name);
	}
} Abc9ExePass;

PRIVATE_NAMESPACE_END
