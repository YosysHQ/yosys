#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SdcexpandPass : public ScriptPass
{
	const char* default_sta_cmd = "sta";
	SdcexpandPass() : ScriptPass("sdc_expand", "run OpenSTA") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sdc_expand [options]\n");
		log("\n");
		// TODO
		log("\n");
		log("    -exe <command>\n");
		log("        use <command> to run OpenSTA instead of \"%s\"\n", default_sta_cmd);
		log("\n");
		log("    -sdc-in <filename>\n");
		log("        expand SDC file <filename>\n");
		log("\n");
		log("    -nocleanup\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string opensta_exe, sdc_filename, sdc_expanded_filename;
	bool cleanup;
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		cleanup = true;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-exe" && argidx+1 < args.size()) {
				opensta_exe = args[++argidx];
				continue;
			}
			if (args[argidx] == "-sdc-in" && argidx+1 < args.size()) {
				sdc_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-sdc-out" && argidx+1 < args.size()) {
				sdc_expanded_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-nocleanup") {
				cleanup = false;
				continue;
			}
			// repetitive boring bit
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing OPENSTA pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		std::string tempdir_name;
		std::string liberty_path;
		std::string verilog_path;

		run("design -save pre_expand");
		run("proc");
		run("memory");
		// run("dfflegalize -cell $dff");

		std::string write_verilog_cmd = "write_verilog -norename -noexpr -attr2comment -defparam ";
		if (help_mode) {
			run(write_verilog_cmd + "<tmp_dir>/elaborated.v");
		} else {
			if (cleanup)
				tempdir_name = get_base_tmpdir() + "/";
			else
				tempdir_name = "_tmp_";
			tempdir_name += proc_program_prefix() + "yosys-sdc_expand-XXXXXX";
			tempdir_name = make_temp_dir(tempdir_name);
			verilog_path = tempdir_name + "/elaborated.v";
			run(write_verilog_cmd + verilog_path);
		}

		run("read_verilog -setattr whitebox -defer -DSIMLIB_NOCHECKS +/simlib.v");
		run("proc");
		run("hierarchy -auto-top");
		run("publish");

		if (help_mode) {
			run("icell_liberty <tmp_dir>/yosys.lib");
		} else {
			liberty_path = tempdir_name + "/yosys.lib";
			run(stringf("icell_liberty %s", liberty_path.c_str()));
		}

		std::string opensta_pass_call = "opensta -exe ";
		opensta_pass_call += help_mode ? "<exe>" : opensta_exe;
		opensta_pass_call += " -sdc-in ";
		opensta_pass_call += help_mode ? "<sdc-in>" : sdc_filename;
		opensta_pass_call += " -sdc-out ";
		opensta_pass_call += help_mode ? "<sdc-out>" : sdc_expanded_filename;
		opensta_pass_call += " -verilog ";
		opensta_pass_call += help_mode ? "<verilog>" : verilog_path;
		opensta_pass_call += " -liberty ";
		opensta_pass_call += help_mode ? "<tmp_dir>/yosys.lib" : liberty_path;
		if (!cleanup)
			opensta_pass_call += " -nocleanup";
		run(opensta_pass_call.c_str());

		if (!help_mode) {
			if (cleanup) {
				log("Removing temp directory.\n");
				remove_directory(tempdir_name);
			} else {
				log("Keeping temp directory %s\n", tempdir_name.c_str());
			}
		}
		run("design -load pre_expand");
	}
} SdcexpandPass;

PRIVATE_NAMESPACE_END
