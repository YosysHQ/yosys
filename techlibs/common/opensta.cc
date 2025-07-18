#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#if !defined(YOSYS_DISABLE_SPAWN)
struct OpenstaPass : public Pass
{
	const char* default_sta_cmd = "sta";
	OpenstaPass() : Pass("opensta", "run OpenSTA") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opensta [options]\n");
		log("\n");
		// TOOD
		log("\n");
		log("    -exe <command>\n");
		log("        use <command> to run OpenSTA instead of \"%s\"\n", default_sta_cmd);
		log("\n");
		log("    -sdc-in <filename>\n");
		log("        expand SDC input file <filename>\n");
		log("\n");
		log("    -sdc-out <filename>\n");
		log("        expand SDC file to output file <filename>\n");
		log("\n");
		log("    -nocleanup\n");
		log("\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		string opensta_exe = "sta";
		string sdc_filename, sdc_expanded_filename;
		string tempdir_name, script_filename;
		string verilog_filename, liberty_filename;
		bool cleanup = true;

		log_header(design, "Executing OPENSTA pass.\n");
		log_push();

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
			if (args[argidx] == "-verilog" && argidx+1 < args.size()) {
				verilog_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-liberty" && argidx+1 < args.size()) {
				liberty_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-nocleanup") {
				cleanup = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (cleanup)
			tempdir_name = get_base_tmpdir() + "/";
		else
			tempdir_name = "_tmp_";
		tempdir_name += proc_program_prefix() + "yosys-opensta-XXXXXX";
		tempdir_name = make_temp_dir(tempdir_name);
		script_filename = tempdir_name + "/opensta.tcl";
		// script_filename

		auto top_mod = design->top_module();
		if (!top_mod)
			log_error("Can't find top module in current design!\n");

		std::ofstream f_script;
		f_script.open(script_filename);

		f_script << "read_verilog " << verilog_filename << "\n";
		f_script << "read_lib " << liberty_filename << "\n";
		f_script << "link_design " << RTLIL::unescape_id(top_mod->name) << "\n";
		f_script << "read_sdc " << sdc_filename << "\n";
		f_script << "write_sdc " << sdc_expanded_filename << "\n";
		f_script.close();
		std::string command = opensta_exe + " -exit " + script_filename; 
		int ret = run_command(command);
		if (ret)
			log_error("OpenSTA return %d (error)\n", ret);
		else
			log("sdc_expanded_filename: %s\n", sdc_expanded_filename.c_str());

		if (cleanup) {
			log("Removing temp directory.\n");
			remove_directory(tempdir_name);
		}
		log_pop();
	}
} OpenstaPass;
#endif

PRIVATE_NAMESPACE_END
