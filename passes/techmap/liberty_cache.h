#ifndef LIBERTY_CACHE_H
#define LIBERTY_CACHE_H

#include "kernel/yosys.h"

#ifdef YOSYS_LINK_ABC
namespace abc {
	int Abc_RealMain(int argc, char *argv[]);
}
#endif

YOSYS_NAMESPACE_BEGIN

/*
 * convert_liberty_files_to_merged_scl() - Convert multiple Liberty files to a single merged SCL cache file.
 * @liberty_files: Vector of liberty file paths to merge
 * @dont_use_args: Pre-built ABC -X flags string
 * @abc_exe: Path to ABC executable for conversion
 *
 * Return: Path to merged SCL cache file, or empty string if conversion fails
 */
inline std::string convert_liberty_files_to_merged_scl(const std::vector<std::string> &liberty_files, const std::string &dont_use_args, const std::string &abc_exe)
{
	if (liberty_files.empty())
		return "";

	std::string cache_dir = get_base_tmpdir() + "/yosys-liberty-scl-cache";

	if (!create_directory(cache_dir)) {
		log_warning("ABC: cannot create cache directory %s, falling back to liberty format\n", cache_dir.c_str());
		return "";
	}

	// Sort to ensure consistent hash regardless of order
	std::vector<std::string> sorted_files = liberty_files;
	std::sort(sorted_files.begin(), sorted_files.end());
	std::string hash_input;
	time_t newest_mtime = 0;

	for (const std::string &liberty_file : sorted_files) {
		struct stat liberty_stat;
		if (stat(liberty_file.c_str(), &liberty_stat) != 0) {
			log_error("ABC: cannot stat liberty file: %s\n", liberty_file.c_str());
			return "";
		}
		hash_input += liberty_file + "|";
		if (liberty_stat.st_mtime > newest_mtime)
			newest_mtime = liberty_stat.st_mtime;
	}

	hash_input += dont_use_args;
	unsigned int hash = 0;

	for (char c : hash_input)
		hash = hash * 31 + c;

	std::string merged_scl = stringf("%s/yosys_merged_%08x.scl", cache_dir.c_str(), hash);
	bool need_convert = true;
	struct stat scl_stat;

	// Check if merged SCL exists and is newer than all liberty files
	if (stat(merged_scl.c_str(), &scl_stat) == 0) {
		if (scl_stat.st_mtime >= newest_mtime) {
			log("ABC: using cached merged SCL: %s (%zu files)\n", merged_scl.c_str(), liberty_files.size());
			need_convert = false;
		}
	}

	if (need_convert) {
		// read_lib -X cell1 -X cell2 file1 ; read_lib -X cell1 -X cell2 -m file2 ; ... ; write_scl merged.scl
		std::string temp_scl = merged_scl + ".tmp";

#ifdef YOSYS_LINK_ABC
		std::string script_path = stringf("%s/yosys_merged_scl_convert_%08x.script", cache_dir.c_str(), hash);
		FILE *f = fopen(script_path.c_str(), "w");

		if (f == NULL) {
			log_warning("ABC: cannot open %s for writing, falling back to liberty format\n", script_path.c_str());
			return "";
		}

		bool first = true;

		for (const std::string &liberty_file : liberty_files) {
			fprintf(f, "read_lib %s%s-w \"%s\"\n", dont_use_args.c_str(), first ? "" : "-m ", liberty_file.c_str());
			first = false;
		}

		fprintf(f, "write_scl \"%s\"\n", temp_scl.c_str());
		fclose(f);

		char *abc_argv[5];
		abc_argv[0] = strdup(abc_exe.empty() ? "yosys-abc" : abc_exe.c_str());
		abc_argv[1] = strdup("-s");
		abc_argv[2] = strdup("-f");
		abc_argv[3] = strdup(script_path.c_str());
		abc_argv[4] = 0;
		int ret = abc::Abc_RealMain(4, abc_argv);
		free(abc_argv[0]);
		free(abc_argv[1]);
		free(abc_argv[2]);
		free(abc_argv[3]);
		remove(script_path.c_str());

		if (ret != 0) {
			log_warning("ABC: merged SCL conversion failed (ret=%d), falling back to liberty format\n", ret);
			remove(temp_scl.c_str());
			return "";
		}
#else
		std::string abc_script;
		bool first = true;

		for (const std::string &liberty_file : liberty_files) {
			abc_script += stringf("read_lib %s%s-w \\\"%s\\\" ; ", dont_use_args.c_str(), first ? "" : "-m ", liberty_file.c_str());
			first = false;
		}

		abc_script += stringf("write_scl \\\"%s\\\"", temp_scl.c_str());
		std::string cmd = stringf("\"%s\" -c \"%s\" 2>&1", abc_exe.c_str(), abc_script.c_str());
		std::string abc_output;
		int ret = run_command(cmd, [&abc_output](const std::string &line) { abc_output += line + "\n"; });

		if (ret != 0) {
			log_warning("ABC: merged SCL conversion failed, falling back to liberty format\n");
			if (!abc_output.empty()) {
				log("ABC: conversion output:\n%s", abc_output.c_str());
			}
			remove(temp_scl.c_str());
			return "";
		}
#endif
		if (rename(temp_scl.c_str(), merged_scl.c_str()) != 0) {
			log_warning("ABC: failed to rename %s to %s, falling back to liberty format\n", temp_scl.c_str(), merged_scl.c_str());
			remove(temp_scl.c_str());
			return "";
		}
	}

	return merged_scl;
}

YOSYS_NAMESPACE_END

#endif // LIBERTY_CACHE_H