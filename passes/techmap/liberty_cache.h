#ifndef LIBERTY_CACHE_H
#define LIBERTY_CACHE_H

#include "kernel/yosys.h"
#include <vector>
#include <string>
#include <algorithm>
#include <sys/stat.h>

YOSYS_NAMESPACE_BEGIN

/*
 * convert_liberty_files_to_merged_scl() - Convert multiple Liberty files to a single merged SCL cache file.
 * @liberty_files - Vector of liberty file paths to merge
 * @abc_exe - Path to ABC executable for conversion
 *
 * Return: Path to merged SCL cache file, or empty string if conversion fails
 */
inline std::string convert_liberty_files_to_merged_scl(const std::vector<std::string> &liberty_files, const std::string &abc_exe)
{
	if (liberty_files.empty())
		return "";

	// Sort filenames to ensure consistent hash regardless of order
	std::vector<std::string> sorted_files = liberty_files;
	std::sort(sorted_files.begin(), sorted_files.end());
	std::string hash_input;
	time_t newest_mtime = 0;

	for (const std::string &liberty_file : sorted_files) {
		struct stat liberty_stat;
		if (stat(liberty_file.c_str(), &liberty_stat) != 0) {
			log_error("Cannot stat Liberty file: %s\n", liberty_file.c_str());
			return "";
		}
		hash_input += liberty_file + "|";
		if (liberty_stat.st_mtime > newest_mtime)
			newest_mtime = liberty_stat.st_mtime;
	}

	// SCL filename
	std::string first_dir;
	size_t last_slash = liberty_files[0].find_last_of("/\\");
	unsigned int hash = 0;

	if (last_slash == std::string::npos) {
		first_dir = ".";
	} else {
		first_dir = liberty_files[0].substr(0, last_slash);
	}

	for (char c : hash_input)
		hash = hash * 31 + c;

	std::string merged_scl = stringf("%s/.yosys_merged_%08x.scl", first_dir.c_str(), hash);
	bool need_convert = true;
	struct stat scl_stat;

	// Check if merged SCL exists and is newer than all liberty files
	if (stat(merged_scl.c_str(), &scl_stat) == 0) {
		if (scl_stat.st_mtime >= newest_mtime) {
			log("ABC: Using cached merged SCL: %s (%zu files)\n", merged_scl.c_str(), liberty_files.size());
			need_convert = false;
		}
	}

	if (need_convert) {
		// read_lib file1 ; read_lib -m file2 ; ... ; write_scl merged.scl
		std::string abc_script;
		bool first = true;

		for (const std::string &liberty_file : liberty_files) {
			abc_script += stringf("read_lib %s-w \\\"%s\\\" ; ", first ? "" : "-m ", liberty_file.c_str());
			first = false;
		}

		abc_script += stringf("write_scl \\\"%s\\\"", merged_scl.c_str());
		std::string cmd = stringf("\"%s\" -c \"%s\" 2>&1", abc_exe.c_str(), abc_script.c_str());
		std::string abc_output;
		int ret = run_command(cmd, [&abc_output](const std::string &line) { abc_output += line + "\n"; });

		if (ret != 0) {
			log_warning("ABC: Merged SCL conversion failed, falling back to liberty format\n");
			if (!abc_output.empty()) {
				log("ABC conversion output:\n%s", abc_output.c_str());
			}
			return "";
		}
	}

	return merged_scl;
}

YOSYS_NAMESPACE_END

#endif // LIBERTY_CACHE_H
