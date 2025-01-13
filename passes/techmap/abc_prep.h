#ifndef ABC_PREP_H
#define ABC_PREP_H

#include "kernel/gzip.h"

USING_YOSYS_NAMESPACE

namespace AbcPrep {
	inline std::string tmp_base(bool cleanup)
	{
		std::string base;
		if (cleanup)
			base = get_base_tmpdir() + "/";
		else
			base = "_tmp_";
		return base + proc_program_prefix();
	}

	/**
	 * Extracts gzipped liberty_files and rewrites their paths
	 * to the new temporary file paths
	 */
	inline void lib_to_tmp(std::string top_tmpdir, std::vector<std::string>& liberty_files)
	{
		for (std::string& f : liberty_files) {
			bool ends_gz = false;
			auto dot_pos = f.find_last_of(".");
			if(dot_pos != std::string::npos)
				ends_gz = f.substr(dot_pos+1) == "gz";
			log_debug("Does %s end with .gz? %d\n", f.c_str(), ends_gz);
			if (ends_gz) {
				auto filename_pos = f.find_last_of("/");
				if(filename_pos == std::string::npos)
					filename_pos = f.find_last_of("\\");
				if(filename_pos == std::string::npos) {
					filename_pos = 0;
				} else {
					filename_pos++;
				}
				std::istream* s = uncompressed(f);
				std::string base = f.substr(filename_pos, dot_pos - filename_pos);
				log_debug("base %s\n", base.c_str());
				std::string tmp_f = top_tmpdir + "/" + base + "-XXXXXX";
				tmp_f = make_temp_file(tmp_f);
				log_debug("tmp_f %s\n", tmp_f.c_str());
				std::ofstream out(tmp_f);
				out << s->rdbuf();
				f = tmp_f;
			}
		}
	}
};

#endif /* ABC_PREP_H */
