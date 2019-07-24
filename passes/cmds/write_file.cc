/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct WriteFileFrontend : public Frontend {
	WriteFileFrontend() : Frontend("=write_file", "write a text to a file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_file [options] output_file [input_file]\n");
		log("\n");
		log("Write the text from the input file to the output file.\n");
		log("\n");
		log("    -a\n");
		log("        Append to output file (instead of overwriting)\n");
		log("\n");
		log("\n");
		log("Inside a script the input file can also can a here-document:\n");
		log("\n");
		log("    write_file hello.txt <<EOT\n");
		log("    Hello World!\n");
		log("    EOT\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design*) YS_OVERRIDE
	{
		bool append_mode = false;
		std::string output_filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-a") {
				append_mode = true;
				continue;
			}
			break;
		}

		if (argidx < args.size() && args[argidx].rfind("-", 0) != 0)
			output_filename = args[argidx++];
		else
			log_cmd_error("Missing output filename.\n");

		extra_args(f, filename, args, argidx);

		FILE *of = fopen(output_filename.c_str(), append_mode ? "a" : "w");
		yosys_output_files.insert(output_filename);
		char buffer[64 * 1024];
		int bytes;

		while (0 < (bytes = readsome(*f, buffer, sizeof(buffer))))
			fwrite(buffer, bytes, 1, of);

		fclose(of);
	}
} WriteFileFrontend;

PRIVATE_NAMESPACE_END
