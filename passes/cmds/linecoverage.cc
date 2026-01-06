/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/sigtools.h"

#include <regex>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


static const std::regex src_re("(.*):(\\d+)\\.(\\d+)-(\\d+)\\.(\\d+)");

struct CoveragePass : public Pass {
	CoveragePass() : Pass("linecoverage", "report coverage information") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    linecoverage [options] [selection]\n");
		log("\n");
		log("This command prints coverage information on the design based on the current\n");
		log("selection, where items in the selection are considered covered and items not in\n");
		log("the selection are considered uncovered. If the same source location is found\n");
		log("both on items inside and out of the selection, it is considered uncovered.\n");
		log("\n");
		log("    -lcov <filename>\n");
		log("        write coverage information in lcov format to this file\n");
		log("\n");
	}

	std::string extract_src_filename(std::string src) const
	{
		std::smatch m;
		if (std::regex_match(src, m, src_re)) {
			return m[1].str();
		};
		return "";
	}

	std::pair<int, int> extract_src_lines(std::string src) const
	{
		std::smatch m;
		if (std::regex_match(src, m, src_re)) {
			return std::make_pair(stoi(m[2].str()), stoi(m[4].str()));
		};
		return std::make_pair(0,0);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string ofile;

		log_header(design, "Executing linecoverage pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-lcov" && argidx+1 < args.size()) {
				ofile = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ofstream fout;
		if (!ofile.empty()) {
			fout.open(ofile, std::ios::out | std::ios::trunc);
			if (!fout.is_open())
				log_error("Could not open file \"%s\" with write access.\n", ofile);
		}

		std::map<std::string, std::set<int>> uncovered_lines;
		std::map<std::string, std::set<int>> all_lines;
		
		for (auto module : design->modules())
		{
			log_debug("Module %s:\n", log_id(module));
			for (auto wire: module->wires()) {
				log_debug("%s\t%s\t%s\n", module->selected(wire) ? "*" : " ", wire->get_src_attribute(), log_id(wire->name));
				for (auto src: wire->get_strpool_attribute(ID::src)) {
					auto filename = extract_src_filename(src);
					if (filename.empty()) continue;
					auto [begin, end] = extract_src_lines(src);
					for (int l = begin; l <=end; l++) {
						if (l == 0) continue;
						all_lines[filename].insert(l);
						if (!module->selected(wire))
							uncovered_lines[filename].insert(l);
					}
				}
			}
			for (auto cell: module->cells()) {
				log_debug("%s\t%s\t%s\n", module->selected(cell) ? "*" : " ", cell->get_src_attribute(), log_id(cell->name));
				for (auto src: cell->get_strpool_attribute(ID::src)) {
					auto filename = extract_src_filename(src);
					if (filename.empty()) continue;
					auto [begin, end] = extract_src_lines(src);
					for (int l = begin; l <=end; l++) {
						if (l == 0) continue;
						all_lines[filename].insert(l);
						if (!module->selected(cell))
							uncovered_lines[filename].insert(l);
					}
				}
			}
			log_debug("\n");
		}

		for (const auto& file_entry : all_lines) {
			int lines_found = file_entry.second.size();
			int lines_hit = file_entry.second.size() - (uncovered_lines.count(file_entry.first) ? uncovered_lines[file_entry.first].size() : 0);
			log("File %s: %d/%d lines covered\n", file_entry.first, lines_hit, lines_found);

			if(!ofile.empty()) {
				fout << "SF:" << file_entry.first << "\n";
				for (int l : file_entry.second) {
					fout << "DA:" << l << ",";
					if (uncovered_lines.count(file_entry.first) && uncovered_lines[file_entry.first].count(l))
						fout << "0";
					else 
						fout << "1";
					fout << "\n";
				}
				fout << "LF:" << lines_found << "\n";
				fout << "LH:" << lines_hit << "\n";
				fout << "end_of_record\n";
			}
		}

	}
} CoveragePass;

PRIVATE_NAMESPACE_END
