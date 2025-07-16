/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct LibertyStubber {
	CellTypes ct;
	CellTypes ct_ff;
	LibertyStubber() {
		ct.setup();
		ct.setup_internals_ff();
	}
	void liberty_prefix(std::ostream& f)
	{
		f << "library (yosys) {\n";
		f << "\tinput_threshold_pct_fall : 50;\n";
		f << "\tinput_threshold_pct_rise : 50;\n";
		f << "\toutput_threshold_pct_fall : 50;\n";
		f << "\toutput_threshold_pct_rise : 50;\n";
		f << "\tslew_lower_threshold_pct_fall : 1;\n";
		f << "\tslew_lower_threshold_pct_rise : 1;\n";
		f << "\tslew_upper_threshold_pct_fall : 99;\n";
		f << "\tslew_upper_threshold_pct_rise : 99;\n";
	}
	void liberty_suffix(std::ostream& f)
	{
		f << "}\n";
	}
	void liberty_cell(Module* base, Module* derived, std::ostream& f)
	{
		auto base_name = base->name.str().substr(1);
		auto derived_name = derived->name.str().substr(1);
		if (!ct.cell_types.count(base_name)) {
			log_debug("skip skeleton for %s\n", base_name.c_str());
			return;
		}
		auto& base_type = ct.cell_types[base_name];
		f << "\tcell (\"" << derived_name << "\") {\n";
		for (auto x : derived->ports) {
			bool is_input = base_type.inputs.count(x);
			bool is_output = base_type.outputs.count(x);
			f << "\t\tpin (" << RTLIL::unescape_id(x.str()) << ") {\n";
			if (is_input && !is_output) {
				f << "\t\t\tdirection : input;\n";
			} else if (!is_input && is_output) {
				f << "\t\t\tdirection : output;\n";
			} else {
				f << "\t\t\tdirection : inout;\n";
			}
			f << "\t\t}\n";
		}
		f << "\t}\n";
	}
};

struct IcellLiberty : Pass {
	IcellLiberty() : Pass("icell_liberty", "derive box modules") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    icell_liberty <liberty_file>\n"); // TODO
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing ICELL_LIBERTY pass.\n");

		size_t argidx;
		IdString naming_attr;
		std::string liberty_filename;
		std::ofstream* liberty_file = new std::ofstream;

		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		if (argidx < args.size())
			liberty_filename = args[argidx++];
		else
			log_error("no Liberty filename specified\n");

		// extra_args(args, argidx, d);

		if (liberty_filename.size()) {
			liberty_file->open(liberty_filename.c_str());
			if (liberty_file->fail()) {
				delete liberty_file;
				log_error("Can't open file `%s' for writing: %s\n", liberty_filename.c_str(), strerror(errno));
			}
		}

		pool<RTLIL::IdString> done;
		LibertyStubber stubber = {};

		if (liberty_file)
			stubber.liberty_prefix(*liberty_file);

		for (auto module : d->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				Module *inst_module = d->module(cell->type);
				if (!inst_module || !inst_module->get_blackbox_attribute())
					continue;
				Module *base = inst_module;
				if (!done.count(base->name)) {
					stubber.liberty_cell(base, base, *liberty_file);
					done.insert(base->name);
				}
			}
		}

		if (liberty_file) {
			stubber.liberty_suffix(*liberty_file);
			delete liberty_file;
		}
	}
} IcellLiberty;

PRIVATE_NAMESPACE_END
