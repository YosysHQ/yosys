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
		f << "\tcell (" << derived_name << ") {\n";
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

struct BoxDerivePass : Pass {
	BoxDerivePass() : Pass("box_derive", "derive box modules") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    box_derive [-base <base_module>] [-naming_attr <attr>] [selection]\n");
		log("\n");
		log("As part of the assembly of the design hierarchy done by the 'hierarchy' command,\n");
		log("specializations of parametric modules are derived on demand: for each choice of\n");
		log("parameter values appearing in the design, a copy of the parametric module is\n");
		log("derived which is specialized to that choice.\n");
		log("\n");
		log("This derivation process ignores blackboxes and whiteboxes (boxes). To supplement,\n");
		log("this 'box_derive' command can be used to request the derivation of modules based\n");
		log("on box instances appearing in the design, which is desirable in certain use\n");
		log("cases. Only the selected cells are considered as the instances that steer the\n");
		log("derivation process.\n");
		log("\n");
		log("    -base <base_module>\n");
		log("        instead of deriving the module that directly corresponds to each box\n");
		log("        instance, derive a specialization of <base_module> (this option applies\n");
		log("        to all selected box cells)\n");
		log("\n");
		log("    -naming_attr <attr>\n");
		log("        once a specialization is derived, use the value of the module attribute\n");
		log("        <attr> for a name which should be used for the derived module (this\n");
		log("        replaces the internal Yosys naming scheme in which the names of derived\n");
		log("        modules start with '$paramod$')\n");
		log("\n");
		log("    -liberty <file>\n"); // TODO
		log("\n");
		log("    -apply\n");
		log("        use the derived modules\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing BOX_DERIVE pass. (derive modules for boxes)\n");

		size_t argidx;
		IdString naming_attr;
		IdString base_name;
		std::string liberty_filename;
		std::ofstream* liberty_file = new std::ofstream;

		bool apply_mode;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-naming_attr" && argidx + 1 < args.size())
				naming_attr = RTLIL::escape_id(args[++argidx]);
			else if (args[argidx] == "-base" && argidx + 1 < args.size())
				base_name = RTLIL::escape_id(args[++argidx]);
			else if (args[argidx] == "-liberty" && argidx + 1 < args.size())
				liberty_filename = args[++argidx];
			else if (args[argidx] == "-apply")
				apply_mode = true;
			else
				break;
		}
		extra_args(args, argidx, d);

		if (liberty_filename.size()) {
			liberty_file->open(liberty_filename.c_str());
			if (liberty_file->fail()) {
				delete liberty_file;
				log_error("Can't open file `%s' for writing: %s\n", liberty_filename.c_str(), strerror(errno));
			}
		}

		Module *base_override = nullptr;
		if (!base_name.empty()) {
			base_override = d->module(base_name);
			if (!base_override)
				log_cmd_error("Base module %s not found.\n", log_id(base_name));
		}

		dict<std::pair<RTLIL::IdString, dict<RTLIL::IdString, RTLIL::Const>>, Module*> done;
		LibertyStubber stubber = {};

		if (liberty_file)
			stubber.liberty_prefix(*liberty_file);

		for (auto module : d->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				Module *inst_module = d->module(cell->type);
				if (!inst_module || !inst_module->get_blackbox_attribute())
					continue;

				Module *base = inst_module;
				if (base_override)
					base = base_override;

				auto index = std::make_pair(base->name, cell->parameters);

				if (cell->parameters.empty())
					continue;

				if (!done.count(index)) {
					IdString derived_type = base->derive(d, cell->parameters);
					Module *derived = d->module(derived_type);
					log_assert(derived && "Failed to derive module\n");
					log("derived %s\n", derived_type.c_str());

					if (!naming_attr.empty() && derived->has_attribute(naming_attr)) {
						IdString new_name = RTLIL::escape_id(derived->get_string_attribute(naming_attr));
						if (!new_name.isPublic())
							log_error("Derived module %s cannot be renamed to private name %s.\n",
									  log_id(derived), log_id(new_name));
						derived->attributes.erase(naming_attr);
						d->rename(derived, new_name);
					}

					if (liberty_file)
						stubber.liberty_cell(base, derived, *liberty_file);
					done[index] = derived;
				}

				if (apply_mode) {
					cell->type = done[index]->name;
					cell->parameters.clear();
				}
			}
		}

		if (liberty_file) {
			stubber.liberty_suffix(*liberty_file);
			delete liberty_file;
		}
	}
} BoxDerivePass;

PRIVATE_NAMESPACE_END
