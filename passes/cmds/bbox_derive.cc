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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BboxDerivePass : Pass {
	BboxDerivePass() : Pass("bbox_derive", "derive blackbox modules") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bbox_derive [-base <base_module>] [-naming_attr <attr>] [selection]\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing BBOX_DERIVE pass. (derive modules for blackboxes)\n");

		size_t argidx;
		IdString naming_attr;
		IdString base_name;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-naming_attr" && argidx + 1 < args.size())
				naming_attr = RTLIL::escape_id(args[++argidx]);
			else if (args[argidx] == "-base" && argidx + 1 < args.size())
				base_name = RTLIL::escape_id(args[++argidx]);
			else
				break;
		}
		extra_args(args, argidx, d);

		Module *base_override;
		if (!base_name.empty()) {
			base_override = d->module(base_name);
			if (!base_override)
				log_cmd_error("Base module %s not found.\n", log_id(base_name));
		}

		dict<dict<RTLIL::IdString, RTLIL::Const>, Module*> done;

		for (auto module : d->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				Module *inst_module = d->module(cell->type);
				if (!inst_module || !inst_module->get_blackbox_attribute())
					continue;

				if (cell->parameters.empty() || done.count(cell->parameters))
					continue;

				Module *base = inst_module;
				if (base_override)
					base = base_override;

				IdString derived_type = base->derive(d, cell->parameters);
				Module *derived = d->module(derived_type);

				if (!naming_attr.empty() && derived->has_attribute(naming_attr)) {
					IdString new_name = RTLIL::escape_id(derived->get_string_attribute(naming_attr));
					if (!new_name.isPublic())
						log_error("Derived module %s cannot be renamed to private name %s.\n",
								  log_id(derived), log_id(new_name));
					derived->attributes.erase(naming_attr);
					d->rename(derived, new_name);
				}

				done[cell->parameters] = derived;
			}
		}
	}
} BboxDerivePass;

PRIVATE_NAMESPACE_END
