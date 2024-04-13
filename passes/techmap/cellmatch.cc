#include "kernel/celltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/utils.h"

#include <algorithm>

USING_YOSYS_NAMESPACE
YOSYS_NAMESPACE_BEGIN

// return module's inputs in canonical order
SigSpec module_inputs(Module *m)
{
	SigSpec ret;
	for (auto port : m->ports) {
		Wire *w = m->wire(port);
		if (!w->port_input)
			continue;
		if (w->width != 1)
			log_error("Unsupported wide port (%s) of non-unit width found in module %s.\n",
					  log_id(w), log_id(m));
		ret.append(w);
	}
	return ret;
}

// return module's outputs in canonical order
SigSpec module_outputs(Module *m)
{
	SigSpec ret;
	for (auto port : m->ports) {
		Wire *w = m->wire(port);
		if (!w->port_output)
			continue;
		if (w->width != 1)
			log_error("Unsupported wide port (%s) of non-unit width found in module %s.\n",
					  log_id(w), log_id(m));
		ret.append(w);
	}
	return ret;
}

uint64_t permute_lut(uint64_t lut, const std::vector<int> &varmap)
{
	int k = varmap.size();
	uint64_t ret = 0;
	for (int j = 0; j < 1 << k; j++) {
		int m = 0;
		for (int l = 0; l < k; l++)
		if (j & 1 << l)
			m |= 1 << varmap[l];
		if (lut & 1 << m)
			ret |= 1 << j;
	}
	return ret;
}

uint64_t p_class(int k, uint64_t lut)
{
	std::vector<int> map;
	for (int j = 0; j < k; j++)
		map.push_back(j);

	uint64_t repr = ~(uint64_t) 0;
	std::vector<int> repr_vars;
	while (true) {
		uint64_t perm = permute_lut(lut, map);
		if (perm <= repr) {
			repr = perm;
			repr_vars = map;
		}
		if (!std::next_permutation(map.begin(), map.end()))
			break;
	}
	return repr;
}

bool derive_module_luts(Module *m, std::vector<uint64_t> &luts)
{
	CellTypes ff_types;
	ff_types.setup_stdcells_mem();
	for (auto cell : m->cells()) {
		if (ff_types.cell_known(cell->type)) {
			log("Ignoring module '%s' which isn't purely combinational.\n", log_id(m));
			return false;
		}
	}

	SigSpec inputs = module_inputs(m);
	SigSpec outputs = module_outputs(m);
	int ninputs = inputs.size(), noutputs = outputs.size();

	if (ninputs > 6) {
		log_warning("Skipping module %s with more than 6 inputs bits.\n", log_id(m));
		return false;
	}

	luts.clear();
	luts.resize(noutputs);

	ConstEval ceval(m);
	for (int i = 0; i < 1 << ninputs; i++) {
		ceval.clear();
		for (int j = 0; j < ninputs; j++)
			ceval.set(inputs[j], (i & (1 << j)) ? State::S1 : State::S0);
		for (int j = 0; j < noutputs; j++) {
			SigSpec bit = outputs[j];

			if (!ceval.eval(bit)) {
				log("Failed to evaluate output '%s' in module '%s'.\n",
					log_signal(outputs[j]), log_id(m));
				return false;
			}

			log_assert(ceval.eval(bit));

			if (bit[0] == State::S1)
				luts[j] |= 1 << i;
		}
	}

	return true;
}

struct CellmatchPass : Pass {
	CellmatchPass() : Pass("cellmatch", "match cells to their targets in cell library") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    cellmatch -lib <design> [module selection]\n");
		log("\n");
		log("This pass identifies functionally equivalent counterparts between each of the\n");
		log("selected modules and a module from the secondary design <design>. For every such\n");
		log("correspondence found, a techmap rule is generated for mapping instances of the\n");
		log("former to instances of the latter. This techmap rule is saved in yet another\n");
		log("design called '$cellmatch', which is created if non-existent.\n");
		log("\n");
		log("This pass restricts itself to combinational modules. Modules are functionally\n");
		log("equivalent as long as their truth tables are identical upto a permutation of\n");
		log("inputs and outputs. The supported number of inputs is limited to 6.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing CELLMATCH pass. (match cells)\n");

		size_t argidx;
		bool lut_attrs = false;
		Design *lib = NULL;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-lut_attrs") {
				// an undocumented debugging option
				lut_attrs = true;
			} else if (args[argidx] == "-lib" && argidx + 1 < args.size()) {
				if (!saved_designs.count(args[++argidx]))
					log_cmd_error("No design '%s' found!\n", args[argidx].c_str());
				lib = saved_designs.at(args[argidx]);
			} else {
				break;
			}
		}
		extra_args(args, argidx, d);

		if (!lib && !lut_attrs)
			log_cmd_error("Missing required -lib option.\n");

		struct Target {
			Module *module;
			std::vector<uint64_t> luts;
		};

		dict<pool<uint64_t>, std::vector<Target>> targets;

		if (lib)
		for (auto m : lib->modules()) {
			pool<uint64_t> p_classes;

			// produce a fingerprint in p_classes
			int ninputs = module_inputs(m).size();
			std::vector<uint64_t> luts;
			if (!derive_module_luts(m, luts))
				continue;
			for (auto lut : luts)
				p_classes.insert(p_class(ninputs, lut));
			
			log_debug("Registered %s\n", log_id(m));

			// save as a viable target
			targets[p_classes].push_back(Target{m, luts});
		}

		auto r = saved_designs.emplace("$cellmatch", nullptr);
		if (r.second)
			r.first->second = new Design;
		Design *map_design = r.first->second;

		for (auto m : d->selected_whole_modules_warn()) {
			std::vector<uint64_t> luts;
			if (!derive_module_luts(m, luts))
				continue;

			SigSpec inputs = module_inputs(m);
			SigSpec outputs = module_outputs(m);

			if (lut_attrs) {
				int no = 0;
				for (auto bit : outputs) {
					log_assert(bit.is_wire());
					bit.wire->attributes[ID(p_class)] = p_class(inputs.size(), luts[no]);
					bit.wire->attributes[ID(lut)] = luts[no++];	
				}
			}

			// fingerprint
			pool<uint64_t> p_classes;
			for (auto lut : luts)
				p_classes.insert(p_class(inputs.size(), lut));

			for (auto target : targets[p_classes]) {
				log_debug("Candidate %s for matching to %s\n", log_id(target.module), log_id(m));

				SigSpec target_inputs = module_inputs(target.module);
				SigSpec target_outputs = module_outputs(target.module);

				if (target_inputs.size() != inputs.size())
					continue;

				if (target_outputs.size() != outputs.size())
					continue;

				std::vector<int> input_map;
				for (int i = 0; i < inputs.size(); i++)
					input_map.push_back(i);

				bool found_match = false;
				while (!found_match) {
					std::vector<int> output_map;
					for (int i = 0; i < outputs.size(); i++)
						output_map.push_back(i);

					while (!found_match) {
						int out_no = 0;
						bool match = true;
						for (auto lut : luts) {
							if (permute_lut(target.luts[output_map[out_no++]], input_map) != lut) {
								match = false;
								break;
							}
						}

						if (match) {
							log("Module %s matches %s\n", log_id(m), log_id(target.module));
							Module *map = map_design->addModule(stringf("\\_60_%s_%s", log_id(m), log_id(target.module)));
							Cell *cell = map->addCell(ID::_TECHMAP_REPLACE_, target.module->name);

							map->attributes[ID(techmap_celltype)] = m->name.str();

							for (int i = 0; i < outputs.size(); i++) {
								log_assert(outputs[i].is_wire());
								Wire *w = map->addWire(outputs[i].wire->name, 1);
								w->port_id = outputs[i].wire->port_id;
								w->port_output = true;
								log_assert(target_outputs[output_map[i]].is_wire());
								cell->setPort(target_outputs[output_map[i]].wire->name, w);
							}

							for (int i = 0; i < inputs.size(); i++) {
								log_assert(inputs[i].is_wire());
								Wire *w = map->addWire(inputs[i].wire->name, 1);
								w->port_id = inputs[i].wire->port_id;
								w->port_input = true;
								log_assert(target_inputs[input_map[i]].is_wire());
								cell->setPort(target_inputs[input_map[i]].wire->name, w);
							}

							map->fixup_ports();
							found_match = true;
						}

						if (!std::next_permutation(output_map.begin(), output_map.end()))
							break;		
					}

					if (!std::next_permutation(input_map.begin(), input_map.end()))
						break;
				}
			}
		}
	}
} CellmatchPass;

YOSYS_NAMESPACE_END
