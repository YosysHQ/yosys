/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Alberto Gonzalez <boqwxp@airmail.cc>
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

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct GliftPass : public Pass {
	private:

	bool opt_create_precise_model, opt_create_imprecise_model, opt_create_instrumented_model;
	bool opt_taintconstants, opt_keepoutputs, opt_nocostmodel, opt_instrumentmore;
	std::vector<std::string> args;
	std::vector<std::string>::size_type argidx;
	std::vector<RTLIL::Wire *> new_taint_outputs;
	std::vector<RTLIL::SigSpec> meta_mux_selects;
	RTLIL::Module *module;

	const RTLIL::IdString cost_model_wire_name = ID(__glift_weight);

	void parse_args() {
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-create-precise-model") {
				opt_create_precise_model = true;
				continue;
			}
			if (args[argidx] == "-create-imprecise-model") {
				opt_create_imprecise_model = true;
				continue;
			}
			if (args[argidx] == "-create-instrumented-model") {
				opt_create_instrumented_model = true;
				continue;
			}
			if (args[argidx] == "-taint-constants") {
				opt_taintconstants = true;
				continue;
			}
			if (args[argidx] == "-keep-outputs") {
				opt_keepoutputs = true;
				continue;
			}
			if (args[argidx] == "-no-cost-model") {
				opt_nocostmodel = true;
				continue;
			}
			if (args[argidx] == "-instrument-more") {
				opt_instrumentmore = true;
				continue;
			}
			break;
		}
		if(!opt_create_precise_model && !opt_create_imprecise_model && !opt_create_instrumented_model)
			log_cmd_error("No command provided.  See help for usage.\n");
		if(static_cast<int>(opt_create_precise_model) + static_cast<int>(opt_create_imprecise_model) + static_cast<int>(opt_create_instrumented_model) != 1)
			log_cmd_error("Only one command may be specified.  See help for usage.\n");
	}

	RTLIL::SigSpec get_corresponding_taint_signal(RTLIL::SigSpec sig) {
		RTLIL::SigSpec ret;

		//Get the connected wire for the cell port:
		log_assert(sig.is_wire() || sig.is_fully_const());
		log_assert(sig.is_wire() || sig.is_fully_const());

		//Get a SigSpec for the corresponding taint signal for the cell port, creating one if necessary:
		if (sig.is_wire()) {
			RTLIL::Wire *w = module->wire(sig.as_wire()->name.str() + "_t");
			if (w == nullptr) w = module->addWire(sig.as_wire()->name.str() + "_t", 1);
			ret = w;
		}
		else if (sig.is_fully_const() && opt_taintconstants)
			ret = RTLIL::State::S1;
		else if (sig.is_fully_const())
			ret = RTLIL::State::S0;
		else
			log_cmd_error("Cell port SigSpec has unexpected type.\n");

		//Finally, if the cell port was a module input or output, make sure the corresponding taint signal is marked, too:
		if(sig.is_wire() && sig.as_wire()->port_input)
			ret.as_wire()->port_input = true;
		if(sig.is_wire() && sig.as_wire()->port_output)
			new_taint_outputs.push_back(ret.as_wire());

		return ret;
	}

	void add_precise_GLIFT_logic(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH2 or OR2_SH2
		RTLIL::SigSpec n_port_a = module->LogicNot(cell->name.str() + "_t_1_1", port_a, false, cell->get_src_attribute());
		RTLIL::SigSpec n_port_b = module->LogicNot(cell->name.str() + "_t_1_2", port_b, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_1_3", (cell->type == "$_AND_")? port_a : n_port_a, port_b_taint, false, cell->get_src_attribute());
		auto subexpr2 = module->And(cell->name.str() + "_t_1_4", (cell->type == "$_AND_")? port_b : n_port_b, port_a_taint, false, cell->get_src_attribute());
		auto subexpr3 = module->And(cell->name.str() + "_t_1_5", port_a_taint, port_b_taint, false, cell->get_src_attribute());
		auto subexpr4 = module->Or(cell->name.str() + "_t_1_6", subexpr1, subexpr2, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_1_7", subexpr4, subexpr3, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_1(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH3 or OR2_SH3
		RTLIL::SigSpec n_port_a = module->LogicNot(cell->name.str() + "_t_2_1", port_a, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_2_2", (cell->type == "$_AND_")? port_b : n_port_a, (cell->type == "$_AND_")? port_a_taint : port_b_taint, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_2_3", (cell->type == "$_AND_")? port_b_taint : port_a_taint, subexpr1, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_2(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH4 or OR2_SH4
		RTLIL::SigSpec n_port_b = module->LogicNot(cell->name.str() + "_t_3_1", port_b, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_3_2", (cell->type == "$_AND_")? port_a : n_port_b, (cell->type == "$_AND_")? port_b_taint : port_a_taint, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_3_3", (cell->type == "$_AND_")? port_a_taint : port_b_taint, subexpr1, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_3(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH5 or OR2_SH5
		module->addOr(cell->name.str() + "_t_4_1", port_a_taint, port_b_taint, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_4(RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_y_taint) {
		module->connect(port_y_taint, port_a_taint);
	}

	void add_imprecise_GLIFT_logic_5(RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		module->connect(port_y_taint, port_b_taint);
	}

	void add_imprecise_GLIFT_logic_6(RTLIL::SigSpec &port_y_taint) {
		module->connect(port_y_taint, RTLIL::Const(1, 1));
	}

	void add_imprecise_GLIFT_logic_7(RTLIL::SigSpec &port_y_taint) {
		module->connect(port_y_taint, RTLIL::Const(0, 1));
	}

	RTLIL::SigSpec score_metamux_select(const RTLIL::SigSpec &metamux_select) {
		log_assert(metamux_select.is_wire());

		auto num_versions = opt_instrumentmore? 8 : 4;
		auto select_width = log2(num_versions);
		log_assert(metamux_select.as_wire()->width == select_width);

		std::vector<RTLIL::Const> costs = {5, 2, 2, 1, 0, 0, 0, 0}; //in terms of AND/OR gates

		std::vector<RTLIL::SigSpec> next_pmux_y_ports, pmux_y_ports(costs.begin(), costs.begin() + num_versions);
		for (auto i = 0; pmux_y_ports.size() > 1; ++i) {
			for (auto j = 0; j+1 < GetSize(pmux_y_ports); j += 2) {
				next_pmux_y_ports.emplace_back(module->Pmux(stringf("%s_mux_%d_%d", metamux_select.as_wire()->name.c_str(), i, j), pmux_y_ports[j], pmux_y_ports[j+1], metamux_select[GetSize(metamux_select) - 1 - i], metamux_select.as_wire()->get_src_attribute()));
			}
			if (GetSize(pmux_y_ports) % 2 == 1)
				next_pmux_y_ports.push_back(pmux_y_ports[GetSize(pmux_y_ports) - 1]);
			pmux_y_ports.swap(next_pmux_y_ports);
			next_pmux_y_ports.clear();
		}

		log_assert(pmux_y_ports.size() == 1);
		return pmux_y_ports[0];
	}

	void create_glift_logic() {
		std::vector<RTLIL::SigSig> connections(module->connections());

		for(auto &cell : module->cells().to_vector()) {
			if (!cell->type.in("$_AND_", "$_OR_", "$_NOT_", "$anyconst", "$allconst", "$assume", "$assert")) {
				log_cmd_error("Invalid cell type \"%s\" found.  Module must be techmapped.\n", cell->type.c_str());
			}
			if (cell->type.in("$_AND_", "$_OR_")) {
				const unsigned int A = 0, B = 1, Y = 2;
				const unsigned int NUM_PORTS = 3;
				RTLIL::SigSpec ports[NUM_PORTS] = {cell->getPort(ID::A), cell->getPort(ID::B), cell->getPort(ID::Y)};
				RTLIL::SigSpec port_taints[NUM_PORTS];

				if (ports[A].size() != 1 || ports[B].size() != 1 || ports[Y].size() != 1)
					log_cmd_error("Multi-bit signal found.  Run `splitnets` first.\n");
				for (unsigned int i = 0; i < NUM_PORTS; ++i)
					port_taints[i] = get_corresponding_taint_signal(ports[i]);

				if (opt_create_precise_model)
					add_precise_GLIFT_logic(cell, ports[A], port_taints[A], ports[B], port_taints[B], port_taints[Y]);
				else if (opt_create_imprecise_model)
					add_imprecise_GLIFT_logic_3(cell, port_taints[A], port_taints[B], port_taints[Y]);
				else if (opt_create_instrumented_model) {
					std::vector<RTLIL::SigSpec> taint_version;
					int num_versions = opt_instrumentmore? 8 : 4;

					for (auto i = 1; i <= num_versions; ++i)
						taint_version.emplace_back(RTLIL::SigSpec(module->addWire(stringf("%s_y%d", cell->name.c_str(), i), 1)));

					for (auto i = 0; i < num_versions; ++i) {
						switch(i) {
							case 0: add_precise_GLIFT_logic(cell, ports[A], port_taints[A], ports[B], port_taints[B], taint_version[i]);
							break;
							case 1: add_imprecise_GLIFT_logic_1(cell, ports[A], port_taints[A], ports[B], port_taints[B], taint_version[i]);
							break;
							case 2: add_imprecise_GLIFT_logic_2(cell, ports[A], port_taints[A], ports[B], port_taints[B], taint_version[i]);
							break;
							case 3: add_imprecise_GLIFT_logic_3(cell, port_taints[A], port_taints[B], taint_version[i]);
							break;
							case 4: add_imprecise_GLIFT_logic_4(port_taints[A], taint_version[i]);
							break;
							case 5: add_imprecise_GLIFT_logic_5(port_taints[B], taint_version[i]);
							break;
							case 6: add_imprecise_GLIFT_logic_6(taint_version[i]);
							break;
							case 7: add_imprecise_GLIFT_logic_7(taint_version[i]);
							break;
							default: log_assert(false);
						}
					}

					auto select_width = log2(num_versions);
					log_assert(exp2(select_width) == num_versions);
					RTLIL::SigSpec meta_mux_select(module->addWire(cell->name.str() + "_sel", select_width));
					meta_mux_selects.push_back(meta_mux_select);
					module->connect(meta_mux_select, module->Anyconst(cell->name.str() + "_hole", select_width, cell->get_src_attribute()));

					std::vector<RTLIL::SigSpec> next_meta_mux_y_ports, meta_mux_y_ports(taint_version);
					for (auto i = 0; meta_mux_y_ports.size() > 1; ++i) {
						for (auto j = 0; j+1 < GetSize(meta_mux_y_ports); j += 2) {
							next_meta_mux_y_ports.emplace_back(module->Mux(stringf("%s_mux_%d_%d", cell->name.c_str(), i, j), meta_mux_y_ports[j], meta_mux_y_ports[j+1], meta_mux_select[GetSize(meta_mux_select) - 1 - i]));
						}
						if (GetSize(meta_mux_y_ports) % 2 == 1)
							next_meta_mux_y_ports.push_back(meta_mux_y_ports[GetSize(meta_mux_y_ports) - 1]);
						meta_mux_y_ports.swap(next_meta_mux_y_ports);
						next_meta_mux_y_ports.clear();
					}
					log_assert(meta_mux_y_ports.size() == 1);
					module->connect(port_taints[Y], meta_mux_y_ports[0]);
				}
				else log_cmd_error("This is a bug (1).\n");
			}
			else if (cell->type.in("$_NOT_")) {
				const unsigned int A = 0, Y = 1;
				const unsigned int NUM_PORTS = 2;
				RTLIL::SigSpec ports[NUM_PORTS] = {cell->getPort(ID::A), cell->getPort(ID::Y)};
				RTLIL::SigSpec port_taints[NUM_PORTS];

				if (ports[A].size() != 1 || ports[Y].size() != 1)
					log_cmd_error("Multi-bit signal found.  Run `splitnets` first.\n");
				for (unsigned int i = 0; i < NUM_PORTS; ++i)
					port_taints[i] = get_corresponding_taint_signal(ports[i]);

				if (cell->type == "$_NOT_") {
					module->connect(port_taints[Y], port_taints[A]);
				}
				else log_cmd_error("This is a bug (2).\n");
			}
		} //end foreach cell in cells

		for (auto &conn : connections) {
			RTLIL::SigSpec first = get_corresponding_taint_signal(conn.first);
			RTLIL::SigSpec second = get_corresponding_taint_signal(conn.second);

			module->connect(get_corresponding_taint_signal(conn.first), get_corresponding_taint_signal(conn.second));

			if(conn.second.is_wire() && conn.second.as_wire()->port_input)
				second.as_wire()->port_input = true;
			if(conn.first.is_wire() && conn.first.as_wire()->port_output)
				new_taint_outputs.push_back(first.as_wire());
		} //end foreach conn in connections

		//Create a rough model of area by summing the "weight" score of each meta-mux select:
		if (!opt_nocostmodel) {
			std::vector<RTLIL::SigSpec> meta_mux_select_sums;
			std::vector<RTLIL::SigSpec> meta_mux_select_sums_buf;
			for (auto &wire : meta_mux_selects) {
				meta_mux_select_sums.emplace_back(score_metamux_select(wire));
			}
			for (unsigned int i = 0; meta_mux_select_sums.size() > 1; ) {
				meta_mux_select_sums_buf.clear();
				for (i = 0; i + 1 < meta_mux_select_sums.size(); i += 2) {
					meta_mux_select_sums_buf.push_back(module->Add(meta_mux_select_sums[i].as_wire()->name.str() + "_add", meta_mux_select_sums[i], meta_mux_select_sums[i+1], false));
				}
				if (meta_mux_select_sums.size() % 2 == 1)
					meta_mux_select_sums_buf.push_back(meta_mux_select_sums[meta_mux_select_sums.size()-1]);
				meta_mux_select_sums.swap(meta_mux_select_sums_buf);
			}
			if (meta_mux_select_sums.size() > 0) {
				meta_mux_select_sums[0].as_wire()->set_bool_attribute("\\minimize");
				meta_mux_select_sums[0].as_wire()->set_bool_attribute("\\keep");
				module->rename(meta_mux_select_sums[0].as_wire(), cost_model_wire_name);
			}
		}

		//Mark new module outputs:
		for (auto &port_name : module->ports) {
			RTLIL::Wire *port = module->wire(port_name);
			log_assert(port != nullptr);
			if (port->port_output && !opt_keepoutputs)
				port->port_output = false;
		}
		for (auto &output : new_taint_outputs)
			output->port_output = true;
		module->fixup_ports(); //we have some new taint signals in the module interface
	}

	void reset() {
		opt_create_precise_model = false;
		opt_create_imprecise_model = false;
		opt_create_instrumented_model = false;
		opt_taintconstants = false;
		opt_keepoutputs = false;
		opt_nocostmodel = false;
		opt_instrumentmore = false;
		module = nullptr;
		args.clear();
		argidx = 0;
		new_taint_outputs.clear();
		meta_mux_selects.clear();
	}

	public:

	GliftPass() : Pass("glift", "create GLIFT models and optimization problems"), opt_create_precise_model(false), opt_create_imprecise_model(false), opt_create_instrumented_model(false), opt_taintconstants(false), opt_keepoutputs(false), opt_nocostmodel(false), opt_instrumentmore(false), module(nullptr) { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    glift <command> [options] [selection]\n");
		log("\n");
		log("Augments the current or specified module with gate-level information flow tracking\n");
		log("(GLIFT) logic using the \"constructive mapping\" approach. Also can set up QBF-SAT\n");
		log("optimization problems in order to optimize GLIFT models or trade off precision and\n");
		log("complexity.\n");
		log("\n");
		log("\n");
		log("Commands:\n");
		log("\n");
		log("  -create-precise-model\n");
		log("    Replaces the current or specified module with one that has corresponding \"taint\"\n");
		log("    inputs, outputs, and internal nets along with precise taint tracking logic.\n");
		log("    For example, precise taint tracking logic for an AND gate is:\n");
		log("\n");
		log("      y_t = a & b_t | b & a_t | a_t & b_t\n");
		log("\n");
		log("\n");
		log("  -create-imprecise-model\n");
		log("    Replaces the current or specified module with one that has corresponding \"taint\"\n");
		log("    inputs, outputs, and internal nets along with imprecise \"All OR\" taint tracking\n");
		log("    logic:\n");
		log("\n");
		log("      y_t = a_t | b_t\n");
		log("\n");
		log("\n");
		log("  -create-instrumented-model\n");
		log("    Replaces the current or specified module with one that has corresponding \"taint\"\n");
		log("    inputs, outputs, and internal nets along with 4 varying-precision versions of taint\n");
		log("    tracking logic. Which version of taint tracking logic is used for a given gate is\n");
		log("    determined by a MUX selected by an $anyconst cell.  By default, unless the\n");
		log("    `-no-cost-model` option is provided, an additional wire named `__glift_weight` with\n");
		log("    the `keep` and `minimize` attributes is added to the module along with pmuxes and\n");
		log("    adders to calculate a rough estimate of the number of logic gates in the GLIFT model\n");
		log("    given an assignment for the $anyconst cells. The four versions of taint tracking logic\n");
		log("    for an AND gate are:");
		log("\n");
		log("      y_t = a & b_t | b & a_t | a_t & b_t           (like `-create-precise-model`)\n");
		log("      y_t = a_t | a & b_t\n");
		log("      y_t = b_t | b & a_t\n");
		log("      y_t = a_t | b_t                               (like `-create-imprecise-model`)\n");
		log("\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("  -taint-constants\n");
		log("    Constant values in the design are labeled as tainted.\n");
		log("    (default: label constants as un-tainted)\n");
		log("\n");
		log("  -keep-outputs\n");
		log("    Do not remove module outputs. Taint tracking outputs will appear in the module ports\n");
		log("    alongside the orignal outputs.\n");
		log("    (default: original module outputs are removed)\n");
		log("\n");
		log("  -no-cost-model\n");
		log("    Do not model taint tracking logic area and do not create a `__glift_weight` wire.\n");
		log("    Only applicable in combination with `-create-instrumented-model`.\n");
		log("    (default: model area and give that wire the \"keep\" and \"minimize\" attributes)\n");
		log("\n");
		log("  -instrument-more\n");
		log("    Allow choice from more versions of (even simpler) taint tracking logic. A total\n");
		log("    of 8 versions of taint tracking logic will be added per gate, including the 4\n");
		log("    versions from `-create-instrumented-model` and these additional versions:\n");
		log("\n");
		log("      y_t = a_t\n");
		log("      y_t = b_t\n");
		log("      y_t = 1\n");
		log("      y_t = 0\n");
		log("\n");
		log("    Only applicable in combination with `-create-instrumented-model`.\n");
		log("    (default: do not add more versions of taint tracking logic.\n");
		log("\n");
	}

	void execute(std::vector<std::string> _args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing GLIFT pass (creating and manipulating GLIFT models).\n");

		reset();
		args = _args;
		parse_args();
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module may be selected for the glift pass! Flatten the design if necessary. (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == nullptr)
			log_cmd_error("Can't operate on an empty selection!\n");

		create_glift_logic();
	}
} GliftPass;

PRIVATE_NAMESPACE_END
