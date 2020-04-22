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

	bool opt_create, opt_sketchify, opt_taintconstants;
	std::vector<std::string> args;
	std::vector<std::string>::size_type argidx;
	RTLIL::Module *module;

	void parse_args() {
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-create") {
				opt_create = true;
				continue;
			}
			if (args[argidx] == "-sketchify") {
				opt_sketchify = true;
				continue;
			}
			if (args[argidx] == "-taint-constants") {
				opt_taintconstants = true;
				continue;
			}
			break;
		}
		if(!opt_create && !opt_sketchify) log_cmd_error("One of `-create` or `-sketchify` must be specified.\n");
		if(opt_create && opt_sketchify) log_cmd_error("Only one of `-create` or `-sketchify` may be specified.\n");
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
			ret.as_wire()->port_output = true;

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

	void create_glift_logic() {
		std::vector<RTLIL::SigSig> connections(module->connections());
		std::vector<RTLIL::SigSig> new_connections;

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

				if (opt_create)
					add_precise_GLIFT_logic(cell, ports[A], port_taints[A], ports[B], port_taints[B], port_taints[Y]);
				else if (opt_sketchify) {
					RTLIL::SigSpec precise_y(module->addWire(cell->name.str() + "_y1", 1)),
							imprecise_1_y(module->addWire(cell->name.str() + "_y2", 1)),
							imprecise_2_y(module->addWire(cell->name.str() + "_y3", 1)),
							imprecise_3_y(module->addWire(cell->name.str() + "_y4", 1));

					add_precise_GLIFT_logic(cell, ports[A], port_taints[A], ports[B], port_taints[B], precise_y);
					add_imprecise_GLIFT_logic_1(cell, ports[A], port_taints[A], ports[B], port_taints[B], imprecise_1_y);
					add_imprecise_GLIFT_logic_2(cell, ports[A], port_taints[A], ports[B], port_taints[B], imprecise_2_y);
					add_imprecise_GLIFT_logic_3(cell, port_taints[A], port_taints[B], imprecise_3_y);

					RTLIL::SigSpec meta_mux_select(module->addWire(cell->name.str() + "_sel", 2));
					meta_mux_select.as_wire()->set_bool_attribute("\\maximize");
					new_connections.emplace_back(meta_mux_select, module->Anyconst(cell->name.str() + "_hole", 2, cell->get_src_attribute()));
					RTLIL::SigSpec meta_mux1(module->Mux(cell->name.str() + "_mux1", precise_y, imprecise_1_y, meta_mux_select[1]));
					RTLIL::SigSpec meta_mux2(module->Mux(cell->name.str() + "_mux2", imprecise_2_y, imprecise_3_y, meta_mux_select[1]));
					module->addMux(cell->name.str() + "_mux3", meta_mux1, meta_mux2, meta_mux_select[0], port_taints[Y]);
				}
				else log_cmd_error("This is a bug (2).\n");
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
					new_connections.emplace_back(port_taints[Y], port_taints[A]);
				}
				else log_cmd_error("This is a bug (3).\n");
			}
		} //end foreach cell in cells

		for (auto &conn : connections) {
			RTLIL::SigSpec first = get_corresponding_taint_signal(conn.first);
			RTLIL::SigSpec second = get_corresponding_taint_signal(conn.second);

			module->connect(get_corresponding_taint_signal(conn.first), get_corresponding_taint_signal(conn.second));

			if(conn.second.is_wire() && conn.second.as_wire()->port_input)
				second.as_wire()->port_input = true;
			if(conn.first.is_wire() && conn.first.as_wire()->port_output)
				first.as_wire()->port_output = true;
		} //end foreach conn in connections

		for (auto &conn : new_connections)
			module->connect(conn);

		module->fixup_ports(); //we have some new taint signals in the module interface
	}

	public:

	GliftPass() : Pass("glift", "create and transform GLIFT models"), opt_create(false), opt_sketchify(false), opt_taintconstants(false), module(nullptr) { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    glift -create|-sketchify [options] [selection]\n");
		log("\n");
		log("Adds, removes, or manipulates gate-level information flow tracking (GLIFT) logic\n");
		log("to the current or specified module.\n");
		log("\n");
		log("Commands:");
		log("\n");
		log("  -create");
		log("    Replaces the current or specified module with one that has additional \"taint\"\n");
		log("    inputs, outputs, and internal nets along with precise taint-tracking logic.\n");
		log("\n");
		log("  -sketchify");
		log("    Replaces the current or specified module with one that has additional \"taint\"\n");
		log("    inputs, outputs, and internal nets along with varying-precision taint-tracking logic.\n");
		log("    Which version of taint tracking logic is used at a given cell is determined by a MUX\n");
		log("    selected by an $anyconst cell.\n");
		log("\n");
		log("Options:");
		log("\n");
		log("  -taint-constants");
		log("    Constant values in the design are labeled as tainted.\n");
		log("    (default: label constants as un-tainted)\n");
		log("\n");
	}
	void execute(std::vector<std::string> _args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing GLIFT pass (creating and manipulating GLIFT models).\n");

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
