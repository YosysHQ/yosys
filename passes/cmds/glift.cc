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
#include "kernel/utils.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct GliftWorker {
private:
	bool is_top_module = false;
	bool opt_create_precise_model = false, opt_create_imprecise_model = false, opt_create_instrumented_model = false;
	bool opt_taintconstants = false, opt_keepoutputs = false, opt_simplecostmodel = false, opt_nocostmodel = false;
	bool opt_instrumentmore = false;
	std::vector<RTLIL::Wire *> new_taint_outputs;
	std::vector<std::pair<RTLIL::SigSpec, RTLIL::IdString>> meta_mux_selects;
	RTLIL::Module *module = nullptr;

	const RTLIL::IdString cost_model_wire_name = ID(__glift_weight);
	const RTLIL::IdString glift_attribute_name = ID(glift);


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
		bool is_and = cell->type.in(ID($_AND_), ID($_NAND_));
		RTLIL::SigSpec n_port_a = module->LogicNot(cell->name.str() + "_t_1_1", port_a, false, cell->get_src_attribute());
		RTLIL::SigSpec n_port_b = module->LogicNot(cell->name.str() + "_t_1_2", port_b, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_1_3", is_and? port_a : n_port_a, port_b_taint, false, cell->get_src_attribute());
		auto subexpr2 = module->And(cell->name.str() + "_t_1_4", is_and? port_b : n_port_b, port_a_taint, false, cell->get_src_attribute());
		auto subexpr3 = module->And(cell->name.str() + "_t_1_5", port_a_taint, port_b_taint, false, cell->get_src_attribute());
		auto subexpr4 = module->Or(cell->name.str() + "_t_1_6", subexpr1, subexpr2, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_1_7", subexpr4, subexpr3, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_1(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH3 or OR2_SH3
		bool is_and = cell->type.in(ID($_AND_), ID($_NAND_));
		RTLIL::SigSpec n_port_a = module->LogicNot(cell->name.str() + "_t_2_1", port_a, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_2_2", is_and? port_b : n_port_a, is_and? port_a_taint : port_b_taint, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_2_3", is_and? port_b_taint : port_a_taint, subexpr1, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_2(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH4 or OR2_SH4
		bool is_and = cell->type.in(ID($_AND_), ID($_NAND_));
		RTLIL::SigSpec n_port_b = module->LogicNot(cell->name.str() + "_t_3_1", port_b, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_3_2", is_and? port_a : n_port_b, is_and? port_b_taint : port_a_taint, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_3_3", is_and? port_a_taint : port_b_taint, subexpr1, port_y_taint, false, cell->get_src_attribute());
	}

	void add_imprecise_GLIFT_logic_3(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_y_taint) {
		//AKA AN2_SH5 or OR2_SH5 or XR2_SH2
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

	void add_precise_GLIFT_mux(const RTLIL::Cell *cell, RTLIL::SigSpec &port_a, RTLIL::SigSpec &port_a_taint, RTLIL::SigSpec &port_b, RTLIL::SigSpec &port_b_taint, RTLIL::SigSpec &port_s, RTLIL::SigSpec &port_s_taint, RTLIL::SigSpec &port_y_taint) {
		//S&At | ~S&Bt | ~A&B&St | A&~B&St | At&St | Bt&St
		RTLIL::SigSpec n_port_a = module->LogicNot(cell->name.str() + "_t_4_1", port_a, false, cell->get_src_attribute());
		RTLIL::SigSpec n_port_b = module->LogicNot(cell->name.str() + "_t_4_2", port_b, false, cell->get_src_attribute());
		RTLIL::SigSpec n_port_s = module->LogicNot(cell->name.str() + "_t_4_3", port_s, false, cell->get_src_attribute());
		auto subexpr1 = module->And(cell->name.str() + "_t_4_4", port_s, port_a_taint, false, cell->get_src_attribute());
		auto subexpr2 = module->And(cell->name.str() + "_t_4_5", n_port_s, port_b_taint, false, cell->get_src_attribute());
		auto subexpr3 = module->And(cell->name.str() + "_t_4_6", n_port_a, port_b, false, cell->get_src_attribute());
		auto subexpr4 = module->And(cell->name.str() + "_t_4_7", subexpr3, port_s_taint, false, cell->get_src_attribute());
		auto subexpr5 = module->And(cell->name.str() + "_t_4_8", port_a, n_port_b, false, cell->get_src_attribute());
		auto subexpr6 = module->And(cell->name.str() + "_t_4_9", subexpr5, port_s_taint, false, cell->get_src_attribute());
		auto subexpr7 = module->And(cell->name.str() + "_t_4_10", port_a_taint, port_s_taint, false, cell->get_src_attribute());
		auto subexpr8 = module->And(cell->name.str() + "_t_4_11", port_b_taint, port_s_taint, false, cell->get_src_attribute());
		auto subexpr9  = module->Or(cell->name.str() + "_t_4_12", subexpr1, subexpr2, false, cell->get_src_attribute());
		auto subexpr10 = module->Or(cell->name.str() + "_t_4_13", subexpr4, subexpr6, false, cell->get_src_attribute());
		auto subexpr11 = module->Or(cell->name.str() + "_t_4_14", subexpr7, subexpr8, false, cell->get_src_attribute());
		auto subexpr12 = module->Or(cell->name.str() + "_t_4_15", subexpr9, subexpr10, false, cell->get_src_attribute());
		module->addOr(cell->name.str() + "_t_4_16", subexpr11, subexpr12, port_y_taint, false, cell->get_src_attribute());
	}

	RTLIL::SigSpec score_metamux_select(const RTLIL::SigSpec &metamux_select, const RTLIL::IdString celltype) {
		log_assert(metamux_select.is_wire());

		if (opt_simplecostmodel) {
			//The complex model is an area model, so a lower score should mean smaller.
			//In this case, a nonzero hole metamux select value means less logic.
			//Thus we should invert the ReduceOr over the metamux_select signal.
			RTLIL::SigSpec pmux_select = module->ReduceOr(metamux_select.as_wire()->name.str() + "_nonzero", metamux_select);
			return module->Pmux(NEW_ID, RTLIL::Const(1), RTLIL::Const(0), pmux_select, metamux_select.as_wire()->get_src_attribute());
		} else {
			auto select_width = metamux_select.as_wire()->width;

			std::vector<RTLIL::Const> costs;
			if (celltype == ID($_AND_) || celltype == ID($_OR_)) {
				costs = {5, 2, 2, 1, 0, 0, 0, 0};
				log_assert(select_width == 2 || select_width == 3);
				log_assert(opt_instrumentmore || select_width == 2);
				log_assert(!opt_instrumentmore || select_width == 3);
			}
			else if (celltype == ID($_XOR_) || celltype == ID($_XNOR_)) {
				costs = {1, 0, 0, 0};
				log_assert(select_width == 2);
			}

			std::vector<RTLIL::SigSpec> next_pmux_y_ports, pmux_y_ports(costs.begin(), costs.begin() + exp2(select_width));
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
	}

	void create_glift_logic() {
		if (module->get_bool_attribute(glift_attribute_name))
			return;

		std::vector<RTLIL::SigSig> connections(module->connections());

		for(auto &cell : module->cells().to_vector()) {
			if (!cell->type.in({ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_MUX_), ID($_NMUX_), ID($_NOT_), ID($anyconst), ID($allconst), ID($assume), ID($assert)}) && module->design->module(cell->type) == nullptr) {
				log_cmd_error("Unsupported cell type \"%s\" found.  Run `techmap` first.\n", cell->type.c_str());
			}
			if (cell->type.in(ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_))) {
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
					meta_mux_selects.push_back(make_pair(meta_mux_select, cell->type));
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
			else if (cell->type.in(ID($_XOR_), ID($_XNOR_))) {
				const unsigned int A = 0, B = 1, Y = 2;
				const unsigned int NUM_PORTS = 3;
				RTLIL::SigSpec ports[NUM_PORTS] = {cell->getPort(ID::A), cell->getPort(ID::B), cell->getPort(ID::Y)};
				RTLIL::SigSpec port_taints[NUM_PORTS];

				if (ports[A].size() != 1 || ports[B].size() != 1 || ports[Y].size() != 1)
					log_cmd_error("Multi-bit signal found.  Run `splitnets` first.\n");
				for (unsigned int i = 0; i < NUM_PORTS; ++i)
					port_taints[i] = get_corresponding_taint_signal(ports[i]);

				if (opt_create_precise_model || opt_create_imprecise_model)
					add_imprecise_GLIFT_logic_3(cell, port_taints[A], port_taints[B], port_taints[Y]);
				else if (opt_create_instrumented_model) {
					std::vector<RTLIL::SigSpec> taint_version;
					int num_versions = 4;
					auto select_width = log2(num_versions);
					log_assert(exp2(select_width) == num_versions);

					for (auto i = 1; i <= num_versions; ++i)
						taint_version.emplace_back(RTLIL::SigSpec(module->addWire(stringf("%s_y%d", cell->name.c_str(), i), 1)));

					for (auto i = 0; i < num_versions; ++i) {
						switch(i) {
							case 0: add_imprecise_GLIFT_logic_3(cell, port_taints[A], port_taints[B], taint_version[i]);
							break;
							case 1: add_imprecise_GLIFT_logic_4(port_taints[A], taint_version[i]);
							break;
							case 2: add_imprecise_GLIFT_logic_5(port_taints[B], taint_version[i]);
							break;
							case 3: add_imprecise_GLIFT_logic_6(taint_version[i]);
							break;
							default: log_assert(false);
						}
					}

					RTLIL::SigSpec meta_mux_select(module->addWire(cell->name.str() + "_sel", select_width));
					meta_mux_selects.push_back(make_pair(meta_mux_select, cell->type));
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
				else log_cmd_error("This is a bug (2).\n");

			}
			else if (cell->type.in(ID($_MUX_), ID($_NMUX_))) {
				const unsigned int A = 0, B = 1, S = 2, Y = 3;
				const unsigned int NUM_PORTS = 4;
				RTLIL::SigSpec ports[NUM_PORTS] = {cell->getPort(ID::A), cell->getPort(ID::B), cell->getPort(ID::S), cell->getPort(ID::Y)};
				RTLIL::SigSpec port_taints[NUM_PORTS];

				if (ports[A].size() != 1 || ports[B].size() != 1 || ports[S].size() != 1 || ports[Y].size() != 1)
					log_cmd_error("Multi-bit signal found.  Run `splitnets` first.\n");
				for (unsigned int i = 0; i < NUM_PORTS; ++i)
					port_taints[i] = get_corresponding_taint_signal(ports[i]);

				add_precise_GLIFT_mux(cell, ports[A], port_taints[A], ports[B], port_taints[B], ports[S], port_taints[S], port_taints[Y]);
			}
			else if (cell->type.in(ID($_NOT_))) {
				const unsigned int A = 0, Y = 1;
				const unsigned int NUM_PORTS = 2;
				RTLIL::SigSpec ports[NUM_PORTS] = {cell->getPort(ID::A), cell->getPort(ID::Y)};
				RTLIL::SigSpec port_taints[NUM_PORTS];

				if (ports[A].size() != 1 || ports[Y].size() != 1)
					log_cmd_error("Multi-bit signal found.  Run `splitnets` first.\n");
				for (unsigned int i = 0; i < NUM_PORTS; ++i)
					port_taints[i] = get_corresponding_taint_signal(ports[i]);

				if (cell->type == ID($_NOT_)) {
					module->connect(port_taints[Y], port_taints[A]);
				}
				else log_cmd_error("This is a bug (3).\n");
			}
			else if (module->design->module(cell->type) != nullptr) {
				//User cell type
				//This function is called on modules according to topological order, so we do not need to
				//recurse to GLIFT model the child module. However, we need to augment the ports list
				//with taint signals and connect the new ports to the corresponding taint signals.
				RTLIL::Module *cell_module_def = module->design->module(cell->type);
				dict<RTLIL::IdString, RTLIL::SigSpec> orig_ports = cell->connections();
				log("Adding cell %s\n", cell_module_def->name.c_str());
				for (auto &it : orig_ports) {
					RTLIL::SigSpec port = it.second;
					RTLIL::SigSpec port_taint = get_corresponding_taint_signal(port);

					log_assert(port_taint.is_wire());
					log_assert(std::find(cell_module_def->ports.begin(), cell_module_def->ports.end(), port_taint.as_wire()->name) != cell_module_def->ports.end());
					cell->setPort(port_taint.as_wire()->name, port_taint);
				}
			}
			else log_cmd_error("This is a bug (4).\n");
		} //end foreach cell in cells

		for (auto &conn : connections) {
			RTLIL::SigSpec first = get_corresponding_taint_signal(conn.first);
			RTLIL::SigSpec second = get_corresponding_taint_signal(conn.second);

			module->connect(first, second);

			if(conn.second.is_wire() && conn.second.as_wire()->port_input)
				second.as_wire()->port_input = true;
			if(conn.first.is_wire() && conn.first.as_wire()->port_output)
				new_taint_outputs.push_back(first.as_wire());
		} //end foreach conn in connections

		//Create a rough model of area by summing the (potentially simplified) "weight" score of each meta-mux select:
		if (!opt_nocostmodel) {
			std::vector<RTLIL::SigSpec> meta_mux_select_sums;
			std::vector<RTLIL::SigSpec> meta_mux_select_sums_buf;
			for (auto &it : meta_mux_selects) {
				meta_mux_select_sums.emplace_back(score_metamux_select(it.first, it.second));
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
			if (is_top_module && port->port_output && !opt_keepoutputs)
				port->port_output = false;
		}
		for (auto &output : new_taint_outputs)
			output->port_output = true;
		module->fixup_ports(); //we have some new taint signals in the module interface
		module->set_bool_attribute(glift_attribute_name, true);
	}

public:
	GliftWorker(RTLIL::Module *_module, bool _is_top_module, bool _opt_create_precise_model, bool _opt_create_imprecise_model, bool _opt_create_instrumented_model, bool _opt_taintconstants, bool _opt_keepoutputs, bool _opt_simplecostmodel, bool _opt_nocostmodel, bool _opt_instrumentmore) {
		module = _module;
		is_top_module = _is_top_module;
		opt_create_precise_model = _opt_create_precise_model;
		opt_create_imprecise_model = _opt_create_imprecise_model;
		opt_create_instrumented_model = _opt_create_instrumented_model;
		opt_taintconstants = _opt_taintconstants;
		opt_keepoutputs = _opt_keepoutputs;
		opt_simplecostmodel = _opt_simplecostmodel;
		opt_nocostmodel = _opt_nocostmodel;
		opt_instrumentmore = _opt_instrumentmore;

		create_glift_logic();
	}
};

struct GliftPass : public Pass {
	GliftPass() : Pass("glift", "create GLIFT models and optimization problems") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    glift <command> [options] [selection]\n");
		log("\n");
		log("Augments the current or specified module with gate-level information flow \n");
		log("tracking (GLIFT) logic using the \"constructive mapping\" approach. Also can set\n");
		log("up QBF-SAT optimization problems in order to optimize GLIFT models or trade off\n");
		log("precision and complexity.\n");
		log("\n");
		log("\n");
		log("Commands:\n");
		log("\n");
		log("  -create-precise-model\n");
		log("    Replaces the current or specified module with one that has corresponding\n");
		log("    \"taint\" inputs, outputs, and internal nets along with precise taint\n");
		log("    tracking logic. For example, precise taint tracking logic for an AND gate\n");
		log("    is:\n");
		log("\n");
		log("      y_t = a & b_t | b & a_t | a_t & b_t\n");
		log("\n");
		log("\n");
		log("  -create-imprecise-model\n");
		log("    Replaces the current or specified module with one that has corresponding\n");
		log("    \"taint\" inputs, outputs, and internal nets along with imprecise \"All OR\"\n");
		log("    taint tracking logic:\n");
		log("\n");
		log("      y_t = a_t | b_t\n");
		log("\n");
		log("\n");
		log("  -create-instrumented-model\n");
		log("    Replaces the current or specified module with one that has corresponding\n");
		log("    \"taint\" inputs, outputs, and internal nets along with 4 varying-precision\n");
		log("    versions of taint tracking logic. Which version of taint tracking logic is\n");
		log("    used for a given gate is determined by a MUX selected by an $anyconst cell.\n");
		log("     By default, unless the `-no-cost-model` option is provided, an additional\n");
		log("    wire named `__glift_weight` with the `keep` and `minimize` attributes is\n");
		log("    added to the module along with pmuxes and adders to calculate a rough\n");
		log("    estimate of the number of logic gates in the GLIFT model given an assignment\n");
		log("    for the $anyconst cells. The four versions of taint tracking logic for an\n");
		log("    AND gate are:\n");
		log("      y_t = a & b_t | b & a_t | a_t & b_t       (like `-create-precise-model`)\n");
		log("      y_t = a_t | a & b_t\n");
		log("      y_t = b_t | b & a_t\n");
		log("      y_t = a_t | b_t                           (like `-create-imprecise-model`)\n");
		log("\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("  -taint-constants\n");
		log("    Constant values in the design are labeled as tainted.\n");
		log("    (default: label constants as un-tainted)\n");
		log("\n");
		log("  -keep-outputs\n");
		log("    Do not remove module outputs. Taint tracking outputs will appear in the\n");
		log("    module ports alongside the orignal outputs.\n");
		log("    (default: original module outputs are removed)\n");
		log("\n");
		log("  -simple-cost-model\n");
		log("    Do not model logic area. Instead model the number of non-zero assignments to\n");
		log("    $anyconsts. Taint tracking logic versions vary in their size, but all\n");
		log("    reduced-precision versions are significantly smaller than the fully-precise\n");
		log("    version. A non-zero $anyconst assignment means that reduced-precision taint\n");
		log("    tracking logic was chosen for some gate. Only applicable in combination with\n");
		log("    `-create-instrumented-model`. (default: use a complex model and give that\n");
		log("     wire the \"keep\" and \"minimize\" attributes)\n");
		log("\n");
		log("  -no-cost-model\n");
		log("    Do not model taint tracking logic area and do not create a `__glift_weight`\n");
		log("    wire. Only applicable in combination with `-create-instrumented-model`.\n");
		log("    (default: model area and give that wire the \"keep\" and \"minimize\"\n");
		log("    attributes)\n");
		log("\n");
		log("  -instrument-more\n");
		log("    Allow choice from more versions of (even simpler) taint tracking logic. A\n");
		log("    total of 8 versions of taint tracking logic will be added per gate,\n");
		log("    including the 4 versions from `-create-instrumented-model` and these\n");
		log("    additional versions:\n");
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

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool opt_create_precise_model = false, opt_create_imprecise_model = false, opt_create_instrumented_model = false;
		bool opt_taintconstants = false, opt_keepoutputs = false, opt_simplecostmodel = false, opt_nocostmodel = false;
		bool opt_instrumentmore = false;
		log_header(design, "Executing GLIFT pass (creating and manipulating GLIFT models).\n");
		std::vector<std::string>::size_type argidx;

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
			if (args[argidx] == "-simple-cost-model") {
				opt_simplecostmodel = true;
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
		if(opt_simplecostmodel && opt_nocostmodel)
			log_cmd_error("Only one of `-simple-cost-model` and `-no-cost-model` may be specified. See help for usage.\n");
		if((opt_simplecostmodel || opt_nocostmodel) && !opt_create_instrumented_model)
			log_cmd_error("Options `-simple-cost-model` and `-no-cost-model` may only be used with `-create-instrumented-model`. See help for usage.\n");
		extra_args(args, argidx, design);

		if (GetSize(design->selected_modules()) == 0)
			log_cmd_error("Can't operate on an empty selection!\n");

		TopoSort<RTLIL::Module*, IdString::compare_ptr_by_name<RTLIL::Module>> topo_modules; //cribbed from passes/techmap/flatten.cc
		auto worklist = design->selected_modules();
		pool<RTLIL::IdString> non_top_modules;
		while (!worklist.empty()) {
			RTLIL::Module *module = *(worklist.begin());
			worklist.erase(worklist.begin());
			topo_modules.node(module);

			for (auto cell : module->selected_cells()) {
				RTLIL::Module *tpl = design->module(cell->type);
				if (tpl != nullptr) {
					if (!topo_modules.has_node(tpl))
						worklist.push_back(tpl);
					topo_modules.edge(tpl, module);
					non_top_modules.insert(cell->type);
				}
			}
		}

		if (!topo_modules.sort())
			log_cmd_error("Cannot handle recursive module instantiations.\n");

		for (auto i = 0; i < GetSize(topo_modules.sorted); ++i) {
			RTLIL::Module *module = topo_modules.sorted[i];
			GliftWorker(module, !non_top_modules[module->name], opt_create_precise_model, opt_create_imprecise_model, opt_create_instrumented_model, opt_taintconstants, opt_keepoutputs, opt_simplecostmodel, opt_nocostmodel, opt_instrumentmore);
		}
	}
} GliftPass;

PRIVATE_NAMESPACE_END
