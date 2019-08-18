/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  whitequark <whitequark@whitequark.org>
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
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptLutWorker
{
	dict<IdString, dict<int, IdString>> &dlogic;
	RTLIL::Module *module;
	ModIndex index;
	SigMap sigmap;

	pool<RTLIL::Cell*> luts;
	dict<RTLIL::Cell*, int> luts_arity;
	dict<RTLIL::Cell*, pool<RTLIL::Cell*>> luts_dlogics;
	dict<RTLIL::Cell*, pool<int>> luts_dlogic_inputs;

	int eliminated_count = 0, combined_count = 0;

	bool evaluate_lut(RTLIL::Cell *lut, dict<SigBit, bool> inputs)
	{
		SigSpec lut_input = sigmap(lut->getPort(ID::A));
		int lut_width = lut->getParam(ID(WIDTH)).as_int();
		Const lut_table = lut->getParam(ID(LUT));
		int lut_index = 0;

		for (int i = 0; i < lut_width; i++)
		{
			SigBit input = sigmap(lut_input[i]);
			if (inputs.count(input))
			{
				lut_index |= inputs[input] << i;
			}
			else
			{
				lut_index |= SigSpec(lut_input[i]).as_bool() << i;
			}
		}

		return lut_table.extract(lut_index).as_bool();
	}

	void show_stats_by_arity()
	{
		dict<int, int> arity_counts;
		dict<IdString, int> dlogic_counts;
		int max_arity = 0;

		for (auto lut_arity : luts_arity)
		{
			max_arity = max(max_arity, lut_arity.second);
			arity_counts[lut_arity.second]++;
		}

		for (auto &lut_dlogics : luts_dlogics)
		{
			for (auto &lut_dlogic : lut_dlogics.second)
			{
				dlogic_counts[lut_dlogic->type]++;
			}
		}

		log("Number of LUTs: %8d\n", GetSize(luts));
		for (int arity = 1; arity <= max_arity; arity++)
		{
			if (arity_counts[arity])
				log("  %d-LUT %16d\n", arity, arity_counts[arity]);
		}
		for (auto &dlogic_count : dlogic_counts)
		{
			log("  with %-12s %4d\n", dlogic_count.first.c_str(), dlogic_count.second);
		}
	}

	OptLutWorker(dict<IdString, dict<int, IdString>> &dlogic, RTLIL::Module *module, int limit) :
		dlogic(dlogic), module(module), index(module), sigmap(module)
	{
		log("Discovering LUTs.\n");
		for (auto cell : module->selected_cells())
		{
			if (cell->type == ID($lut))
			{
				if (cell->has_keep_attr())
					continue;
				SigBit lut_output = cell->getPort(ID::Y);
				if (lut_output.wire->get_bool_attribute(ID::keep))
					continue;

				int lut_width = cell->getParam(ID(WIDTH)).as_int();
				SigSpec lut_input = cell->getPort(ID::A);
				int lut_arity = 0;

				log_debug("Found $lut\\WIDTH=%d cell %s.%s.\n", lut_width, log_id(module), log_id(cell));
				luts.insert(cell);

				// First, find all dedicated logic we're connected to. This results in an overapproximation
				// of such connections.
				pool<RTLIL::Cell*> lut_all_dlogics;
				for (int i = 0; i < lut_width; i++)
				{
					SigBit bit = lut_input[i];
					for (auto &port : index.query_ports(bit))
					{
						if (dlogic.count(port.cell->type))
						{
							auto &dlogic_map = dlogic[port.cell->type];
							if (dlogic_map.count(i))
							{
								if (port.port == dlogic_map[i])
								{
									lut_all_dlogics.insert(port.cell);
								}
							}
						}
					}
				}

				// Second, make sure that the connection to dedicated logic is legal. If it is not legal,
				// it means one of the two things:
				//   * The connection is spurious. I.e. this is dedicated logic that will be packed
				//     with some other LUT, and it just happens to be connected to this LUT as well.
				//   * The connection is illegal.
				// In either of these cases, we don't need to concern ourselves with preserving the connection
				// between this LUT and this dedicated logic cell.
				pool<RTLIL::Cell*> lut_legal_dlogics;
				pool<int> lut_dlogic_inputs;
				for (auto lut_dlogic : lut_all_dlogics)
				{
					auto &dlogic_map = dlogic[lut_dlogic->type];
					bool legal = true;
					for (auto &dlogic_conn : dlogic_map)
					{
						if (lut_width <= dlogic_conn.first)
						{
							log_debug("  LUT has illegal connection to %s cell %s.%s.\n", lut_dlogic->type.c_str(), log_id(module), log_id(lut_dlogic));
							log_debug("    LUT input A[%d] not present.\n", dlogic_conn.first);
							legal = false;
							break;
						}
						if (sigmap(lut_input[dlogic_conn.first]) != sigmap(lut_dlogic->getPort(dlogic_conn.second)))
						{
							log_debug("  LUT has illegal connection to %s cell %s.%s.\n", lut_dlogic->type.c_str(), log_id(module), log_id(lut_dlogic));
							log_debug("    LUT input A[%d] (wire %s) not connected to %s port %s (wire %s).\n", dlogic_conn.first, log_signal(lut_input[dlogic_conn.first]), lut_dlogic->type.c_str(), dlogic_conn.second.c_str(), log_signal(lut_dlogic->getPort(dlogic_conn.second)));
							legal = false;
							break;
						}
					}

					if (legal)
					{
						log_debug("  LUT has legal connection to %s cell %s.%s.\n", lut_dlogic->type.c_str(), log_id(module), log_id(lut_dlogic));
						lut_legal_dlogics.insert(lut_dlogic);
						for (auto &dlogic_conn : dlogic_map)
							lut_dlogic_inputs.insert(dlogic_conn.first);
					}
				}

				// Third, determine LUT arity. An n-wide LUT that has k constant inputs and m inputs shared with dedicated
				// logic implements an (n-k-m)-ary function.
				for (int i = 0; i < lut_width; i++)
				{
					SigBit bit = lut_input[i];
					if (bit.wire || lut_dlogic_inputs.count(i))
						lut_arity++;
				}

				log_debug("  Cell implements a %d-LUT.\n", lut_arity);
				luts_arity[cell] = lut_arity;
				luts_dlogics[cell] = lut_legal_dlogics;
				luts_dlogic_inputs[cell] = lut_dlogic_inputs;
			}
		}
		show_stats_by_arity();

		log("\n");
		log("Eliminating LUTs.\n");
		pool<RTLIL::Cell*> worklist = luts;
		while (worklist.size())
		{
			if (limit == 0)
			{
				log("Limit reached.\n");
				break;
			}

			auto lut = worklist.pop();
			SigSpec lut_input = sigmap(lut->getPort(ID::A));
			pool<int> &lut_dlogic_inputs = luts_dlogic_inputs[lut];

			vector<SigBit> lut_inputs;
			for (auto &bit : lut_input)
			{
				if (bit.wire)
					lut_inputs.push_back(sigmap(bit));
			}

			bool const0_match = true;
			bool const1_match = true;
			vector<bool> input_matches;
			for (size_t i = 0; i < lut_inputs.size(); i++)
				input_matches.push_back(true);

			for (int eval = 0; eval < 1 << lut_inputs.size(); eval++)
			{
				dict<SigBit, bool> eval_inputs;
				for (size_t i = 0; i < lut_inputs.size(); i++)
					eval_inputs[lut_inputs[i]] = (eval >> i) & 1;
				bool value = evaluate_lut(lut, eval_inputs);
				if (value != 0)
					const0_match = false;
				if (value != 1)
					const1_match = false;
				for (size_t i = 0; i < lut_inputs.size(); i++)
				{
					if (value != eval_inputs[lut_inputs[i]])
						input_matches[i] = false;
				}
			}

			int input_match = -1;
			for (size_t i = 0; i < lut_inputs.size(); i++)
				if (input_matches[i])
					input_match = i;

			if (const0_match || const1_match || input_match != -1)
			{
				log_debug("Found redundant cell %s.%s.\n", log_id(module), log_id(lut));

				SigBit value;
				if (const0_match)
				{
					log_debug("  Cell evaluates constant 0.\n");
					value = State::S0;
				}
				if (const1_match)
				{
					log_debug("  Cell evaluates constant 1.\n");
					value = State::S1;
				}
				if (input_match != -1) {
					log_debug("  Cell evaluates signal %s.\n", log_signal(lut_inputs[input_match]));
					value = lut_inputs[input_match];
				}

				if (lut_dlogic_inputs.size())
					log_debug("  Not eliminating cell (connected to dedicated logic).\n");
				else
				{
					SigSpec lut_output = lut->getPort(ID::Y);
					for (auto &port : index.query_ports(lut_output))
					{
						if (port.cell != lut && luts.count(port.cell))
							worklist.insert(port.cell);
					}

					module->connect(lut_output, value);
					sigmap.add(lut_output, value);

					module->remove(lut);
					luts.erase(lut);
					luts_arity.erase(lut);
					luts_dlogics.erase(lut);
					luts_dlogic_inputs.erase(lut);

					eliminated_count++;
					if (limit > 0)
						limit--;
				}
			}
		}
		show_stats_by_arity();

		log("\n");
		log("Combining LUTs.\n");
		worklist = luts;
		while (worklist.size())
		{
			if (limit == 0)
			{
				log("Limit reached.\n");
				break;
			}

			auto lutA = worklist.pop();
			SigSpec lutA_input = sigmap(lutA->getPort(ID::A));
			SigSpec lutA_output = sigmap(lutA->getPort(ID::Y)[0]);
			int lutA_width = lutA->getParam(ID(WIDTH)).as_int();
			int lutA_arity = luts_arity[lutA];
			pool<int> &lutA_dlogic_inputs = luts_dlogic_inputs[lutA];

			auto lutA_output_ports = index.query_ports(lutA->getPort(ID::Y));
			if (lutA_output_ports.size() != 2)
				continue;

			for (auto &port : lutA_output_ports)
			{
				if (port.cell == lutA)
					continue;

				if (luts.count(port.cell))
				{
					auto lutB = port.cell;
					SigSpec lutB_input = sigmap(lutB->getPort(ID::A));
					SigSpec lutB_output = sigmap(lutB->getPort(ID::Y)[0]);
					int lutB_width = lutB->getParam(ID(WIDTH)).as_int();
					int lutB_arity = luts_arity[lutB];
					pool<int> &lutB_dlogic_inputs = luts_dlogic_inputs[lutB];

					log_debug("Found %s.%s (cell A) feeding %s.%s (cell B).\n", log_id(module), log_id(lutA), log_id(module), log_id(lutB));

					if (index.query_is_output(lutA->getPort(ID::Y)))
					{
						log_debug("  Not combining LUTs (cascade connection feeds module output).\n");
						continue;
					}

					pool<SigBit> lutA_inputs;
					pool<SigBit> lutB_inputs;
					for (auto &bit : lutA_input)
					{
						if (bit.wire)
							lutA_inputs.insert(sigmap(bit));
					}
					for (auto &bit : lutB_input)
					{
						if (bit.wire)
							lutB_inputs.insert(sigmap(bit));
					}

					pool<SigBit> common_inputs;
					for (auto &bit : lutA_inputs)
					{
						if (lutB_inputs.count(bit))
							common_inputs.insert(bit);
					}

					int lutM_arity = lutA_arity + lutB_arity - 1 - common_inputs.size();
					if (lutA_dlogic_inputs.size())
						log_debug("  Cell A is a %d-LUT with %d dedicated connections. ", lutA_arity, GetSize(lutA_dlogic_inputs));
					else
						log_debug("  Cell A is a %d-LUT. ", lutA_arity);
					if (lutB_dlogic_inputs.size())
						log_debug("Cell B is a %d-LUT with %d dedicated connections.\n", lutB_arity, GetSize(lutB_dlogic_inputs));
					else
						log_debug("Cell B is a %d-LUT.\n", lutB_arity);
					log_debug("  Cells share %d input(s) and can be merged into one %d-LUT.\n", GetSize(common_inputs), lutM_arity);

					const int COMBINE_A = 1, COMBINE_B = 2, COMBINE_EITHER = COMBINE_A | COMBINE_B;
					int combine_mask = 0;
					if (lutM_arity > lutA_width)
						log_debug("  Not combining LUTs into cell A (combined LUT wider than cell A).\n");
					else if (lutB_dlogic_inputs.size() > 0)
						log_debug("  Not combining LUTs into cell A (cell B is connected to dedicated logic).\n");
					else if (lutB->get_bool_attribute(ID(lut_keep)))
						log_debug("  Not combining LUTs into cell A (cell B has attribute \\lut_keep).\n");
					else
						combine_mask |= COMBINE_A;
					if (lutM_arity > lutB_width)
						log_debug("  Not combining LUTs into cell B (combined LUT wider than cell B).\n");
					else if (lutA_dlogic_inputs.size() > 0)
						log_debug("  Not combining LUTs into cell B (cell A is connected to dedicated logic).\n");
					else if (lutA->get_bool_attribute(ID(lut_keep)))
						log_debug("  Not combining LUTs into cell B (cell A has attribute \\lut_keep).\n");
					else
						combine_mask |= COMBINE_B;

					int combine = combine_mask;
					if (combine == COMBINE_EITHER)
					{
						log_debug("  Can combine into either cell.\n");
						if (lutA_arity == 1)
						{
							log_debug("    Cell A is a buffer or inverter, combining into cell B.\n");
							combine = COMBINE_B;
						}
						else if (lutB_arity == 1)
						{
							log_debug("    Cell B is a buffer or inverter, combining into cell A.\n");
							combine = COMBINE_A;
						}
						else
						{
							log_debug("    Arbitrarily combining into cell A.\n");
							combine = COMBINE_A;
						}
					}

					RTLIL::Cell *lutM, *lutR;
					pool<SigBit> lutM_inputs, lutR_inputs;
					pool<int> lutM_dlogic_inputs;
					if (combine == COMBINE_A)
					{
						log_debug("  Combining LUTs into cell A.\n");
						lutM = lutA;
						lutM_inputs = lutA_inputs;
						lutM_dlogic_inputs = lutA_dlogic_inputs;
						lutR = lutB;
						lutR_inputs = lutB_inputs;
					}
					else if (combine == COMBINE_B)
					{
						log_debug("  Combining LUTs into cell B.\n");
						lutM = lutB;
						lutM_inputs = lutB_inputs;
						lutM_dlogic_inputs = lutB_dlogic_inputs;
						lutR = lutA;
						lutR_inputs = lutA_inputs;
					}
					else
					{
						log_debug("  Cannot combine LUTs.\n");
						continue;
					}

					pool<SigBit> lutR_unique;
					for (auto &bit : lutR_inputs)
					{
						if (!common_inputs.count(bit) && bit != lutA_output)
							lutR_unique.insert(bit);
					}

					int lutM_width = lutM->getParam(ID(WIDTH)).as_int();
					SigSpec lutM_input = sigmap(lutM->getPort(ID::A));
					std::vector<SigBit> lutM_new_inputs;
					for (int i = 0; i < lutM_width; i++)
					{
						bool input_unused = false;
						if (sigmap(lutM_input[i]) == lutA_output)
							input_unused = true;
						if (!lutM_input[i].wire && !lutM_dlogic_inputs.count(i))
							input_unused = true;

						if (input_unused && lutR_unique.size())
						{
							SigBit new_input = lutR_unique.pop();
							log_debug("    Connecting input %d as %s.\n", i, log_signal(new_input));
							lutM_new_inputs.push_back(new_input);
						}
						else if (sigmap(lutM_input[i]) == lutA_output)
						{
							log_debug("    Disconnecting cascade input %d.\n", i);
							lutM_new_inputs.push_back(SigBit());
						}
						else
						{
							log_debug("    Leaving input %d as %s.\n", i, log_signal(lutM_input[i]));
							lutM_new_inputs.push_back(lutM_input[i]);
						}
					}
					log_assert(lutR_unique.size() == 0);

					RTLIL::Const lutM_new_table(State::Sx, 1 << lutM_width);
					for (int eval = 0; eval < 1 << lutM_width; eval++)
					{
						dict<SigBit, bool> eval_inputs;
						for (size_t i = 0; i < lutM_new_inputs.size(); i++)
						{
							eval_inputs[lutM_new_inputs[i]] = (eval >> i) & 1;
						}
						eval_inputs[lutA_output] = evaluate_lut(lutA, eval_inputs);
						lutM_new_table[eval] = (RTLIL::State) evaluate_lut(lutB, eval_inputs);
					}

					log_debug("  Cell A truth table: %s.\n", lutA->getParam(ID(LUT)).as_string().c_str());
					log_debug("  Cell B truth table: %s.\n", lutB->getParam(ID(LUT)).as_string().c_str());
					log_debug("  Merged truth table: %s.\n", lutM_new_table.as_string().c_str());

					lutM->setParam(ID(LUT), lutM_new_table);
					lutM->setPort(ID::A, lutM_new_inputs);
					lutM->setPort(ID::Y, lutB_output);

					luts_arity[lutM] = lutM_arity;
					luts.erase(lutR);
					luts_arity.erase(lutR);
					lutR->module->remove(lutR);

					worklist.insert(lutM);
					worklist.erase(lutR);

					combined_count++;
					if (limit > 0)
						limit--;
				}
			}
		}
		show_stats_by_arity();
	}
};

static void split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

struct OptLutPass : public Pass {
	OptLutPass() : Pass("opt_lut", "optimize LUT cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_lut [options] [selection]\n");
		log("\n");
		log("This pass combines cascaded $lut cells with unused inputs.\n");
		log("\n");
		log("    -dlogic <type>:<cell-port>=<LUT-input>[:<cell-port>=<LUT-input>...]\n");
		log("        preserve connections to dedicated logic cell <type> that has ports\n");
		log("        <cell-port> connected to LUT inputs <LUT-input>. this includes\n");
		log("        the case where both LUT and dedicated logic input are connected to\n");
		log("        the same constant.\n");
		log("\n");
		log("    -limit N\n");
		log("        only perform the first N combines, then stop. useful for debugging.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_LUT pass (optimize LUTs).\n");

		dict<IdString, dict<int, IdString>> dlogic;
		int limit = -1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-dlogic" && argidx+1 < args.size())
			{
				std::vector<std::string> tokens;
				split(tokens, args[++argidx], ':');
				if (tokens.size() < 2)
					log_cmd_error("The -dlogic option requires at least one connection.\n");
				IdString type = "\\" + tokens[0];
				for (auto it = tokens.begin() + 1; it != tokens.end(); ++it) {
					std::vector<std::string> conn_tokens;
					split(conn_tokens, *it, '=');
					if (conn_tokens.size() != 2)
						log_cmd_error("Invalid format of -dlogic signal mapping.\n");
					IdString logic_port = "\\" + conn_tokens[0];
					int lut_input = atoi(conn_tokens[1].c_str());
					dlogic[type][lut_input] = logic_port;
				}
				continue;
			}
			if (args[argidx] == "-limit" && argidx + 1 < args.size())
			{
				limit = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int eliminated_count = 0, combined_count = 0;
		for (auto module : design->selected_modules())
		{
			OptLutWorker worker(dlogic, module, limit - eliminated_count - combined_count);
			eliminated_count += worker.eliminated_count;
			combined_count   += worker.combined_count;
		}
		if (eliminated_count)
			design->scratchpad_set_bool("opt.did_something", true);
		if (combined_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("\n");
		log("Eliminated %d LUTs.\n", eliminated_count);
		log("Combined %d LUTs.\n", combined_count);
	}
} OptLutPass;

PRIVATE_NAMESPACE_END
