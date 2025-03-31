/*
 *	yosys -- Yosys Open SYnthesis Suite
 *
 *	Copyright (C) 2017 Robert Ou <rqou@robertou.com>
 *
 *	Permission to use, copy, modify, and/or distribute this software for any
 *	purpose with or without fee is hereby granted, provided that the above
 *	copyright notice and this permission notice appear in all copies.
 *
 *	THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *	WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *	MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *	ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *	WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *	ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *	OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AnnotateUnqcoefPass : public Pass
{
	AnnotateUnqcoefPass() : Pass("annotate_unqcoef", "annotate uniqueness coefficients") { }

	void help() override
	{
		//	 |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("		annotate_unqcoef [options] [selection]\n");
		log("\n");
		log("annotate uniqueness coefficients onto cells with sharing\n");
		log("\n");
		log("This command annotates the uniqueness of each term in reduce-style cells.\n");
		log("These types of cells include $reduce_*, $logic_*, $eq*, $ne*, and $pmux.\n");
		log("cell. The unq coefficient is the number of times a term is shared in similar\n");
		log("cells. For example, if a term is shared in 4 $reduce_and cells, the uniqueness\n");
		log("coefficient is 1/4. This is useful for predicting area/power/etc. from sharing\n");
		log("without explicitly splitting/re-merging cells.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ANNOTATE_UNQCOEF pass (annotate uniqueness coefficients).\n");
		log_push();

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			// Data structures
			SigMap sigmap(module);
			std::map<SigBit, int> reduce_and_sig_count;
			std::map<SigBit, int> reduce_or_sig_count;
			std::map<SigBit, int> reduce_xor_sig_count;
			std::map<std::pair<SigBit, SigBit>, int> eq_sig_count;
			std::map<std::pair<SigBit, SigBit>, int> pmux_sig_count;

			// Count the number of times each bit is used in a $reduce_*/$logic_*/$eq*/$ne*/$pmux cell
			for (auto cell : module->selected_cells())
				if (cell->type.in(ID($reduce_or), ID($logic_not), ID($logic_bool), ID($logic_and), ID($logic_or)))
				{
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
								reduce_or_sig_count[bit]++;
				}
				else if (cell->type.in(ID($reduce_and)))
				{
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
								reduce_and_sig_count[bit]++;
				}
				else if (cell->type.in(ID($reduce_xor), ID($reduce_xnor)))
				{
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
								reduce_xor_sig_count[bit]++;
				}
				else if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
				{
					SigSpec a_sig = sigmap(cell->getPort(ID::A));
					SigSpec b_sig = sigmap(cell->getPort(ID::B));
					for (int i = 0; i < std::min(a_sig.size(), b_sig.size()); i++)
						eq_sig_count[std::make_pair(a_sig.extract(i), b_sig.extract(i))]++;
				}
				else if (cell->type.in(ID($pmux)))
				{
					SigSpec b_sig = sigmap(cell->getPort(ID::B));
					SigSpec s_sig = sigmap(cell->getPort(ID::S));
					int width = cell->getParam(ID::WIDTH).as_int();
					for (int i = 0; i < b_sig.size(); i++)
						pmux_sig_count[std::make_pair(s_sig.extract(i / width), b_sig.extract(i))]++;
				}

			// Calculate the overall uniqueness coefficient for each $reduce_*/$logic_*/$eq*/$ne*/$pmux cell
			for (auto cell : module->selected_cells())
				if (cell->type.in(ID($reduce_or), ID($logic_not), ID($logic_bool), ID($logic_and), ID($logic_or)))
				{
					// Calculate the uniqueness coefficient of each input bit
					float sum_coefs = 0, n_coefs = 0;
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
							{
								auto it = reduce_or_sig_count.find(bit);
								if (it != reduce_or_sig_count.end())
								{
									sum_coefs += 1.0 / it->second;
									n_coefs++;
								}
							}
					
					// Calculate the mean of coefficients
					float coef = sum_coefs / n_coefs;

					// Set string attribute with uniqueness coefficient
					cell->set_string_attribute(ID(UNQCOEF), std::to_string(coef));
				}
				else if (cell->type.in(ID($reduce_and)))
				{
					// Calculate the uniqueness coefficient of each input bit
					float sum_coefs = 0, n_coefs = 0;
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
							{
								auto it = reduce_and_sig_count.find(bit);
								if (it != reduce_and_sig_count.end())
								{
									sum_coefs += 1.0 / it->second;
									n_coefs++;
								}
							}

					// Calculate the mean of coefficients
					float coef = sum_coefs / n_coefs;

					// Set string attribute with uniqueness coefficient
					cell->set_string_attribute(ID(UNQCOEF), std::to_string(coef));
				}
				else if (cell->type.in(ID($reduce_xor), ID($reduce_xnor)))
				{
					// Calculate the uniqueness coefficient of each input bit
					float sum_coefs = 0, n_coefs = 0;
					for (auto &conn : cell->connections())
						if (cell->input(conn.first))
							for (auto bit : sigmap(conn.second))
							{
								auto it = reduce_xor_sig_count.find(bit);
								if (it != reduce_xor_sig_count.end())
								{
									sum_coefs += 1.0 / it->second;
									n_coefs++;
								}
							}

					// Calculate the mean of coefficients
					float coef = sum_coefs / n_coefs;

					// Set string attribute with uniqueness coefficient
					cell->set_string_attribute(ID(UNQCOEF), std::to_string(coef));
				}
				else if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
				{
					SigSpec a_sig = sigmap(cell->getPort(ID::A));
					SigSpec b_sig = sigmap(cell->getPort(ID::B));
					int width = std::min(a_sig.size(), b_sig.size());

					// Calculate the uniqueness coefficient of each input bit
					float sum_coefs = 0, n_coefs = 0;
					for (int i = 0; i < width; i++)
					{
						auto it = eq_sig_count.find(std::make_pair(a_sig.extract(i), b_sig.extract(i)));
						if (it != eq_sig_count.end())
						{
							sum_coefs += 1.0 / it->second;
							n_coefs++;
						}
					}

					// Calculate the mean of coefficients
					float coef = 0.5 * (1 + sum_coefs / n_coefs);

					// Set string attribute with uniqueness coefficient
					cell->set_string_attribute(ID(UNQCOEF), std::to_string(coef));
				}
				else if (cell->type.in(ID($pmux)))
				{
					SigSpec b_sig = sigmap(cell->getPort(ID::B));
					SigSpec s_sig = sigmap(cell->getPort(ID::S));
					int width = cell->getParam(ID::WIDTH).as_int();

					// Calculate the uniqueness coefficient of each input bit
					float sum_coefs = 0, n_coefs = 0;
					for (int i = 0; i < b_sig.size(); i++)
					{
						auto it = pmux_sig_count.find(std::make_pair(s_sig.extract(i / width), b_sig.extract(i)));
						if (it != pmux_sig_count.end())
						{
							sum_coefs += 1.0 / it->second;
							n_coefs++;
						}
					}

					// Calculate the mean of coefficients
					float coef = 0.5 * (1 + sum_coefs / n_coefs);

					// Set string attribute with uniqueness coefficient
					cell->set_string_attribute(ID(UNQCOEF), std::to_string(coef));
				}
		}
	}
} AnnotateUnqcoefPass;

PRIVATE_NAMESPACE_END
