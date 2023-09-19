/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Andy Fox <andy@rushc.com> https://www.linkedin.com/in/awfox/
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

/*
  Booth Pass
  ----------

  Replace $mul with booth encoded multipliers. Two different
  architectures used for signed/unsigned.

  References:
  Signed architecture: A Low Power Radix-4 Booth Multipliers with Pre-Encoded Mechanism, IEEE Access
  https://ieeexplore.ieee.org/document/9121226

  Unsigned architecture: Gary Bewick, Fast Multiplication algorithms and implementation. Stanford PhD:
  http://i.stanford.edu/pub/cstr/reports/csl/tr/94/617/CSL-TR-94-617.pdf

  How to use:
  Add booth pass  to your yosys script eg:

  read_verilog smultiply5_rtl.v
  opt
  wreduce
  opt
  booth
  alumacc
  maccmap
  opt
  techmap -map ./techmap.v
  dfflibmap -liberty NangateOpenCellLibrary_typical.lib
  abc -liberty NangateOpenCellLibrary_typical.lib
  stat -liberty NangateOpenCellLibrary_typical.lib
  write_verilog -norename booth_final.v

or in generic synthesis call with -booth argument:
synth -top my_design -booth
*/

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BoothPassWorker {

	RTLIL::Module *module;
	SigMap sigmap;
	int booth_counter;

	BoothPassWorker(RTLIL::Module *module) : module(module), sigmap(module) { booth_counter = 0; }

	// Unary gate
	RTLIL::Wire *mk_ugate1(const RTLIL::IdString &red_typ, std::string &name, SigBit ip1, std::string &op_name)
	{
		std::string op_wire_name;
		if (op_name.empty())
			op_wire_name = name + "_o";
		else
			op_wire_name = op_name;
		RTLIL::Wire *ret = module->addWire(new_id(op_wire_name, __LINE__, ""), 1);
		auto g = module->addCell(new_id(name, __LINE__, ""), red_typ);
		g->setPort(ID::A, ip1);
		g->setPort(ID::Y, ret);
		g->setParam(ID::A_SIGNED, false);
		g->setParam(ID::A_WIDTH, 1);
		g->setParam(ID::Y_WIDTH, 1);
		return ret;
	}

	// Binary gate
	RTLIL::Wire *mk_ugate2(const RTLIL::IdString &red_typ, std::string &name, SigBit ip1, SigBit ip2, std::string &op_name)
	{
		auto g = module->addCell(new_id(name, __LINE__, ""), red_typ);
		std::string op_wire_name;
		if (op_name.empty())
			op_wire_name = name + "_o";
		else
			op_wire_name = op_name;

		auto ret = module->addWire(new_id(op_wire_name, __LINE__, ""), 1);

		g->setPort(ID::A, ip1);
		g->setPort(ID::B, ip2);
		g->setPort(ID::Y, ret);
		g->setParam(ID::A_SIGNED, false);
		g->setParam(ID::B_SIGNED, false);
		g->setParam(ID::A_WIDTH, 1);
		g->setParam(ID::B_WIDTH, 1);
		g->setParam(ID::Y_WIDTH, 1);
		return ret;
	}

	// Booth unsigned decoder lsb
	void BuildBur4d_lsb(std::string &name, SigBit lsb_i, SigBit one_i, SigBit s_i, SigBit &ppij_o,
			    std::string op_wire_name)
	{
		std::string empty;
		auto and_op = mk_ugate2(ID($and), name, lsb_i, one_i, empty);
		ppij_o = mk_ugate2(ID($xor), name, and_op, s_i, op_wire_name);
	}

	// Booth unsigned radix4 decoder
	void BuildBur4d_n(std::string &name, SigBit yn_i, SigBit ynm1_i, SigBit one_i, SigBit two_i, SigBit s_i,
			  SigBit &ppij_o)
	{
		// ppij = ((yn & one)   | (ynm1 & two)) ^ s;
		std::string empty;
		auto an1 = mk_ugate2(ID($and), name, yn_i, one_i, empty);
		auto an2 = mk_ugate2(ID($and), name, ynm1_i, two_i, empty);
		auto or1 = mk_ugate2(ID($or), name, an1, an2, empty);
		ppij_o = mk_ugate2(ID($xor), name, s_i, or1, empty);
	}

	// Booth unsigned radix4 decoder
	void BuildBur4d_msb(std::string &name, SigBit msb_i, SigBit two_i, SigBit s_i, SigBit &ppij_o)
	{
		// ppij = (msb & two)  ^ s;
		std::string empty;
		auto an1 = mk_ugate2(ID($and), name, msb_i, two_i, empty);
		ppij_o = mk_ugate2(ID($xor), name, s_i, an1, empty);
	}

	// half adder, used in CPA
	void BuildHa(std::string &name, SigBit a_i, SigBit b_i, SigBit &s_o, SigBit &c_o)
	{
		std::string empty;
		s_o = mk_ugate2(ID($xor), name, a_i, b_i, empty);
		c_o = mk_ugate2(ID($and), name, a_i, b_i, empty);
	}

	// Booth unsigned radix 4 encoder
	void BuildBur4e(std::string &name, SigBit y0_i, SigBit y1_i, SigBit y2_i,
			SigBit &one_o, SigBit &two_o, SigBit &s_o, SigBit &sb_o)
	{

		std::string empty;
		one_o = mk_ugate2(ID($xor), name, y0_i, y1_i, empty);
		s_o = y2_i;
		sb_o = mk_ugate1(ID($not), name, y2_i, empty);
		auto inv_y1_xor_y2 = mk_ugate1(ID($not), name, mk_ugate2(ID($xor), name, y1_i, y2_i, empty), empty);
		two_o = mk_ugate1(ID($not), name, mk_ugate2(ID($or), name, inv_y1_xor_y2, one_o, empty), empty);
	}

	void BuildBr4e(std::string &name, SigBit y2_m1_i,
		       SigBit y2_i, // y2i
		       SigBit y2_p1_i,
		       SigBit &negi_o, SigBit &twoi_n_o, SigBit &onei_n_o, SigBit &cori_o)
	{

		std::string empty;
		auto y2_p1_n = mk_ugate1(ID($not), name, y2_p1_i, empty);
		auto y2_n = mk_ugate1(ID($not), name, y2_i, empty);
		auto y2_m1_n = mk_ugate1(ID($not), name, y2_m1_i, empty);

		// negi_o = y2_p1_i
		negi_o = mk_ugate1(ID($pos), name, y2_p1_i, empty);
		// twoi_n = ~(
		//    (y2_p1_n & y2_i & y2_m1_i) |
		//    (y2_p1 & y2_n & y2_m1_n)
		// )
		auto and3_1 = mk_ugate2(ID($and), name, y2_p1_n, mk_ugate2(ID($and), name, y2_i, y2_m1_i, empty), empty);
		auto and3_2 = mk_ugate2(ID($and), name, y2_p1_i, mk_ugate2(ID($and), name, y2_n, y2_m1_n, empty), empty);

		twoi_n_o = mk_ugate1(ID($not), name, mk_ugate2(ID($or), name, and3_1, and3_2, empty), empty);
		// onei_n = ~(y2_m1_i ^ y2_i);
		onei_n_o = mk_ugate1(ID($not), name, mk_ugate2(ID($xor), name, y2_m1_i, y2_i, empty), empty);
		// cori = (y2_m1_n | y2_n) & y2_p1_i;
		cori_o = mk_ugate2(ID($and), name, y2_p1_i, mk_ugate2(ID($or), name, y2_m1_n, y2_n, empty), empty);
	}

	//
	// signed booth radix 4 decoder
	//
	void BuildBr4d(std::string &name, SigBit nxj_m1_i, SigBit twoi_n_i, SigBit xj_i, SigBit negi_i, SigBit onei_n_i,
		       SigBit &ppij_o, SigBit &nxj_o)
	{

		std::string empty;
		// nxj_in = xnor(xj,negi)
		// nxj_o = xnj_in,
		// ppij = ~( (nxj_m1_i | twoi_n_i) & (nxj_int | onei_n_i));
		nxj_o = mk_ugate2(ID($xnor), name, xj_i, negi_i, empty);
		SigBit or1 = mk_ugate2(ID($or), name, nxj_m1_i, twoi_n_i, empty);
		SigBit or2 = mk_ugate2(ID($or), name, nxj_o, onei_n_i, empty);
		ppij_o = mk_ugate1(ID($not), name, mk_ugate2(ID($and), name, or1, or2, empty), empty);
	}

	/*
	  In signed case 1st two bits best realised
	  using non-booth encoded logic. We can save a booth
	  encoder for the first couple of bits.
	*/
	void BuildBoothQ1(std::string &name, SigBit negi_i, SigBit cori_i, SigBit x0_i, SigBit x1_i, SigBit y0_i,
			  SigBit y1_i,
			  SigBit &nxj_o, SigBit &cor_o, SigBit &pp0_o, SigBit &pp1_o)
	{
		/*
		  assign NXJO = ~(X1 ^ NEGI);
		  assign PP0 = (X0 & Y0);
		  //and terms for multiply
		  wire pp1_1_int = X1 & Y0;
		  wire pp1_2_int = X0 & Y1;
		  //sum generation for pp[1]
		  assign PP1 = pp1_1_int ^ pp1_2_int;
		  //correction propagation
		  assign CORO = (~PP1 & ~PP0)? CORI : 1'b0;
		*/
		std::string empty;
		nxj_o = mk_ugate2(ID($xnor), name, x1_i, negi_i, empty);
		pp0_o = mk_ugate2(ID($and), name, x0_i, y0_i, empty);
		SigBit pp1_1_int = mk_ugate2(ID($and), name, x1_i, y0_i, empty);
		SigBit pp1_2_int = mk_ugate2(ID($and), name, x0_i, y1_i, empty);
		pp1_o = mk_ugate2(ID($xor), name, pp1_1_int, pp1_2_int, empty);

		SigBit pp1_nor_pp0 = mk_ugate1(ID($not), name, mk_ugate2(ID($or), name, pp1_o, pp0_o, empty), empty);
		cor_o = mk_ugate2(ID($and), name, pp1_nor_pp0, cori_i, empty);
	}

	void run()
	{
		for (auto cell : module->selected_cells()) {
			if (cell->type.in(ID($mul))) {
				RTLIL::SigSpec A = sigmap(cell->getPort(ID::A));
				RTLIL::SigSpec B = sigmap(cell->getPort(ID::B));
				RTLIL::SigSpec Y = sigmap(cell->getPort(ID::Y));
				if (GetSize(A) >= 4 && GetSize(B) >= 4 && GetSize(Y) >= 8 &&
				    ((cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool()) ||
				     (!cell->getParam(ID::A_SIGNED).as_bool() && !cell->getParam(ID::B_SIGNED).as_bool()))) {
					bool is_signed = false;
					if (cell->getParam(ID::A_SIGNED).as_bool()) {
						log("    By passing macc inferencing for signed multiplier -- generating booth\n");
						is_signed = true;
					} else
						log("    By passing macc inferencing for unsigned multiplier -- generating booth\n");

					int x_sz = GetSize(A);
					int y_sz = GetSize(B);
					int z_sz = GetSize(Y);

					// To simplify the generator size the arguments
					// to be the same. Then allow logic synthesis to
					// clean things up. Size to biggest

					int x_sz_revised = x_sz;
					int y_sz_revised = y_sz;

					if (x_sz != y_sz) {
						if (x_sz < y_sz) {
							if (y_sz % 2 != 0) {
								x_sz_revised = y_sz + 1;
								y_sz_revised = y_sz + 1;
							} else
								x_sz_revised = y_sz;

						} else {
							if (x_sz % 2 != 0) {
								y_sz_revised = x_sz + 1;
								x_sz_revised = x_sz + 1;
							} else
								y_sz_revised = x_sz;
						}
					} else {
						if (x_sz % 2 != 0) {
							y_sz_revised = y_sz + 1;
							x_sz_revised = x_sz + 1;
						}
					}

					log_assert((x_sz_revised == y_sz_revised) && (x_sz_revised % 2 == 0) && (y_sz_revised % 2 == 0));

					Wire *expanded_A = module->addWire(NEW_ID, x_sz_revised);
					Wire *expanded_B = module->addWire(NEW_ID, y_sz_revised);

					std::string buf_name = "expand_a_buf_";
					auto buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
					buf->setParam(ID::A_WIDTH, x_sz);
					buf->setParam(ID::Y_WIDTH, x_sz_revised);
					buf->setPort(ID::A, SigSpec(A));
					buf->setParam(ID::A_SIGNED, is_signed ? true : false);
					buf->setPort(ID::Y, SigSpec(expanded_A));

					buf_name = "expand_b_buf_";
					buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
					buf->setPort(ID::A, SigSpec(B));
					buf->setParam(ID::A_WIDTH, y_sz);
					buf->setParam(ID::Y_WIDTH, y_sz_revised);
					buf->setParam(ID::A_SIGNED, is_signed ? true : false);
					buf->setPort(ID::Y, SigSpec(expanded_B));

					// Make sure output domain is big enough to take
					// all combinations.
					// Later logic synthesis will kill unused
					// portions of the output domain.

					unsigned required_op_size = x_sz_revised + y_sz_revised;
					Wire *expanded_Y = module->addWire(NEW_ID, required_op_size);
					// now connect the expanded_Y with a tap to fill out sig Spec Y
					buf_name = "reducer_buf_";
					buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
					buf->setPort(ID::A, expanded_Y);
					buf->setParam(ID::A_WIDTH, required_op_size);
					buf->setParam(ID::Y_WIDTH, z_sz); // The real user width
					buf->setParam(ID::A_SIGNED, is_signed ? true : false);
					// wire in output Y
					buf->setPort(ID::Y, SigSpec(Y));

					if (is_signed == false) /* unsigned multiplier */
						CreateBoothUMult(module,
								 expanded_A, // multiplicand
								 expanded_B, // multiplier(scanned)
								 expanded_Y  // result
						);
					else /*signed multiplier */
						CreateBoothSMult(module,
								 expanded_A, // multiplicand
								 expanded_B, // multiplier(scanned)
								 expanded_Y  // result (sized)
						);
					module->remove(cell);
					booth_counter++;
					continue;
				}
			}
		}
	}

	/*
	  Build Unsigned Multiplier.
	  -------------------------
	  Create a booth unsigned multiplier.
	  Uses a generic booth multiplier with
	  extra row of decoders and extended multiplier
	*/

	void CreateBoothUMult(RTLIL::Module *module,
			      SigSpec X, // multiplicand
			      SigSpec Y, // multiplier
			      SigSpec Z)
	{ // result
		int x_sz = X.size(), z_sz = Z.size();

		SigSpec one_int, two_int, s_int, sb_int;
		int encoder_count = 0;

		BuildBoothUMultEncoders(Y, one_int, two_int, s_int, sb_int, module, encoder_count);

		// Build the decoder rows
		// format of each Partial product to be passed to CSA
		// tree builder:
		//
		// Bits to be added
		// Shift
		// Sign bit to be added
		//
		std::vector<std::tuple<SigSpec, int, SigBit>> ppij_int;

		// Row 0: special case 1. Format S/.S.S.C.Data
		SigSpec ppij_row_0;
		BuildBoothUMultDecoderRow0(module, X, s_int, sb_int, one_int, two_int, ppij_row_0);

		// data, shift, sign
		ppij_int.push_back(std::make_tuple(ppij_row_0, 0, s_int[0]));

		for (int i = 1; i < encoder_count - 2; i++) {
			// format 1,S.Data.shift = encoder_ix*2,sign = sb_int[i]
			SigSpec ppij_row_n;

			BuildBoothUMultDecoderRowN(module,
						   X, // multiplicand
						   one_int[i], two_int[i], s_int[i], sb_int[i], ppij_row_n, i,
						   false, // include sign
						   false  // include constant
			);
			// data, shift, sign
			ppij_int.push_back(std::make_tuple(ppij_row_n, i * 2, s_int[i]));
		}

		// Build second to last row
		// format S/,Data + sign bit
		SigSpec ppij_row_em1;
		BuildBoothUMultDecoderRowN(module, X, one_int[encoder_count - 2], two_int[encoder_count - 2], s_int[encoder_count - 2],
					   sb_int[encoder_count - 2], ppij_row_em1, encoder_count - 2,
					   false, // include sign
					   true	  // no constant
		);
		ppij_int.push_back(std::make_tuple(ppij_row_em1, (encoder_count - 2) * 2, s_int[encoder_count - 2]));
		// Build last row
		// format Data + sign bit
		SigSpec ppij_row_e;
		BuildBoothUMultDecoderRowN(module, X, one_int[encoder_count - 1], two_int[encoder_count - 1], s_int[encoder_count - 1],
					   sb_int[encoder_count - 1], ppij_row_e, encoder_count - 1,
					   true, // no sign
					   true	 // no constant
		);
		ppij_int.push_back(std::make_tuple(ppij_row_e, (encoder_count - 1) * 2, s_int[encoder_count - 1]));

		//  Debug dump out partial products
		//  DebugDumpPP(ppij_int);

		// Summation of Partial Products (Wallace Tree)
		std::vector<SigSpec> aligned_pp;
		aligned_pp.resize(encoder_count + 1); // make an entirely redundant row
		// just for sign bit in lsb. (We then filter this out).

		// resize all to be same size as z
		for (int i = 0; i < encoder_count + 1; i++)
			aligned_pp[i].extend_u0(z_sz);

		AlignPP(x_sz, z_sz, ppij_int, aligned_pp);

		// Debug: dump out aligned partial products.
		// Later on yosys will clean up unused constants
		//  DebugDumpAlignPP(aligned_pp);

		SigSpec s_vec;
		SigSpec c_vec;
		std::vector<std::vector<RTLIL::Cell *>> debug_csa_trees;

		debug_csa_trees.resize(z_sz);

		BuildCSATree(module, aligned_pp, s_vec, c_vec, debug_csa_trees);

		// Debug code: Dump out the csa trees
		// DumpCSATrees(debug_csa_trees);
		// Build the CPA to do the final accumulation.
		BuildCPA(module, s_vec, c_vec, Z);
	}

	/*
	  Build Row 0 of decoders
	*/

	void BuildBoothUMultDecoderRow0(RTLIL::Module *module,
					SigSpec X, // multiplicand
					SigSpec s_int, SigSpec sb_int, SigSpec one_int,
					SigSpec two_int, SigSpec &ppij_vec)
	{
		(void)module;
		int x_sz = GetSize(X);

		// lsb
		std::string dec_name = "row0_lsb_dec";

		SigBit ppij;
		std::string ppij_name = "ppij_0_0";
		BuildBur4d_lsb(dec_name, X[0], one_int[0], s_int[0], ppij, ppij_name);
		ppij_vec.append(ppij);

		// 1..xsize -1
		for (int i = 1; i < x_sz; i++) {
			dec_name = "row0_dec_" + std::to_string(i);
			SigBit ppij;
			BuildBur4d_n(dec_name, X[i], X[i - 1], one_int[0], two_int[0],
				     s_int[0], ppij);
			ppij_vec.append(ppij);
		}

		// The redundant bit. Duplicate decoding of last bit.
		dec_name = "row0_dec_msb";
		BuildBur4d_msb(dec_name, X[x_sz - 1], two_int[0], s_int[0], ppij);
		ppij_vec.append(ppij);

		// append the sign bits
		ppij_vec.append(s_int[0]);
		ppij_vec.append(s_int[0]);
		ppij_vec.append(sb_int[0]);
	}

	// Build a generic row of decoders.

	void BuildBoothUMultDecoderRowN(RTLIL::Module *module,
					SigSpec X, // multiplicand
					SigSpec one_int, SigSpec two_int, SigSpec s_int, SigSpec sb_int,
					SigSpec &ppij_vec, int row_ix, bool no_sign, bool no_constant)
	{
		(void)module;
		int x_sz = GetSize(X);

		// lsb
		std::string ppij_name = "ppij_" + std::to_string(row_ix) + "_0";
		SigBit ppij;
		std::string empty;
		std::string dec_name = "row" + std::to_string(row_ix) + "_lsb_dec";
		BuildBur4d_lsb(dec_name, X[0], one_int, s_int, ppij, empty);

		ppij_vec.append(ppij);

		// core bits
		for (int i = 1; i < x_sz; i++) {

			dec_name = "row_" + std::to_string(row_ix) + "_dec_" + std::to_string(i);
			BuildBur4d_n(dec_name, X[i], X[i - 1],
				     one_int, two_int, s_int, ppij);
			ppij_vec.append(ppij);
		}

		// redundant bit

		dec_name = "row_dec_red";
		BuildBur4d_msb(dec_name, X[x_sz - 1], two_int, s_int, ppij);
		ppij_vec.append(ppij);

		// sign bit
		if (no_sign == false) // if no sign is false then make a sign bit
			ppij_vec.append(sb_int);

		// constant bit
		if (no_constant == false) { // if non constant is false make a constant bit
			ppij_vec.append(State::S1);
		}
	}

	void DebugDumpAlignPP(std::vector<std::vector<RTLIL::Wire *>> &aligned_pp)
	{
		printf("Aligned & Padded Partial products\n");
		int pp_ix = 0;
		for (auto pp_row : aligned_pp) {
			printf("PP_%d \t", pp_ix);
			for (unsigned i = 0; i < pp_row.size(); i++)
				printf("[%d] %s ", i, pp_row[i] == nullptr ? " 0 " : pp_row[i]->name.c_str());
			printf("\n");
			pp_ix++;
		}
	}

	// Debug routines to inspect intermediate results
	void DebugDumpPP(std::vector<std::tuple<std::vector<RTLIL::Wire *>, int, RTLIL::Wire *>> &ppij_int)
	{
		printf("Debug dump of partial products\n");
		int pp_ix = 0;

		for (auto pp : ppij_int) {
			int shift = get<1>(pp);
			RTLIL::Wire *sign_bit = get<2>(pp);

			printf("PP %d\n", pp_ix);
			printf("\tShift %d\n", shift);
			printf("\tData (0 lsb)\n\t");
			int ix = 0;

			for (auto pp_wire : get<0>(pp)) {
				RTLIL::IdString wire_name = pp_wire->name;

				printf(" [%d]:%s ", ix, wire_name.c_str());
				ix++;
			}
			printf("\n");
			printf("\tSign bit to add in: %s\n", sign_bit->name.c_str());

			pp_ix++;
		}
	}

	void DumpCSATrees(std::vector<std::vector<RTLIL::Cell *>> &debug_csa_trees)
	{
		int i = 0;
		for (auto csa_tree : debug_csa_trees) {
			printf("CSA Tree column %d\n", i);
			int ix = 0;
			for (auto csa_elem : csa_tree) {
				printf("\tCell %d  %s type %s\n", ix, csa_elem->name.c_str(), csa_elem->type.c_str());
				if (csa_elem->getPort(ID::A) == State::S0)
					printf("\tA set to constant 0\n");
				else if (csa_elem->getPort(ID::A) == State::S1)
					printf("\tA set to constant 1\n");
				else
					printf("\tA driven by %s\n", csa_elem->getPort(ID::A).as_wire()->name.c_str());

				if (csa_elem->getPort(ID::B) == State::S0)
					printf("\tB set to constant 0\n");
				else if (csa_elem->getPort(ID::B) == State::S1)
					printf("\tB set to constant 1\n");
				else
					printf("\tB driven by %s\n", csa_elem->getPort(ID::B).as_wire()->name.c_str());

				if (csa_elem->getPort(ID::C) == State::S0)
					printf("\tC set to constant 0\n");
				else if (csa_elem->getPort(ID::C) == State::S1)
					printf("\tC set to constant 1\n");
				else
					printf("\tC driven by %s\n", csa_elem->getPort(ID::C).as_wire()->name.c_str());

				printf("Carry out: %s\n", csa_elem->getPort(ID::X).as_wire()->name.c_str());
				printf("Sum out: %s\n", csa_elem->getPort(ID::Y).as_wire()->name.c_str());

				ix++;
			}
			i++;
		}
	}

	void BuildCSATree(RTLIL::Module *module, std::vector<SigSpec> &bits_to_reduce, SigSpec &s_vec,
			  SigSpec &c_vec, std::vector<std::vector<RTLIL::Cell *>> &debug_csa_trees)
	{

		if (!(bits_to_reduce.size() > 0))
			return;

		int column_size = bits_to_reduce[0].size();
		int row_size = bits_to_reduce.size();
		SigSpec carry_bits_to_add_to_next_column;

		for (int column_ix = 0; column_ix < column_size; column_ix++) {

			// get the bits in this column.
			SigSpec column_bits;
			for (int row_ix = 0; row_ix < row_size; row_ix++) {
				if (bits_to_reduce[row_ix][column_ix].wire)
					column_bits.append(bits_to_reduce[row_ix][column_ix]);
			}
			for (auto c : carry_bits_to_add_to_next_column) {
#ifdef DEBUG_CSA
				printf("\t Propagating column bit %s to column %d from column %d\n", c->name.c_str(), column_ix, column_ix - 1);
#endif
				column_bits.append(c);
			}

			carry_bits_to_add_to_next_column = {};

#ifdef DEBUG_CSA
			printf("Column %d Reducing %d bits\n", column_ix, column_bits.size());
			for (auto b : column_bits) {
				printf("\t %s\n", b->name.c_str());
			}
			printf("\n");
#endif

			SigBit s, c;
#ifdef DEBUG_CSA
			int csa_count_before = debug_csa_trees[column_ix].size();
#endif

			ReduceBits(module, column_ix, column_bits, s, c, carry_bits_to_add_to_next_column, debug_csa_trees);

			s_vec.append(s);
			c_vec.append(c);

#ifdef DEBUG_CSA
			int csa_count_after = debug_csa_trees[column_ix].size();

			printf("Column %d Created %d csa tree elements\n", column_ix, csa_count_after - csa_count_before);
#endif
		}
	}

	/*
	  Alignment:
	  ---------

	  Concept traverse from last row.
	  Pad row by shift
	  Add sign bit from prior row to 2 bits right of end of data.

	  Example

	  SCDDDDDDD- +S
	  DDDDDDDD_

	  ==>
	  SCDDDDDDD-
	  DDDDDDDD_S <-- prior rows sign bit added 2 columns to right on next row.

	  Pad out rows with zeros and left the opt pass clean them up.

	*/
	void AlignPP(int x_sz, int z_sz, std::vector<std::tuple<SigSpec, int, SigBit>> &ppij_int,
		     std::vector<SigSpec> &aligned_pp)
	{
		unsigned aligned_pp_ix = aligned_pp.size() - 1;

		// default is zero for everything (so don't have to think to hard
		// about padding).

		for (unsigned i = 0; i < aligned_pp.size(); i++) {
			for (int j = 0; j < z_sz; j++) {
				aligned_pp[i][j] = State::S0;
			}
		}

		// for very last row we just have the sign bit
		// Note that the aligned_pp is one row bigger
		// than the ppij_int. We put the sign bit
		// in first column of the last partial product
		// which is at index corresponding to size of multiplicand
		{
			SigBit prior_row_sign = get<2>(ppij_int[aligned_pp_ix - 1]);
			//if (prior_row_sign) {
				log_assert(aligned_pp_ix < aligned_pp.size());
				log_assert(x_sz - 1 < (int)(aligned_pp[aligned_pp_ix].size()));
				aligned_pp[aligned_pp_ix][x_sz - 1] = prior_row_sign;
			//}
		}

		for (int row_ix = aligned_pp_ix - 1; row_ix >= 0; row_ix--) {
			int shift_amount = get<1>(ppij_int[row_ix]);

			// copy in data
			int copy_ix = shift_amount;
			for (auto w : get<0>(ppij_int[row_ix])) {
				if (copy_ix < aligned_pp[row_ix].size()) {
					aligned_pp[row_ix][copy_ix] = w;
				}
				copy_ix++;
			}

			// copy in the sign bit from the prior row
			if (row_ix > 0) {
				// if sign bit on prior row, copy in
				// the destination of the sign bit is the (row_ix -1)*2
				// eg destination for sign bit for row 0 is 0.
				// eg destination for sign bit for row 1 is 1
				SigBit prior_row_sign = get<2>(ppij_int[row_ix - 1]);
				copy_ix = (row_ix - 1) * 2;
				aligned_pp[row_ix][copy_ix] = prior_row_sign;
			}
		}
	}

	/*
	  Build a Carry Propagate Adder
	  -----------------------------
	  First build the sum and carry vectors to be added.
	*/
	void BuildCPA(RTLIL::Module *module, SigSpec s_vec, SigSpec c_vec, SigSpec result)
	{
		static int cpa_id;
		cpa_id++;

		log_assert(c_vec.size() == s_vec.size());
		// TODO: doesn't pass
		//log_assert(result.size() == s_vec.size() + 2);

		SigBit carry;
		for (int n = 0; n < s_vec.size(); n++) {
			std::string carry_name;

			// Base Case: Bit 0 is sum 0
			if (n == 0) {
				module->addBufGate(NEW_ID_SUFFIX(stringf("base_buf_%d_%d", cpa_id, n)), s_vec[0], result[0]);

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IP 0 %s \n", n, buf->name.c_str(), s_vec[0]->name.c_str());
#endif
			}

			//
			// Base Case
			// c,s = ha(s_vec[1],c_vec[0])
			//
			else if (n == 1) {
				std::string ha_name = "cpa_" + std::to_string(cpa_id) + "_ha_" + std::to_string(n);
				SigBit ha_op;
				BuildHa(ha_name, s_vec[n], c_vec[n - 1], ha_op, carry);
				module->connect(result[n], ha_op);

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IPs [%s] [%s] \n", n, ha_cell->name.c_str(), s_vec[n]->name.c_str(),
				       c_vec[n - 1]->name.c_str());
#endif

			}
			// End Case
			else if (n == s_vec.size() - 1) {
				// Make the carry results.. Two extra bits after fa.
				std::string fa_name = "cpa_" + std::to_string(cpa_id) + "_fa_" + std::to_string(n);

				auto fa_cell = module->addCell(new_id(fa_name, __LINE__, ""), ID($fa));
				fa_cell->setParam(ID::WIDTH, 1);
				carry_name = "cpa_" + std::to_string(cpa_id) + "carry_" + std::to_string(n);
				fa_cell->setPort(ID::A, s_vec[n]);
				fa_cell->setPort(ID::B, c_vec[n - 1]);
				fa_cell->setPort(ID::C, carry);
				// wire in result and carry out
				fa_cell->setPort(ID::Y, result[n]);

				// make a new carry bit for carry out...
				carry = module->addWire(new_id(carry_name, __LINE__, ""), 1);
				fa_cell->setPort(ID::X, carry);

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IPs [%s] [%s] [%s]\n", n, fa_cell->name.c_str(), s_vec[n]->name.c_str(),
				       c_vec[n - 1]->name.c_str(), carry->name.c_str());
#endif
				if (n + 1 < GetSize(result)) {
					// Now make a half adder: c_vec[n] = carry
					std::string ha_name = "cpa_" + std::to_string(cpa_id) + "_ha_" + std::to_string(n);
					SigBit ha_sum;
					SigBit ha_carry;
					BuildHa(ha_name, c_vec[n], carry, ha_sum, ha_carry);
					if (n + 1 < GetSize(result))
						module->connect(result[n + 1], ha_sum);
					if (n + 2 < GetSize(result))
						module->connect(result[n + 2], ha_carry);
				}
			}
			// Step case
			else {
				std::string fa_name = "cpa_" + std::to_string(cpa_id) + "_fa_" + std::to_string(n);
				auto fa_cell = module->addCell(new_id(fa_name, __LINE__, ""), ID($fa));
				fa_cell->setParam(ID::WIDTH, 1);

				carry_name = "cpa_" + std::to_string(cpa_id) + "carry_" + std::to_string(n);
				fa_cell->setPort(ID::A, s_vec[n]);
				fa_cell->setPort(ID::B, c_vec[n - 1]);
				fa_cell->setPort(ID::C, carry);
				// wire in result and carry out
				fa_cell->setPort(ID::Y, result[n]);
				// make a new carry bit for carry out...
				carry = module->addWire(new_id(carry_name, __LINE__, ""), 1);
				fa_cell->setPort(ID::X, carry);

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IPs [%s] [%s] [%s]\n", n, fa_cell->name.c_str(), s_vec[n]->name.c_str(),
				       c_vec[n - 1]->name.c_str(), carry->name.c_str());
#endif
			}
		}
	}

	// Sum the bits in the current column
	// Pass the carry bits from each csa to the next
	// column for summation.

	void ReduceBits(RTLIL::Module *module, int column_ix, SigSpec column_bits, SigBit &s_result, SigBit &c_result,
			SigSpec &carry_bits_to_sum, std::vector<std::vector<RTLIL::Cell *>> &debug_csa_trees)
	{

		int csa_ix = 0;
		int column_size = column_bits.size();
		static int unique_id = 0;

		unique_id++;

		if (column_size > 0) {
			int var_ix = 0;
			SigSpec first_csa_ips;
			// get the first 3 inputs, if possible
			for (var_ix = 0; var_ix < column_bits.size() && first_csa_ips.size() != 3; var_ix++) {
				if (column_bits[var_ix].is_wire())
					first_csa_ips.append(column_bits[var_ix]);
			}

			if (first_csa_ips.size() > 0) {
				// build the first csa
				std::string csa_name =
				  "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix) + "_" + std::to_string(unique_id) + "_";
				auto csa = module->addCell(NEW_ID,
							   // new_id(csa_name,
							   //					    __LINE__,
							   //	    ""),
							   ID($fa));
				csa->setParam(ID::WIDTH, 1);
				debug_csa_trees[column_ix].push_back(csa);
				csa_ix++;

				csa->setPort(ID::A, first_csa_ips[0]);

				if (first_csa_ips.size() > 1)
					csa->setPort(ID::B, first_csa_ips[1]);
				else
					csa->setPort(ID::B, State::S0);

				if (first_csa_ips.size() > 2)
					csa->setPort(ID::C, first_csa_ips[2]);
				else
					csa->setPort(ID::C, State::S0);

				std::string sum_wire_name = "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix) + "_s";
				auto s_wire = module->addWire(new_id(sum_wire_name, __LINE__, ""), 1);
				csa->setPort(ID::Y, s_wire);
				s_result = s_wire;
				std::string carry_wire_name = "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix) + "_c";
				auto c_wire = module->addWire(new_id(carry_wire_name, __LINE__, ""), 1);
				csa->setPort(ID::X, c_wire);
				c_result = c_wire;

				if (var_ix <= column_bits.size() - 1)
					carry_bits_to_sum.append(c_wire);

				// Now build the rest of the tree if we can
				while (var_ix <= column_bits.size() - 1) {
					SigSpec csa_ips;
					// get the next two variables to sum
					for (; var_ix <= column_bits.size() - 1 && csa_ips.size() < 2;) {
						// skip any empty bits
						if (column_bits[var_ix].is_wire())
							csa_ips.append(column_bits[var_ix]);
						var_ix++;
					}

					if (csa_ips.size() > 0) {
						csa_name = "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix);
						auto csa = module->addCell(new_id(csa_name, __LINE__, ""), ID($fa));
						csa->setParam(ID::WIDTH, 1);
						debug_csa_trees[column_ix].push_back(csa);

						csa_ix++;
						// prior level
						csa->setPort(ID::A, s_wire);
						csa->setPort(ID::B, csa_ips[0]);
						if (csa_ips.size() > 1)
							csa->setPort(ID::C, csa_ips[1]);
						else
							csa->setPort(ID::C, State::S0);

						carry_wire_name = "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix) + "_c";
						c_wire = module->addWire(new_id(carry_wire_name, __LINE__, ""), 1);

						if (var_ix <= column_bits.size() - 1)
							carry_bits_to_sum.append(c_wire);

						sum_wire_name = "csa_" + std::to_string(column_ix) + "_" + std::to_string(csa_ix) + "_s";
						s_wire = module->addWire(new_id(sum_wire_name, __LINE__, ""), 1);

						csa->setPort(ID::X, c_wire);
						csa->setPort(ID::Y, s_wire);

						s_result = s_wire;
						c_result = c_wire;
					}
				}
			}
		}
	}

	void BuildBoothUMultEncoders(SigSpec Y, SigSpec &one_int, SigSpec &two_int,
				     SigSpec &s_int, SigSpec &sb_int, RTLIL::Module *module, int &encoder_ix)
	{
		int y_sz = GetSize(Y);

		for (int y_ix = 0; y_ix < y_sz;) {
			std::string enc_name = "bur_enc_" + std::to_string(encoder_ix) + "_";

			std::string two_name = "two_int" + std::to_string(encoder_ix);
			two_int.append(module->addWire(new_id(two_name, __LINE__, ""), 1));

			std::string one_name = "one_int" + std::to_string(encoder_ix);
			one_int.append(module->addWire(new_id(one_name, __LINE__, ""), 1));

			std::string s_name = "s_int" + std::to_string(encoder_ix);
			s_int.append(module->addWire(new_id(s_name, __LINE__, ""), 1));

			std::string sb_name = "sb_int" + std::to_string(encoder_ix);
			sb_int.append(module->addWire(new_id(sb_name, __LINE__, ""), 1));

			if (y_ix == 0) {

				BuildBur4e(enc_name, State::S0, Y[y_ix],
					   Y[y_ix + 1], one_int[encoder_ix], two_int[encoder_ix], s_int[encoder_ix],
					   sb_int[encoder_ix]);

				y_ix = y_ix + 1;
				encoder_ix++;
			} else {
				//
				// step case. If multiplier ends on a boundary
				// then add an extra booth encoder bounded by
				// zeroes to ensure unsigned works.
				//
				SigBit y0, y1, y2;

				bool need_padded_cell = false;

				if (y_ix > y_sz - 1) {
					y0 = State::S0;
					need_padded_cell = false;
				} else {
					y0 = Y[y_ix];
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y1 = State::S0;
				} else {
					y1 = Y[y_ix];
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y2 = State::S0;
				} else {
					if (y_ix == y_sz - 1)
						need_padded_cell = true;
					else
						need_padded_cell = false;
					y2 = Y[y_ix];

					BuildBur4e(enc_name, y0, y1, y2, one_int[encoder_ix], two_int[encoder_ix], s_int[encoder_ix],
						   sb_int[encoder_ix]);
				}

				encoder_ix++;

				if (need_padded_cell == true) {

					// make extra encoder cell
					// y_ix at y0, rest 0

					std::string enc_name = "br_enc_pad" + std::to_string(encoder_ix) + "_";

					std::string two_name = "two_int" + std::to_string(encoder_ix);
					two_int.append(module->addWire(new_id(two_name, __LINE__, ""), 1));

					std::string one_name = "one_int" + std::to_string(encoder_ix);
					one_int.append(module->addWire(new_id(two_name, __LINE__, ""), 1));

					std::string s_name = "s_int" + std::to_string(encoder_ix);
					s_int.append(module->addWire(new_id(s_name, __LINE__, ""), 1));

					std::string sb_name = "sb_int" + std::to_string(encoder_ix);
					sb_int.append(module->addWire(new_id(sb_name, __LINE__, ""), 1));

					SigBit one_o_int, two_o_int, s_o_int, sb_o_int;
					BuildBur4e(enc_name, Y[y_ix], State::S0,
						   State::S0, one_o_int, two_o_int, s_o_int, sb_o_int);

					module->connect(one_int[encoder_ix], one_o_int);
					module->connect(two_int[encoder_ix], two_o_int);
					module->connect(s_int[encoder_ix], s_o_int);
					module->connect(sb_int[encoder_ix], sb_o_int);
					y_ix++;
					encoder_ix++;
				}
			}
		}
	}

	/*
	  Signed Multiplier
	*/
	void CreateBoothSMult(RTLIL::Module *module, SigSpec X, SigSpec Y, SigSpec Z)
	{ // product
		int x_sz = X.size(), y_sz = Y.size(), z_sz = Z.size();

		unsigned enc_count = (y_sz / 2) + (((y_sz % 2) != 0) ? 1 : 0);
		int dec_count = x_sz + 1;

		int fa_count = x_sz + 4;
		int fa_row_count = enc_count - 1;

		log("Signed multiplier generator using low Power Negative First Booth Algorithm. Multiplicand of size %d Multiplier of size %d. "
		    "Result of size %d. %d encoders %d decoders\n",
		    x_sz, y_sz, z_sz, enc_count, dec_count);

		SigSpec negi_n_int, twoi_n_int, onei_n_int, cori_n_int;

		negi_n_int.extend_u0(enc_count);
		twoi_n_int.extend_u0(enc_count);
		onei_n_int.extend_u0(enc_count);
		cori_n_int.extend_u0(enc_count);

		for (unsigned encoder_ix = 1; encoder_ix <= enc_count; encoder_ix++) {
			std::string enc_name = "enc_" + std::to_string(encoder_ix) + "_";
			std::string negi_name = "negi_n_int" + std::to_string(encoder_ix) + "_";
			negi_n_int[encoder_ix - 1] = module->addWire(new_id(negi_name, __LINE__, ""), 1);
			std::string twoi_name = "twoi_n_int_" + std::to_string(encoder_ix) + "_";
			twoi_n_int[encoder_ix - 1] = module->addWire(new_id(twoi_name, __LINE__, ""), 1);
			std::string onei_name = "onei_n_int_" + std::to_string(encoder_ix) + "_";
			onei_n_int[encoder_ix - 1] = module->addWire(new_id(onei_name, __LINE__, ""), 1);
			std::string cori_name = "cori_n_int_" + std::to_string(encoder_ix) + "_";
			cori_n_int[encoder_ix - 1] = module->addWire(new_id(cori_name, __LINE__, ""), 1);

			if (encoder_ix == 1) {

				BuildBr4e(enc_name, State::S0, Y[0], Y[1],
					  negi_n_int[encoder_ix - 1], twoi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  cori_n_int[encoder_ix - 1]);

			} else {
				SigBit y1, y2, y3;

				y1 = Y[(encoder_ix - 1) * 2 - 1];

				if ((encoder_ix - 1) * 2 >= (unsigned)y_sz)
					y2 = State::S0; // constant 0
				else
					y2 = Y[(encoder_ix - 1) * 2]; // 0

				if (((encoder_ix - 1) * 2 + 1) >= (unsigned)y_sz)
					y3 = State::S0; // constant 0
				else
					y3 = Y[(encoder_ix - 1) * 2 + 1]; //+1

				BuildBr4e(enc_name, y1, y2, y3,
					  negi_n_int[encoder_ix - 1], twoi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  cori_n_int[encoder_ix - 1]);
			}
		}

		// Decoders and PP generation
		SigSpec PPij(State::S0, enc_count * dec_count);
		SigSpec nxj(State::S0, enc_count * dec_count);

		for (int encoder_ix = 1; encoder_ix <= (int)enc_count; encoder_ix++) {
			for (int decoder_ix = 1; decoder_ix <= dec_count; decoder_ix++) {
				std::string ppij_name = "ppij_" + std::to_string(encoder_ix) + "_" + std::to_string(decoder_ix) + "_";
				PPij[((encoder_ix - 1) * dec_count) + decoder_ix - 1] = module->addWire(new_id(ppij_name, __LINE__, ""), 1);
				std::string nxj_name;
				if (decoder_ix == 1)
					nxj_name = "nxj_pre_dec" + std::to_string(encoder_ix) + "_" + std::to_string(decoder_ix) + "_";
				else
					nxj_name = "nxj_" + std::to_string(encoder_ix) + "_" + std::to_string(decoder_ix) + "_";

				nxj[((encoder_ix - 1) * dec_count) + decoder_ix - 1] = module->addWire(new_id(nxj_name, __LINE__, ""), 1);
			}
		}

		//
		// build decoder array
		//

		for (int encoder_ix = 1; encoder_ix <= (int)enc_count; encoder_ix++) {
			// pre-decoder
			std::string pre_dec_name = "pre_dec_" + std::to_string(encoder_ix) + "_";

			if (encoder_ix == 1) {
				// quadrant 1 optimization
			} else {
				auto cell = module->addCell(new_id(pre_dec_name, __LINE__, ""), ID($_NOT_));
				cell->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));
				cell->setPort(ID::A, negi_n_int[encoder_ix - 1]);
				cell->setPort(ID::Y, nxj[(encoder_ix - 1) * dec_count]);
			}

			for (int decoder_ix = 1; decoder_ix < dec_count; decoder_ix++) {
				// range 1..8

				// quadrant 1 optimization.
				if ((decoder_ix == 1 || decoder_ix == 2) && encoder_ix == 1)
					continue;

				std::string dec_name = "dec_" + std::to_string(encoder_ix) + "_" + std::to_string(decoder_ix) + "_";

				BuildBr4d(dec_name, nxj[((encoder_ix - 1) * dec_count) + decoder_ix - 1], twoi_n_int[encoder_ix - 1],
					  X[decoder_ix - 1], negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  PPij[((encoder_ix - 1) * dec_count) + decoder_ix - 1], nxj[((encoder_ix - 1) * dec_count) + decoder_ix]);
			}

			// duplicate end for sign fix
			// applies to 9th decoder (xsz+1 decoder).
			std::string dec_name = "dec_" + std::to_string(encoder_ix) + "_" + std::to_string(x_sz + 1) + "_";
			SigBit unused_op;
			BuildBr4d(dec_name, nxj[((encoder_ix - 1) * dec_count) + dec_count - 1], twoi_n_int[encoder_ix - 1],
				  X[dec_count - 2], negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
				  PPij[((encoder_ix - 1) * dec_count) + dec_count - 1], unused_op);
		}

		//
		// sum up the partial products
		//
		int fa_el_ix = 0;
		int fa_row_ix = 0;
		// use 1 d arrays (2d cannot have variable sized indices)
		SigSpec fa_sum_n(State::S0, fa_row_count * fa_count);
		SigSpec fa_carry_n(State::S0, fa_row_count * fa_count);

		for (fa_row_ix = 0; fa_row_ix < fa_row_count; fa_row_ix++) {
			for (fa_el_ix = 0; fa_el_ix < fa_count; fa_el_ix++) {

				std::string fa_sum_name = "fa_sum_n_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_";
				fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix] = module->addWire(new_id(fa_sum_name, __LINE__, ""), 1);
				std::string fa_carry_name = "fa_carry_n" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_";
				fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix] = module->addWire(new_id(fa_carry_name, __LINE__, ""), 1);
			}
		}

		// full adder creation
		std::string bfa_name;
		std::string exc_inv_name;
		for (fa_row_ix = 0; fa_row_ix < fa_row_count; fa_row_ix++) {
			for (fa_el_ix = 0; fa_el_ix < fa_count; fa_el_ix++) {
				// base case: 1st row. Inputs from decoders
				// Note in rest of tree inputs from prior addition and a decoder
				if (fa_row_ix == 0) {
					// beginning
					// base case:
					// first two cells: have B input hooked to 0.
					if (fa_el_ix == 0) {
						// quadrant 1: we hard code these using non-booth
						fa_el_ix++;

					}
					// step case
					else if (fa_el_ix >= 2 && fa_el_ix <= x_sz) {
						// middle (2...x_sz cells)
						bfa_name = "bfa_0_step_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";
						auto cell = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell->setParam(ID::WIDTH, 1);
						cell->setPort(ID::A, PPij[(0 * dec_count) + fa_el_ix]);
						cell->setPort(ID::B, PPij[(1 * dec_count) + fa_el_ix - 2]);
						cell->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
					}
					// end 3 cells: x_sz+1.2.3
					//
					else {
						// fa_el_ix = x_sz+1
						bfa_name = "bfa_0_se_0" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";
						auto cell1 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell1->setParam(ID::WIDTH, 1);
						cell1->setPort(ID::A, PPij[(0 * dec_count) + x_sz]);
						cell1->setPort(ID::B, PPij[(1 * dec_count) + fa_el_ix - 2]);
						cell1->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell1->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell1->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);

						// exception:invert ppi
						fa_el_ix++;
						exc_inv_name = "bfa_0_exc_inv1_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";
						auto cellinv1 = module->addCell(new_id(exc_inv_name, __LINE__, ""), ID($_NOT_));
						cellinv1->add_strpool_attribute(ID::src, cellinv1->get_strpool_attribute(ID::src));

						RTLIL::Wire *d08_inv = module->addWire(NEW_ID, 1);

						cellinv1->setPort(ID::A, PPij[(0 * dec_count) + dec_count - 1]);
						cellinv1->setPort(ID::Y, d08_inv);

						exc_inv_name = "bfa_0_exc_inv2_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";

						auto cellinv2 = module->addCell(new_id(exc_inv_name, __LINE__, ""), ID($_NOT_));
						cellinv2->add_strpool_attribute(ID::src, cellinv2->get_strpool_attribute(ID::src));
						RTLIL::Wire *d18_inv = module->addWire(NEW_ID, 1);
						cellinv2->setPort(ID::A, PPij[(1 * dec_count) + dec_count - 1]);
						cellinv2->setPort(ID::Y, d18_inv);

						bfa_name = "bfa_0_se_1_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";

						auto cell2 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell2->setParam(ID::WIDTH, 1);
						cell2->setPort(ID::A, d08_inv);
						cell2->setPort(ID::B, d18_inv);
						cell2->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell2->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell2->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);

						// sign extension
						fa_el_ix++;
						bfa_name = "bfa_0_se_2_" + std::to_string(fa_row_ix) + "_" + std::to_string(fa_el_ix) + "_L";
						auto cell3 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell3->setParam(ID::WIDTH, 1);
						cell3->setPort(ID::A, State::S0);
						cell3->setPort(ID::B, State::S1);
						cell3->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell3->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell3->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
					}
				}

				// step case: 2nd and rest of rows. (fa_row_ix == 1...n)
				// special because these are driven by a decoder and prior fa.
				else {
					// beginning
					if (fa_el_ix == 0) {
						// first two cells: have B input hooked to 0.
						// column is offset by row_ix*2
						bfa_name = "bfa_" + std::to_string(fa_row_ix) + "_base_" + std::to_string(fa_row_ix) + "_" +
							   std::to_string(fa_el_ix) + "_L";
						auto cell1 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell1->setParam(ID::WIDTH, 1);
						cell1->setPort(ID::A, fa_sum_n[(fa_row_ix - 1) * fa_count + 2]); // from prior full adder row
						cell1->setPort(ID::B, State::S0);
						cell1->setPort(ID::C, cori_n_int[fa_row_ix]);
						cell1->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell1->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
						fa_el_ix++;

						bfa_name = "bfa_" + std::to_string(fa_row_ix) + "_base_" + std::to_string(fa_row_ix) + "_" +
							   std::to_string(fa_el_ix) + "_L";
						auto cell2 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell2->setParam(ID::WIDTH, 1);
						cell2->setPort(ID::A,
							       fa_sum_n[(fa_row_ix - 1) * fa_count + 3]); // from prior full adder row
						cell2->setPort(ID::B, State::S0);
						cell2->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell2->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell2->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
					}

					else if (fa_el_ix >= 2 && fa_el_ix <= x_sz + 1) {
						// middle (2...x_sz+1 cells)
						bfa_name = "bfa_" + std::to_string(fa_row_ix) + "_step_" + std::to_string(fa_row_ix) + "_" +
							   std::to_string(fa_el_ix) + "_L";
						auto cell = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell->setParam(ID::WIDTH, 1);
						cell->setPort(ID::A, fa_sum_n[(fa_row_ix - 1) * fa_count + fa_el_ix + 2]);
						cell->setPort(ID::B, PPij[(fa_row_ix + 1) * dec_count + fa_el_ix - 2]);
						cell->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
					}

					else if (fa_el_ix > x_sz + 1) {
						// end two bits: sign extension
						std::string se_inv_name;
						se_inv_name = "bfa_" + std::to_string(fa_row_ix) + "_se_inv_" + std::to_string(fa_row_ix) + "_" +
							      std::to_string(fa_el_ix) + "_L";
						auto cellinv = module->addCell(new_id(se_inv_name, __LINE__, ""), ID($_NOT_));
						cellinv->add_strpool_attribute(ID::src, cellinv->get_strpool_attribute(ID::src));
						RTLIL::Wire *d_inv = module->addWire(NEW_ID, 1);
						cellinv->setPort(ID::A, PPij[((fa_row_ix + 1) * dec_count) + dec_count - 1]);
						cellinv->setPort(ID::Y, d_inv);

						bfa_name = "bfa_" + std::to_string(fa_row_ix) + "_se_" + std::to_string(fa_row_ix) + "_" +
							   std::to_string(fa_el_ix) + "_L";
						auto cell1 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell1->setParam(ID::WIDTH, 1);
						cell1->setPort(ID::A, fa_carry_n[((fa_row_ix - 1) * fa_count) + fa_count - 1]);
						cell1->setPort(ID::B, d_inv);
						cell1->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell1->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell1->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
						fa_el_ix++;

						// sign extension
						bfa_name = "bfa_" + std::to_string(fa_row_ix) + "_se_" + std::to_string(fa_row_ix) + "_" +
							   std::to_string(fa_el_ix) + "_L";
						auto cell2 = module->addCell(new_id(bfa_name, __LINE__, ""), ID($fa));
						cell2->setParam(ID::WIDTH, 1);
						cell2->setPort(ID::A, State::S0);
						cell2->setPort(ID::B, State::S1);
						cell2->setPort(ID::C, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix - 1]);
						cell2->setPort(ID::X, fa_carry_n[(fa_row_ix * fa_count) + fa_el_ix]);
						cell2->setPort(ID::Y, fa_sum_n[(fa_row_ix * fa_count) + fa_el_ix]);
					}
				}
			}
		}

		// instantiate the cpa
		SigSpec cpa_carry;

		for (int cix = 0; cix < z_sz; cix++) {
			std::string cpa_cix_name = "cpa_carry_" + std::to_string(cix) + "_";
			cpa_carry.append(module->addWire(new_id(cpa_cix_name, __LINE__, ""), 1));
		}

		for (int cpa_ix = 0; cpa_ix < z_sz; cpa_ix++) {

			// The end case where we pass the last two summands
			// from prior row directly to product output
			// without using a cpa cell. This is always
			// 0,1 index of prior fa row
			if (cpa_ix <= fa_row_count * 2 - 1) {
				int fa_row_ix = cpa_ix / 2;

				std::string buf_name =
				  "pp_buf_" + std::to_string(cpa_ix) + "_" + "driven_by_fa_row_" + std::to_string(fa_row_ix) + "_";
				auto buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
				buf->setPort(ID::A, fa_sum_n[(fa_row_ix * fa_count) + 0]);
				buf->setParam(ID::A_WIDTH, 1);
				buf->setParam(ID::Y_WIDTH, 1);
				buf->setParam(ID::A_SIGNED, true);
				buf->setPort(ID::Y, Z[cpa_ix]);

				cpa_ix++;
				buf_name = "pp_buf_" + std::to_string(cpa_ix) + "_" + "driven_by_fa_row_" + std::to_string(fa_row_ix) + "_";
				buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
				buf->setPort(ID::A, fa_sum_n[(fa_row_ix * fa_count) + 1]);
				buf->setParam(ID::A_WIDTH, 1);
				buf->setParam(ID::Y_WIDTH, 1);
				buf->setParam(ID::A_SIGNED, true);
				buf->setPort(ID::Y, Z[cpa_ix]);
			} else {
				int offset = fa_row_count * 2;
				bool base_case = cpa_ix - offset == 0 ? true : false;
				std::string cpa_name = "cpa_" + std::to_string(cpa_ix - offset) + "_";

				SigBit ci;
				if (base_case)
					ci = cori_n_int[enc_count - 1];
				else
					ci = cpa_carry[cpa_ix - offset - 1];

				SigBit op;
				BuildHa(cpa_name, fa_sum_n[(fa_row_count - 1) * fa_count + cpa_ix - offset + 2], ci, op,
					cpa_carry[cpa_ix - offset]);
				module->connect(Z[cpa_ix], op);
			}
		}

		//
		// instantiate the quadrant 1 cell. This is the upper right
		// quadrant which can be realized using non-booth encoded logic.
		//
		std::string q1_name = "icb_booth_q1_";

		SigBit pp0_o_int;
		SigBit pp1_o_int;
		SigBit nxj_o_int;
		SigBit cor_o_int;

		BuildBoothQ1(q1_name,
			     negi_n_int[0], // negi
			     cori_n_int[0], // cori

			     X[0], X[1], Y[0], Y[1],

			     nxj_o_int, cor_o_int, pp0_o_int, pp1_o_int);

		module->connect(fa_sum_n[(0 * fa_count) + 0], pp0_o_int);
		module->connect(fa_sum_n[(0 * fa_count) + 1], pp1_o_int);
		module->connect(fa_carry_n[(0 * fa_count) + 1], cor_o_int);
		module->connect(nxj[(0 * dec_count) + 2], nxj_o_int);
	}
};

struct BoothPass : public Pass {
	BoothPass() : Pass("booth", "Map $mul to booth multipliers") {}
	void execute(vector<string> args, RTLIL::Design *design) override
	{
		(void)args;
		log_header(design,
			   "Executing booth pass. Generating Booth Multiplier structures for signed/unsigned multipliers of 4 bits or more\n");
		for (auto mod : design->selected_modules())
			if (!mod->has_processes_warn()) {
				BoothPassWorker worker(mod);
				worker.run();
				log_header(design, "Created %d booth multipliers.\n", worker.booth_counter);
			}
	}
} MultPass;

PRIVATE_NAMESPACE_END
