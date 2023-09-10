/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
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
  MultPass
  --------

  Replace $mul with booth encoded multipliers. Two different
  architectures used for signed/unsigned.

  References:
  Signed architecture: A Low Power Radix-4 Booth Multipliers with Pre-Encoded Mechanism, IEEE Access
  https://ieeexplore.ieee.org/document/9121226

  Unsigned architecture: Gary Bewick, Fast Multiplication algorithms and implementation. Stanford PhD:
  http://i.stanford.edu/pub/cstr/reports/csl/tr/94/617/CSL-TR-94-617.pdf

  How to use:
  Add multpass to your yosys script eg:

  read_verilog smultiply5_rtl.v
  opt
  wreduce
  opt
  multpass
  alumacc
  maccmap
  opt
  techmap -map ./techmap.v
  dfflibmap -liberty NangateOpenCellLibrary_typical.lib
  abc -liberty NangateOpenCellLibrary_typical.lib
  stat -liberty NangateOpenCellLibrary_typical.lib
  write_verilog -norename booth_final.v
*/

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MultPassWorker {

	RTLIL::Module *module;
	SigMap sigmap;
	int booth_counter;

	MultPassWorker(RTLIL::Module *module) : module(module), sigmap(module) { booth_counter = 0; }

	// Helper routines for building architecture subcomponents

	RTLIL::Wire *mk_wireFromSigSpec(const SigSpec &v)
	{

		auto g = module->addCell(NEW_ID, ID($pos));
		Wire *ret = module->addWire(NEW_ID, 1);
		g->setPort(ID::A, v);
		g->setPort(ID::Y, ret);
		g->setParam(ID::A_WIDTH, 1);
		g->setParam(ID::Y_WIDTH, 1);
		g->setParam(ID::A_SIGNED, false);
		return ret;
	}

	// fuse wires.
	void join_wires_with_buffer(RTLIL::Wire *ip, RTLIL::Wire *op)
	{
		std::string wire_name = "join_";
		auto g = module->addCell(new_id(wire_name, __LINE__, ""), ID($pos));
		g->setParam(ID::A_WIDTH, 1);
		g->setParam(ID::Y_WIDTH, 1);
		g->setParam(ID::A_SIGNED, false);
		g->setPort(ID::A, ip);
		g->setPort(ID::Y, op);
	}

	// Unary gate
	RTLIL::Wire *mk_ugate1(const RTLIL::IdString &red_typ, std::string &name, RTLIL::Wire *ip1, std::string &op_name)
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
	RTLIL::Wire *mk_ugate2(const RTLIL::IdString &red_typ, std::string &name, RTLIL::Wire *ip1, RTLIL::Wire *ip2, std::string &op_name)
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
	void BuildBur4d_lsb(std::string &name, RTLIL::Wire *lsb_i, RTLIL::Wire *one_i, RTLIL::Wire *s_i, RTLIL::Wire *&ppij_o,
			    std::string op_wire_name)
	{
		std::string empty;
		auto and_op = mk_ugate2(ID($and), name, lsb_i, one_i, empty);
		ppij_o = mk_ugate2(ID($xor), name, and_op, s_i, op_wire_name);
	}

	// Booth unsigned radix4 decoder
	void BuildBur4d_n(std::string &name, RTLIL::Wire *yn_i, RTLIL::Wire *ynm1_i, RTLIL::Wire *one_i, RTLIL::Wire *two_i, RTLIL::Wire *s_i,
			  RTLIL::Wire *&ppij_o)
	{
		// ppij = ((yn & one)   | (ynm1 & two)) ^ s;
		std::string empty;
		auto an1 = mk_ugate2(ID($and), name, yn_i, one_i, empty);
		auto an2 = mk_ugate2(ID($and), name, ynm1_i, two_i, empty);
		auto or1 = mk_ugate2(ID($or), name, an1, an2, empty);
		ppij_o = mk_ugate2(ID($xor), name, s_i, or1, empty);
	}

	// Booth unsigned radix4 decoder
	void BuildBur4d_msb(std::string &name, RTLIL::Wire *msb_i, RTLIL::Wire *two_i, RTLIL::Wire *s_i, RTLIL::Wire *&ppij_o)
	{
		// ppij = (msb & two)  ^ s;
		std::string empty;
		auto an1 = mk_ugate2(ID($and), name, msb_i, two_i, empty);
		ppij_o = mk_ugate2(ID($xor), name, s_i, an1, empty);
	}

	// half adder, used in CPA
	void BuildHa(std::string &name, RTLIL::Wire *a_i, RTLIL::Wire *b_i, RTLIL::Wire *&s_o, RTLIL::Wire *&c_o)
	{
		std::string empty;
		s_o = mk_ugate2(ID($xor), name, a_i, b_i, empty);
		c_o = mk_ugate2(ID($and), name, a_i, b_i, empty);
	}

	// Booth unsigned radix 4 encoder
	void BuildBur4e(std::string &name, RTLIL::Wire *y0_i, RTLIL::Wire *y1_i, RTLIL::Wire *y2_i,

			RTLIL::Wire *&one_o, RTLIL::Wire *&two_o, RTLIL::Wire *&s_o, RTLIL::Wire *&sb_o)
	{

		std::string empty;
		one_o = mk_ugate2(ID($xor), name, y0_i, y1_i, empty);
		s_o = y2_i;
		sb_o = mk_ugate1(ID($not), name, y2_i, empty);
		auto inv_y1_xor_y2 = mk_ugate1(ID($not), name, mk_ugate2(ID($xor), name, y1_i, y2_i, empty), empty);
		two_o = mk_ugate1(ID($not), name, mk_ugate2(ID($or), name, inv_y1_xor_y2, one_o, empty), empty);
	}

	void BuildBr4e(std::string &name, RTLIL::Wire *y2_m1_i,
		       RTLIL::Wire *y2_i, // y2i
		       RTLIL::Wire *y2_p1_i,

		       RTLIL::Wire *&negi_o, RTLIL::Wire *&twoi_n_o, RTLIL::Wire *&onei_n_o, RTLIL::Wire *&cori_o)
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
	void BuildBr4d(std::string &name, RTLIL::Wire *nxj_m1_i, RTLIL::Wire *twoi_n_i, RTLIL::Wire *xj_i, RTLIL::Wire *negi_i, RTLIL::Wire *onei_n_i,

		       RTLIL::Wire *&ppij_o, RTLIL::Wire *&nxj_o)
	{

		std::string empty;
		// nxj_in = xnor(xj,negi)
		// nxj_o = xnj_in,
		// ppij = ~( (nxj_m1_i | twoi_n_i) & (nxj_int | onei_n_i));
		nxj_o = mk_ugate2(ID($xnor), name, xj_i, negi_i, empty);
		RTLIL::Wire *or1 = mk_ugate2(ID($or), name, nxj_m1_i, twoi_n_i, empty);
		RTLIL::Wire *or2 = mk_ugate2(ID($or), name, nxj_o, onei_n_i, empty);
		ppij_o = mk_ugate1(ID($not), name, mk_ugate2(ID($and), name, or1, or2, empty), empty);
	}

	/*
	  In signed case 1st two bits best realised
	  using non-booth encoded logic. We can save a booth
	  encoder for the first couple of bits.
	*/
	void BuildBoothQ1(std::string &name, RTLIL::Wire *negi_i, RTLIL::Wire *cori_i, RTLIL::Wire *x0_i, RTLIL::Wire *x1_i, RTLIL::Wire *y0_i,
			  RTLIL::Wire *y1_i,

			  RTLIL::Wire *&nxj_o, RTLIL::Wire *&cor_o, RTLIL::Wire *&pp0_o, RTLIL::Wire *&pp1_o

	)
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
		RTLIL::Wire *pp1_1_int = mk_ugate2(ID($and), name, x1_i, y0_i, empty);
		RTLIL::Wire *pp1_2_int = mk_ugate2(ID($and), name, x0_i, y1_i, empty);
		pp1_o = mk_ugate2(ID($xor), name, pp1_1_int, pp1_2_int, empty);

		RTLIL::Wire *pp1_nor_pp0 = mk_ugate1(ID($not), name, mk_ugate2(ID($or), name, pp1_o, pp0_o, empty), empty);
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
						CreateBoothUMult(module, x_sz_revised, y_sz_revised, required_op_size,
								 expanded_A, // multiplicand
								 expanded_B, // multiplier(scanned)
								 expanded_Y  // result
						);
					else /*signed multiplier */
						CreateBoothSMult(module, x_sz_revised, y_sz_revised, required_op_size,
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

	void CreateBoothUMult(RTLIL::Module *module, int x_sz, int y_sz, int z_sz,
			      RTLIL::Wire *X, // multiplicand
			      RTLIL::Wire *Y, // multiplier
			      RTLIL::Wire *Z)
	{ // result

		std::vector<RTLIL::Wire *> one_int;
		std::vector<RTLIL::Wire *> two_int;
		std::vector<RTLIL::Wire *> s_int;
		std::vector<RTLIL::Wire *> sb_int;
		int encoder_count = 0;

		BuildBoothUMultEncoders(Y, y_sz, one_int, two_int, s_int, sb_int, module, encoder_count);

		// Build the decoder rows
		// format of each Partial product to be passed to CSA
		// tree builder:
		//
		// Bits to be added
		// Shift
		// Sign bit to be added
		//
		std::vector<std::tuple<std::vector<RTLIL::Wire *>, int, RTLIL::Wire *>> ppij_int;

		static int constant_ix;
		constant_ix++;
		std::string buf_name = "constant_buf_" + std::to_string(constant_ix);
		auto buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
		RTLIL::Wire *constant_one = module->addWire(new_id(buf_name, __LINE__, ""), 1);
		buf->setPort(ID::A, State::S1);
		buf->setParam(ID::A_WIDTH, 1);
		buf->setParam(ID::Y_WIDTH, 1);
		buf->setParam(ID::A_SIGNED, true);
		buf->setPort(ID::Y, constant_one);

		constant_ix++;
		buf_name = "constant_buf_" + std::to_string(constant_ix);
		buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
		RTLIL::Wire *constant_zero = module->addWire(new_id(buf_name, __LINE__, ""), 1);
		buf->setPort(ID::A, State::S0);
		buf->setParam(ID::A_WIDTH, 1);
		buf->setParam(ID::Y_WIDTH, 1);
		buf->setParam(ID::A_SIGNED, true);
		buf->setPort(ID::Y, constant_zero);

		// Row 0: special case 1. Format S/.S.S.C.Data
		std::vector<RTLIL::Wire *> ppij_row_0;
		BuildBoothUMultDecoderRow0(module, X, s_int, sb_int, one_int, two_int, ppij_row_0);

		// data, shift, sign
		ppij_int.push_back(std::make_tuple(ppij_row_0, 0, s_int[0]));

		for (int i = 1; i < encoder_count - 2; i++) {
			// format 1,S.Data.shift = encoder_ix*2,sign = sb_int[i]
			std::vector<RTLIL::Wire *> ppij_row_n;

			BuildBoothUMultDecoderRowN(module,
						   X, // multiplicand
						   one_int[i], two_int[i], s_int[i], sb_int[i], ppij_row_n, constant_one, i,
						   false, // include sign
						   false  // include constant
			);
			// data, shift, sign
			ppij_int.push_back(std::make_tuple(ppij_row_n, i * 2, s_int[i]));
		}

		// Build second to last row
		// format S/,Data + sign bit
		std::vector<RTLIL::Wire *> ppij_row_em1;
		BuildBoothUMultDecoderRowN(module, X, one_int[encoder_count - 2], two_int[encoder_count - 2], s_int[encoder_count - 2],
					   sb_int[encoder_count - 2], ppij_row_em1, constant_one, encoder_count - 2,
					   false, // include sign
					   true	  // no constant
		);
		ppij_int.push_back(std::make_tuple(ppij_row_em1, (encoder_count - 2) * 2, s_int[encoder_count - 2]));
		// Build last row
		// format Data + sign bit
		std::vector<RTLIL::Wire *> ppij_row_e;
		BuildBoothUMultDecoderRowN(module, X, one_int[encoder_count - 1], two_int[encoder_count - 1], s_int[encoder_count - 1],
					   sb_int[encoder_count - 1], ppij_row_e, constant_one, encoder_count - 1,
					   true, // no sign
					   true	 // no constant
		);
		ppij_int.push_back(std::make_tuple(ppij_row_e, (encoder_count - 1) * 2, s_int[encoder_count - 1]));

		//  Debug dump out partial products
		//  DebugDumpPP(ppij_int);

		// Summation of Partial Products (Wallace Tree)
		std::vector<std::vector<RTLIL::Wire *>> aligned_pp;
		aligned_pp.resize(encoder_count + 1); // make an entirely redundant row
		// just for sign bit in lsb. (We then filter this out).

		// resize all to be same size as z
		for (int i = 0; i < encoder_count + 1; i++)
			aligned_pp[i].resize(z_sz);

		AlignPP(x_sz, z_sz, ppij_int, aligned_pp);

		// Debug: dump out aligned partial products.
		// Later on yosys will clean up unused constants
		//  DebugDumpAlignPP(aligned_pp);

		std::vector<RTLIL::Wire *> s_vec;
		std::vector<RTLIL::Wire *> c_vec;
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
					RTLIL::Wire *X, // multiplicand
					std::vector<RTLIL::Wire *> &s_int, std::vector<RTLIL::Wire *> &sb_int, std::vector<RTLIL::Wire *> &one_int,
					std::vector<RTLIL::Wire *> &two_int, std::vector<RTLIL::Wire *> &ppij_vec)
	{
		(void)module;
		int x_sz = GetSize(X);

		// lsb
		std::string dec_name = "row0_lsb_dec";

		RTLIL::Wire *ppij;
		std::string ppij_name = "ppij_0_0";
		BuildBur4d_lsb(dec_name, mk_wireFromSigSpec(SigSpec(X, 0, 1)), one_int[0], s_int[0], ppij, ppij_name);
		ppij_vec.push_back(ppij);

		// 1..xsize -1
		for (int i = 1; i < x_sz; i++) {
			dec_name = "row0_dec_" + std::to_string(i);
			RTLIL::Wire *ppij;
			BuildBur4d_n(dec_name, mk_wireFromSigSpec(SigSpec(X, i, 1)), mk_wireFromSigSpec(SigSpec(X, i - 1, 1)), one_int[0], two_int[0],
				     s_int[0], ppij);
			ppij_vec.push_back(ppij);
		}

		// The redundant bit. Duplicate decoding of last bit.
		dec_name = "row0_dec_msb";
		BuildBur4d_msb(dec_name, mk_wireFromSigSpec(SigSpec(X, x_sz - 1, 1)), two_int[0], s_int[0], ppij);
		ppij_vec.push_back(ppij);

		// append the sign bits
		ppij_vec.push_back(s_int[0]);
		ppij_vec.push_back(s_int[0]);
		ppij_vec.push_back(sb_int[0]);
	}

	// Build a generic row of decoders.

	void BuildBoothUMultDecoderRowN(RTLIL::Module *module,
					RTLIL::Wire *X, // multiplicand
					RTLIL::Wire *one_int, RTLIL::Wire *two_int, RTLIL::Wire *s_int, RTLIL::Wire *sb_int,
					std::vector<RTLIL::Wire *> &ppij_vec, RTLIL::Wire *constant_one, int row_ix, bool no_sign, bool no_constant)
	{
		(void)module;
		int x_sz = GetSize(X);

		// lsb
		std::string ppij_name = "ppij_" + std::to_string(row_ix) + "_0";
		RTLIL::Wire *ppij = nullptr;
		std::string empty;
		std::string dec_name = "row" + std::to_string(row_ix) + "_lsb_dec";
		BuildBur4d_lsb(dec_name, mk_wireFromSigSpec(SigSpec(X, 0, 1)), one_int, s_int, ppij, empty);

		ppij_vec.push_back(ppij);

		// core bits
		for (int i = 1; i < x_sz; i++) {

			dec_name = "row_" + std::to_string(row_ix) + "_dec_" + std::to_string(i);
			RTLIL::Wire *ppij = nullptr;
			BuildBur4d_n(dec_name, mk_wireFromSigSpec(SigSpec(X, i, 1)), mk_wireFromSigSpec(SigSpec(X, i - 1, 1)), one_int, two_int,
				     s_int, ppij);
			ppij_vec.push_back(ppij);
		}

		// redundant bit

		dec_name = "row_dec_red";
		BuildBur4d_msb(dec_name, mk_wireFromSigSpec(SigSpec(X, x_sz - 1, 1)), two_int, s_int, ppij);
		ppij_vec.push_back(ppij);

		// sign bit
		if (no_sign == false) // if no sign is false then make a sign bit
			ppij_vec.push_back(sb_int);

		// constant bit
		if (no_constant == false) { // if non constant is false make a constant bit
			ppij_vec.push_back(constant_one);
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

	void BuildCSATree(RTLIL::Module *module, std::vector<std::vector<RTLIL::Wire *>> &bits_to_reduce, std::vector<RTLIL::Wire *> &s_vec,
			  std::vector<RTLIL::Wire *> &c_vec, std::vector<std::vector<RTLIL::Cell *>> &debug_csa_trees)
	{

		if (!(bits_to_reduce.size() > 0))
			return;

		int column_size = bits_to_reduce[0].size();
		int row_size = bits_to_reduce.size();
		std::vector<RTLIL::Wire *> carry_bits_to_add_to_next_column;

		for (int column_ix = 0; column_ix < column_size; column_ix++) {

			// get the bits in this column.
			std::vector<RTLIL::Wire *> column_bits;
			for (int row_ix = 0; row_ix < row_size; row_ix++) {
				if (bits_to_reduce[row_ix].at(column_ix))
					column_bits.push_back(bits_to_reduce[row_ix].at(column_ix));
			}
			for (auto c : carry_bits_to_add_to_next_column) {
#ifdef DEBUG_CSA
				printf("\t Propagating column bit %s to column %d from column %d\n", c->name.c_str(), column_ix, column_ix - 1);
#endif
				column_bits.push_back(c);
			}

			carry_bits_to_add_to_next_column.resize(0);

#ifdef DEBUG_CSA
			printf("Column %d Reducing %d bits\n", column_ix, column_bits.size());
			for (auto b : column_bits) {
				printf("\t %s\n", b->name.c_str());
			}
			printf("\n");
#endif

			RTLIL::Wire *s = nullptr;
			RTLIL::Wire *c = nullptr;
#ifdef DEBUG_CSA
			int csa_count_before = debug_csa_trees[column_ix].size();
#endif

			ReduceBits(module, column_ix, column_bits, s, c, carry_bits_to_add_to_next_column, debug_csa_trees);

			s_vec.push_back(s);
			c_vec.push_back(c);

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
	void AlignPP(int x_sz, int z_sz, std::vector<std::tuple<std::vector<RTLIL::Wire *>, int, RTLIL::Wire *>> &ppij_int,
		     std::vector<std::vector<RTLIL::Wire *>> &aligned_pp)
	{
		unsigned aligned_pp_ix = aligned_pp.size() - 1;

		// default is zero for everything (so don't have to think to hard
		// about padding).

		for (unsigned i = 0; i < aligned_pp.size(); i++) {
			for (int j = 0; j < z_sz; j++) {
				aligned_pp[i][j] = nullptr;
			}
		}

		// for very last row we just have the sign bit
		// Note that the aligned_pp is one row bigger
		// than the ppij_int. We put the sign bit
		// in first column of the last partial product
		// which is at index corresponding to size of multiplicand
		{
			RTLIL::Wire *prior_row_sign = nullptr;
			prior_row_sign = get<2>(ppij_int[aligned_pp_ix - 1]);
			if (prior_row_sign) {
				log_assert(aligned_pp_ix < aligned_pp.size());
				log_assert(x_sz - 1 < (int)(aligned_pp[aligned_pp_ix].size()));
				aligned_pp[aligned_pp_ix][x_sz - 1] = prior_row_sign;
			}
		}

		for (int row_ix = aligned_pp_ix - 1; row_ix >= 0; row_ix--) {
			int shift_amount = get<1>(ppij_int[row_ix]);
			RTLIL::Wire *prior_row_sign = nullptr;

			// copy in data
			unsigned copy_ix = shift_amount;
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
				prior_row_sign = get<2>(ppij_int[row_ix - 1]);
				copy_ix = (row_ix - 1) * 2;
				aligned_pp[row_ix][copy_ix] = prior_row_sign;
			}
		}
	}

	/*
	  Build a Carry Propagate Adder
	  -----------------------------
	  First build the sum and carry vectors to be added.
	  Axioms:
	  c_vec.size() == s_vec.size()
	  result.size() == s_vec.size() + 2; (assume result is reserved to hold correct size)
	*/
	void BuildCPA(RTLIL::Module *module, std::vector<RTLIL::Wire *> &s_vec, std::vector<RTLIL::Wire *> &c_vec, RTLIL::Wire *result)
	{

		static int cpa_id;
		cpa_id++;

		RTLIL::Wire *carry = nullptr;

		log_assert(s_vec.size() == c_vec.size());

		for (unsigned n = 0; n < s_vec.size(); n++) {
			std::string carry_name;

			// Base Case: Bit 0 is sum 0
			if (n == 0) {
				std::string buf_name = "base_buf_" + std::to_string(cpa_id) + "_" + std::to_string(n);
				auto buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
				buf->setPort(ID::A, s_vec[0]);
				buf->setParam(ID::A_WIDTH, 1);
				buf->setParam(ID::Y_WIDTH, 1);
				buf->setParam(ID::A_SIGNED, false);
				buf->setPort(ID::Y, SigSpec(result, 0, 1));

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
				RTLIL::Wire *ha_op;
				BuildHa(ha_name, s_vec[n], c_vec[n - 1], ha_op, carry);

				module->connect(ha_op, SigSpec(result, n, 1));

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IPs [%s] [%s] \n", n, ha_cell->name.c_str(), s_vec[n]->name.c_str(),
				       c_vec[n - 1]->name.c_str());
#endif

			}
			// End Case
			else if (n == (unsigned)((s_vec.size() - 1))) {
				// Make the carry results.. Two extra bits after fa.
				std::string fa_name = "cpa_" + std::to_string(cpa_id) + "_fa_" + std::to_string(n);
				auto fa_cell = module->addCell(new_id(fa_name, __LINE__, ""), ID($fa));
				fa_cell->setParam(ID::WIDTH, 1);
				carry_name = "cpa_" + std::to_string(cpa_id) + "carry_" + std::to_string(n);
				fa_cell->setPort(ID::A, s_vec[n]);
				fa_cell->setPort(ID::B, c_vec[n - 1]);
				fa_cell->setPort(ID::C, carry);
				// wire in result and carry out
				fa_cell->setPort(ID::Y, SigSpec(result, n, 1));

				// make a new carry bit for carry out...
				carry = module->addWire(new_id(carry_name, __LINE__, ""), 1);
				fa_cell->setPort(ID::X, carry);

#ifdef DEBUG_CPA
				printf("CPA bit [%d] Cell %s IPs [%s] [%s] [%s]\n", n, fa_cell->name.c_str(), s_vec[n]->name.c_str(),
				       c_vec[n - 1]->name.c_str(), carry->name.c_str());
#endif
				if (n + 1 < (unsigned)(GetSize(result))) {
					// Now make a half adder: c_vec[n] = carry
					std::string ha_name = "cpa_" + std::to_string(cpa_id) + "_ha_" + std::to_string(n);
					RTLIL::Wire *ha_sum;
					RTLIL::Wire *ha_carry;
					BuildHa(ha_name, c_vec[n], carry, ha_sum, ha_carry);
					if (n + 1 < (unsigned)GetSize(result))
						module->connect(ha_sum, SigSpec(result, n + 1, 1));
					if (n + 2 < (unsigned)GetSize(result))
						module->connect(ha_carry, SigSpec(result, n + 2, 1));
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
				fa_cell->setPort(ID::Y, SigSpec(result, n, 1));
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

	void ReduceBits(RTLIL::Module *module, int column_ix, std::vector<RTLIL::Wire *> &column_bits, RTLIL::Wire *&s_result, RTLIL::Wire *&c_result,
			std::vector<RTLIL::Wire *> &carry_bits_to_sum, std::vector<std::vector<RTLIL::Cell *>> &debug_csa_trees)
	{

		int csa_ix = 0;
		int column_size = column_bits.size();
		static int unique_id = 0;

		unique_id++;

		if (column_size > 0) {
			unsigned var_ix = 0;
			std::vector<RTLIL::Wire *> first_csa_ips;
			// get the first 3 inputs, if possible
			for (var_ix = 0; var_ix < column_bits.size() && first_csa_ips.size() != 3; var_ix++) {
				if (column_bits[var_ix])
					first_csa_ips.push_back(column_bits[var_ix]);
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
					carry_bits_to_sum.push_back(c_wire);

				// Now build the rest of the tree if we can
				while (var_ix <= column_bits.size() - 1) {
					std::vector<RTLIL::Wire *> csa_ips;
					// get the next two variables to sum
					for (; var_ix <= column_bits.size() - 1 && csa_ips.size() < 2;) {
						// skip any empty bits
						if (column_bits[var_ix] != nullptr)
							csa_ips.push_back(column_bits[var_ix]);
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
							carry_bits_to_sum.push_back(c_wire);

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

	void BuildBoothUMultEncoders(RTLIL::Wire *Y, int y_sz, std::vector<RTLIL::Wire *> &one_int, std::vector<RTLIL::Wire *> &two_int,
				     std::vector<RTLIL::Wire *> &s_int, std::vector<RTLIL::Wire *> &sb_int, RTLIL::Module *module, int &encoder_ix)
	{
		for (int y_ix = 0; y_ix < y_sz;) {
			std::string enc_name = "bur_enc_" + std::to_string(encoder_ix) + "_";

			std::string two_name = "two_int" + std::to_string(encoder_ix);
			two_int.push_back(module->addWire(new_id(two_name, __LINE__, ""), 1));

			std::string one_name = "one_int" + std::to_string(encoder_ix);
			one_int.push_back(module->addWire(new_id(one_name, __LINE__, ""), 1));

			std::string s_name = "s_int" + std::to_string(encoder_ix);
			s_int.push_back(module->addWire(new_id(s_name, __LINE__, ""), 1));

			std::string sb_name = "sb_int" + std::to_string(encoder_ix);
			sb_int.push_back(module->addWire(new_id(sb_name, __LINE__, ""), 1));

			if (y_ix == 0) {

				BuildBur4e(enc_name, mk_wireFromSigSpec(State::S0), mk_wireFromSigSpec(SigSpec(Y, y_ix, 1)),
					   mk_wireFromSigSpec(SigSpec(Y, y_ix + 1, 1)), one_int[encoder_ix], two_int[encoder_ix], s_int[encoder_ix],
					   sb_int[encoder_ix]);

				y_ix = y_ix + 1;
				encoder_ix++;
			} else {
				//
				// step case. If multiplier ends on a boundary
				// then add an extra booth encoder bounded by
				// zeroes to ensure unsigned works.
				//
				RTLIL::Wire *y0_wire;
				RTLIL::Wire *y1_wire;
				RTLIL::Wire *y2_wire;

				bool need_padded_cell = false;

				if (y_ix > y_sz - 1) {
					y0_wire = mk_wireFromSigSpec(SigSpec(Y, State::S0));
					need_padded_cell = false;
				} else {
					y0_wire = mk_wireFromSigSpec(SigSpec(Y, y_ix, 1));
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y1_wire = mk_wireFromSigSpec(SigSpec(Y, State::S0));
				} else {
					y1_wire = mk_wireFromSigSpec(SigSpec(Y, y_ix, 1));
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y2_wire = mk_wireFromSigSpec(SigSpec(Y, State::S0));
				} else {
					if (y_ix == y_sz - 1)
						need_padded_cell = true;
					else
						need_padded_cell = false;
					y2_wire = mk_wireFromSigSpec(SigSpec(Y, y_ix, 1));

					BuildBur4e(enc_name, y0_wire, y1_wire, y2_wire, one_int[encoder_ix], two_int[encoder_ix], s_int[encoder_ix],
						   sb_int[encoder_ix]);
				}

				encoder_ix++;

				if (need_padded_cell == true) {

					// make extra encoder cell
					// y_ix at y0, rest 0

					std::string enc_name = "br_enc_pad" + std::to_string(encoder_ix) + "_";

					std::string two_name = "two_int" + std::to_string(encoder_ix);
					two_int.push_back(module->addWire(new_id(two_name, __LINE__, ""), 1));

					std::string one_name = "one_int" + std::to_string(encoder_ix);
					one_int.push_back(module->addWire(new_id(two_name, __LINE__, ""), 1));

					std::string s_name = "s_int" + std::to_string(encoder_ix);
					s_int.push_back(module->addWire(new_id(s_name, __LINE__, ""), 1));

					std::string sb_name = "sb_int" + std::to_string(encoder_ix);
					sb_int.push_back(module->addWire(new_id(sb_name, __LINE__, ""), 1));

					RTLIL::Wire *one_o_int, *two_o_int, *s_o_int, *sb_o_int;
					BuildBur4e(enc_name, mk_wireFromSigSpec(SigSpec(Y, y_ix, 1)), mk_wireFromSigSpec(State::S0),
						   mk_wireFromSigSpec(State::S0), one_o_int, two_o_int, s_o_int, sb_o_int);

					join_wires_with_buffer(one_o_int, one_int[encoder_ix]);
					join_wires_with_buffer(two_o_int, two_int[encoder_ix]);
					join_wires_with_buffer(s_o_int, s_int[encoder_ix]);
					join_wires_with_buffer(sb_o_int, sb_int[encoder_ix]);
					y_ix++;
					encoder_ix++;
				}
			}
		}
	}

	/*
	  Signed Multiplier
	*/
	void CreateBoothSMult(RTLIL::Module *module, int x_sz, int y_sz, int z_sz, RTLIL::Wire *X, RTLIL::Wire *Y, RTLIL::Wire *Z)
	{ // product
		unsigned enc_count = (y_sz / 2) + (((y_sz % 2) != 0) ? 1 : 0);
		int dec_count = x_sz + 1;

		int fa_count = x_sz + 4;
		int fa_row_count = enc_count - 1;

		log("Signed multiplier generator using low Power Negative First Booth Algorithm. Multiplicand of size %d Multiplier of size %d. "
		    "Result of size %d. %d encoders %d decoders\n",
		    x_sz, y_sz, z_sz, enc_count, dec_count);

		RTLIL::Wire **negi_n_int = new RTLIL::Wire *[enc_count];
		RTLIL::Wire **twoi_n_int = new RTLIL::Wire *[enc_count];
		RTLIL::Wire **onei_n_int = new RTLIL::Wire *[enc_count];
		RTLIL::Wire **cori_n_int = new RTLIL::Wire *[enc_count];

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

				BuildBr4e(enc_name, mk_wireFromSigSpec(SigSpec(State::S0)), mk_wireFromSigSpec(SigSpec(Y, 0, 1)),
					  mk_wireFromSigSpec(SigSpec(Y, 1, 1)),

					  negi_n_int[encoder_ix - 1], twoi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  cori_n_int[encoder_ix - 1]);

			} else {
				RTLIL::Wire *y1_wire;
				RTLIL::Wire *y2_wire;
				RTLIL::Wire *y3_wire;

				y1_wire = mk_wireFromSigSpec(SigSpec(Y, ((encoder_ix - 1) * 2 - 1), 1)); //-1
				if ((encoder_ix - 1) * 2 >= (unsigned)y_sz)
					y2_wire = mk_wireFromSigSpec(SigSpec(State::S0)); // constant 0
				else
					y2_wire = mk_wireFromSigSpec(SigSpec(Y, ((encoder_ix - 1) * 2), 1)); // 0

				if (((encoder_ix - 1) * 2 + 1) >= (unsigned)y_sz)
					y3_wire = mk_wireFromSigSpec(SigSpec(State::S0)); // constant 0
				else
					y3_wire = mk_wireFromSigSpec(SigSpec(Y, ((encoder_ix - 1) * 2 + 1), 1)); //+1

				BuildBr4e(enc_name, y1_wire, y2_wire, y3_wire,

					  negi_n_int[encoder_ix - 1], twoi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  cori_n_int[encoder_ix - 1]);
			}
		}

		// Decoders and PP generation
		RTLIL::Wire **PPij = new RTLIL::Wire *[enc_count * dec_count];
		RTLIL::Wire **nxj = new RTLIL::Wire *[enc_count * dec_count];

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
					  mk_wireFromSigSpec(SigSpec(X, decoder_ix - 1, 1)), negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  PPij[((encoder_ix - 1) * dec_count) + decoder_ix - 1], nxj[((encoder_ix - 1) * dec_count) + decoder_ix]);
			}

			// duplicate end for sign fix
			// applies to 9th decoder (xsz+1 decoder).
			std::string dec_name = "dec_" + std::to_string(encoder_ix) + "_" + std::to_string(x_sz + 1) + "_";
			RTLIL::Wire *unused_op = nullptr;
			BuildBr4d(dec_name, nxj[((encoder_ix - 1) * dec_count) + dec_count - 1], twoi_n_int[encoder_ix - 1],
				  mk_wireFromSigSpec(SigSpec(X, dec_count - 2, 1)), negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
				  PPij[((encoder_ix - 1) * dec_count) + dec_count - 1], unused_op);
		}

		//
		// sum up the partial products
		//
		int fa_el_ix = 0;
		int fa_row_ix = 0;
		// use 1 d arrays (2d cannot have variable sized indices)
		RTLIL::Wire **fa_sum_n = new RTLIL::Wire *[fa_row_count * fa_count];
		RTLIL::Wire **fa_carry_n = new RTLIL::Wire *[fa_row_count * fa_count];

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
		RTLIL::Wire *cpa_carry[z_sz];

		for (int cix = 0; cix < z_sz; cix++) {
			std::string cpa_cix_name = "cpa_carry_" + std::to_string(cix) + "_";
			cpa_carry[cix] = module->addWire(new_id(cpa_cix_name, __LINE__, ""), 1);
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
				buf->setPort(ID::Y, SigSpec(Z, cpa_ix, 1));

				cpa_ix++;
				buf_name = "pp_buf_" + std::to_string(cpa_ix) + "_" + "driven_by_fa_row_" + std::to_string(fa_row_ix) + "_";
				buf = module->addCell(new_id(buf_name, __LINE__, ""), ID($pos));
				buf->setPort(ID::A, fa_sum_n[(fa_row_ix * fa_count) + 1]);
				buf->setParam(ID::A_WIDTH, 1);
				buf->setParam(ID::Y_WIDTH, 1);
				buf->setParam(ID::A_SIGNED, true);
				buf->setPort(ID::Y, SigSpec(Z, cpa_ix, 1));
			} else {
				int offset = fa_row_count * 2;
				bool base_case = cpa_ix - offset == 0 ? true : false;
				std::string cpa_name = "cpa_" + std::to_string(cpa_ix - offset) + "_";

				RTLIL::Wire *ci_wire;
				if (base_case)
					ci_wire = cori_n_int[enc_count - 1];
				else
					ci_wire = cpa_carry[cpa_ix - offset - 1];

				RTLIL::Wire *op_wire = module->addWire(NEW_ID, 1);
				BuildHa(cpa_name, fa_sum_n[(fa_row_count - 1) * fa_count + cpa_ix - offset + 2], ci_wire, op_wire,
					cpa_carry[cpa_ix - offset]);
				module->connect(op_wire, SigSpec(Z, cpa_ix, 1));
			}
		}

		//
		// instantiate the quadrant 1 cell. This is the upper right
		// quadrant which can be realized using non-booth encoded logic.
		//
		std::string q1_name = "icb_booth_q1_";

		RTLIL::Wire *pp0_o_int;
		RTLIL::Wire *pp1_o_int;
		RTLIL::Wire *nxj_o_int;
		RTLIL::Wire *cor_o_int;

		BuildBoothQ1(q1_name,
			     negi_n_int[0], // negi
			     cori_n_int[0], // cori

			     mk_wireFromSigSpec(SigSpec(X, 0, 1)), // x0
			     mk_wireFromSigSpec(SigSpec(X, 1, 1)), // x1
			     mk_wireFromSigSpec(SigSpec(Y, 0, 1)), // y0
			     mk_wireFromSigSpec(SigSpec(Y, 1, 1)), // y1

			     nxj_o_int, cor_o_int, pp0_o_int, pp1_o_int);

		join_wires_with_buffer(pp0_o_int, fa_sum_n[(0 * fa_count) + 0]);
		join_wires_with_buffer(pp1_o_int, fa_sum_n[(0 * fa_count) + 1]);
		join_wires_with_buffer(cor_o_int, fa_carry_n[(0 * fa_count) + 1]);
		join_wires_with_buffer(nxj_o_int, nxj[(0 * dec_count) + 2]);

		delete[] negi_n_int;
		delete[] twoi_n_int;
		delete[] onei_n_int;
		delete[] cori_n_int;

		delete[] fa_sum_n;
		delete[] fa_carry_n;
	}
};

struct MultPass : public Pass {
	MultPass() : Pass("booth", "Map $mul to booth multipliers") {}
	void execute(vector<string> args, RTLIL::Design *design) override
	{
		(void)args;
		log_header(design, "Executing multpass. Generating Booth Multiplier structures for signed/unsigned multipliers of 4 bits or more\n");
		for (auto mod : design->selected_modules())
			if (!mod->has_processes_warn()) {
				MultPassWorker worker(mod);
				worker.run();
				log_header(design, "Created %d booth multipliers.\n", worker.booth_counter);
			}
	}
} MultPass;

PRIVATE_NAMESPACE_END
