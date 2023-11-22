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

//FIXME: These debug prints are broken now, should be fixed or removed.
//#define DEBUG_CPA

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BoothPassWorker {

	RTLIL::Module *module;
	SigMap sigmap;
	int booth_counter;
	bool lowpower = false;
	bool mapped_cpa = false;

	BoothPassWorker(RTLIL::Module *module) : module(module), sigmap(module) { booth_counter = 0; }

	// Booth unsigned decoder lsb
	SigBit Bur4d_lsb(std::string name, SigBit lsb_i, SigBit one_i, SigBit s_i)
	{
		SigBit and_op = module->AndGate(NEW_ID_SUFFIX(name), lsb_i, one_i);
		return module->XorGate(NEW_ID_SUFFIX(name), and_op, s_i);
	}

	// Booth unsigned radix4 decoder
	SigBit Bur4d_n(std::string name, SigBit yn_i, SigBit ynm1_i, SigBit one_i, SigBit two_i, SigBit s_i)
	{
		// ppij = ((yn & one)   | (ynm1 & two)) ^ s;
		SigBit an1 = module->AndGate(NEW_ID_SUFFIX(name), yn_i, one_i);
		SigBit an2 = module->AndGate(NEW_ID_SUFFIX(name), ynm1_i, two_i);
		SigBit or1 = module->OrGate(NEW_ID_SUFFIX(name), an1, an2);
		return module->XorGate(NEW_ID_SUFFIX(name), s_i, or1);
	}

	// Booth unsigned radix4 decoder
	SigBit Bur4d_msb(std::string name, SigBit msb_i, SigBit two_i, SigBit s_i)
	{
		// ppij = (msb & two)  ^ s;
		SigBit an1 = module->AndGate(NEW_ID_SUFFIX(name), msb_i, two_i);
		return module->XorGate(NEW_ID_SUFFIX(name), s_i, an1);
	}

	// half adder, used in CPA
	void BuildHa(std::string name, SigBit a_i, SigBit b_i, SigBit &s_o, SigBit &c_o)
	{
		s_o = module->XorGate(NEW_ID_SUFFIX(name), a_i, b_i);
		c_o = module->AndGate(NEW_ID_SUFFIX(name), a_i, b_i);
	}

	// Booth unsigned radix 4 encoder
	void BuildBur4e(std::string name, SigBit y0_i, SigBit y1_i, SigBit y2_i,
			SigBit &one_o, SigBit &two_o, SigBit &s_o, SigBit &sb_o)
	{
		one_o = module->XorGate(NEW_ID_SUFFIX(name), y0_i, y1_i);
		s_o = y2_i;
		sb_o = module->NotGate(NEW_ID_SUFFIX(name), y2_i);
		SigBit y1_xnor_y2 = module->XnorGate(NEW_ID_SUFFIX(name), y1_i, y2_i);
		two_o = module->NorGate(NEW_ID_SUFFIX(name), y1_xnor_y2, one_o);
	}

	void BuildBr4e(std::string name, SigBit y2_m1_i,
		       SigBit y2_i, // y2i
		       SigBit y2_p1_i,
		       SigBit &negi_o, SigBit &twoi_n_o, SigBit &onei_n_o, SigBit &cori_o)
	{
		auto y2_p1_n = module->NotGate(NEW_ID_SUFFIX(name), y2_p1_i);
		auto y2_n = module->NotGate(NEW_ID_SUFFIX(name), y2_i);
		auto y2_m1_n = module->NotGate(NEW_ID_SUFFIX(name), y2_m1_i);

		negi_o = y2_p1_i;

		// twoi_n = ~(
		//    (y2_p1_n & y2_i & y2_m1_i) |
		//    (y2_p1 & y2_n & y2_m1_n)
		// )
		twoi_n_o = module->NorGate(NEW_ID_SUFFIX(name),
			module->AndGate(NEW_ID_SUFFIX(name), y2_p1_n, module->AndGate(NEW_ID_SUFFIX(name), y2_i, y2_m1_i)),
			module->AndGate(NEW_ID_SUFFIX(name), y2_p1_i, module->AndGate(NEW_ID_SUFFIX(name), y2_n, y2_m1_n))
		);

		// onei_n = ~(y2_m1_i ^ y2_i);
		onei_n_o = module->XnorGate(NEW_ID_SUFFIX(name), y2_m1_i, y2_i);
		// cori = (y2_m1_n | y2_n) & y2_p1_i;
		cori_o = module->AndGate(NEW_ID_SUFFIX(name), module->OrGate(NEW_ID_SUFFIX(name), y2_m1_n, y2_n), y2_p1_i);
	}

	//
	// signed booth radix 4 decoder
	//
	void BuildBr4d(std::string name, SigBit nxj_m1_i, SigBit twoi_n_i, SigBit xj_i, SigBit negi_i, SigBit onei_n_i,
		       SigBit &ppij_o, SigBit &nxj_o)
	{
		// nxj_in = xnor(xj,negi)
		// nxj_o = xnj_in,
		// ppij = ~( (nxj_m1_i | twoi_n_i) & (nxj_int | onei_n_i));
		nxj_o = module->XnorGate(NEW_ID_SUFFIX(name), xj_i, negi_i);
		ppij_o = module->NandGate(NEW_ID_SUFFIX(name),
			module->OrGate(NEW_ID_SUFFIX(name), nxj_m1_i, twoi_n_i),
			module->OrGate(NEW_ID_SUFFIX(name), nxj_o, onei_n_i)
		);
	}

	/*
	  In signed case 1st two bits best realised
	  using non-booth encoded logic. We can save a booth
	  encoder for the first couple of bits.
	*/
	void BuildBoothQ1(std::string name, SigBit negi_i, SigBit cori_i, SigBit x0_i, SigBit x1_i, SigBit y0_i,
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
		nxj_o = module->XnorGate(NEW_ID_SUFFIX(name), x1_i, negi_i);
		pp0_o = module->AndGate(NEW_ID_SUFFIX(name), x0_i, y0_i);
		SigBit pp1_1_int = module->AndGate(NEW_ID_SUFFIX(name), x1_i, y0_i);
		SigBit pp1_2_int = module->AndGate(NEW_ID_SUFFIX(name), x0_i, y1_i);
		pp1_o = module->XorGate(NEW_ID_SUFFIX(name), pp1_1_int, pp1_2_int);

		SigBit pp1_nor_pp0 = module->NorGate(NEW_ID_SUFFIX(name), pp1_o, pp0_o);
		cor_o = module->AndGate(NEW_ID_SUFFIX(name), pp1_nor_pp0, cori_i);
	}

	void BuildBitwiseFa(Module *mod, std::string name, const SigSpec &sig_a, const SigSpec &sig_b,
			    const SigSpec &sig_c, const SigSpec &sig_x, const SigSpec &sig_y,
			    const std::string &src = "")
	{
		// We can't emit a single wide full-adder cell here since
		// there would typically be feedback loops involving the cells'
		// input and output ports, and Yosys doesn't cope well with
		// those
		log_assert(sig_a.size() == sig_b.size());
		log_assert(sig_a.size() == sig_c.size());
		log_assert(sig_a.size() == sig_x.size());
		log_assert(sig_a.size() == sig_y.size());

		for (int i = 0; i < sig_a.size(); i++)
			mod->addFa(stringf("%s[%d]", name.c_str(), i), sig_a[i], sig_b[i],
				   sig_c[i], sig_x[i], sig_y[i], src);
	}

	void run()
	{
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($mul))
				continue;

			SigSpec A = cell->getPort(ID::A);
			SigSpec B = cell->getPort(ID::B);
			SigSpec Y = cell->getPort(ID::Y);
			int x_sz = GetSize(A), y_sz = GetSize(B), z_sz = GetSize(Y);

			if (x_sz < 4 || y_sz < 4 || z_sz < 8) {
				log_debug("Not mapping cell %s sized at %dx%x, %x: size below threshold\n",
					  log_id(cell), x_sz, y_sz, z_sz);
				continue;
			}

			log_assert(cell->getParam(ID::A_SIGNED).as_bool() == cell->getParam(ID::B_SIGNED).as_bool());
			bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();

			log("Mapping cell %s to %s Booth multiplier\n", log_id(cell), is_signed ? "signed" : "unsigned");

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
					} else {
						x_sz_revised = y_sz;
					}		
				} else {
					if (x_sz % 2 != 0) {
						y_sz_revised = x_sz + 1;
						x_sz_revised = x_sz + 1;
					} else {
						y_sz_revised = x_sz;
					}
				}
			} else {
				if (x_sz % 2 != 0) {
					y_sz_revised = y_sz + 1;
					x_sz_revised = x_sz + 1;
				}
			}

			log_assert((x_sz_revised == y_sz_revised) && (x_sz_revised % 2 == 0) && (y_sz_revised % 2 == 0));


			A.extend_u0(x_sz_revised, is_signed);
			B.extend_u0(y_sz_revised, is_signed);

			// Make sure output domain is big enough to take
			// all combinations.
			// Later logic synthesis will kill unused
			// portions of the output domain.

			int required_op_size = x_sz_revised + y_sz_revised;

			if (required_op_size != z_sz) {
				SigSpec expanded_Y = module->addWire(NEW_ID, required_op_size);
				SigSpec Y_driver = expanded_Y;
				Y_driver.extend_u0(Y.size(), is_signed);
				module->connect(Y, Y_driver);
				Y = expanded_Y;
			}
			log_assert(GetSize(Y) == required_op_size);

			if (!lowpower)
				CreateBoothMult(module,
					A, // multiplicand
					B, // multiplier(scanned)
					Y, // result
					is_signed
				);
			else
				CreateBoothLowpowerMult(module,
					A, // multiplicand
					B, // multiplier(scanned)
					Y, // result
					is_signed
				);

			module->remove(cell);
			booth_counter++;
		}
	}

	SigSig WallaceSum(int width, std::vector<SigSpec> summands)
	{
		for (auto &s : summands)
			s.extend_u0(width);

		while (summands.size() > 2) {
			std::vector<SigSpec> new_summands;
			int i;
			for (i = 0; i < (int) summands.size() - 2; i += 3) {
				SigSpec x = module->addWire(NEW_ID, width);
				SigSpec y = module->addWire(NEW_ID, width);
				BuildBitwiseFa(module, NEW_ID.str(), summands[i], summands[i + 1],
					       summands[i + 2], x, y);
				new_summands.push_back(y);
				new_summands.push_back({x.extract(0, width - 1), State::S0});
			}

			new_summands.insert(new_summands.begin(), summands.begin() + i, summands.end());

			std::swap(summands, new_summands);
		}

		if (!summands.size())
			return SigSig(SigSpec(width, State::S0), SigSpec(width, State::S0));
		else if (summands.size() == 1)
			return SigSig(summands[0], SigSpec(width, State::S0));
		else
			return SigSig(summands[0], summands[1]);
	}

	/*
	  Build Multiplier.
	  -------------------------
	  Uses a generic booth multiplier
	*/

	void CreateBoothMult(RTLIL::Module *module,
			      SigSpec X, // multiplicand
			      SigSpec Y, // multiplier
			      SigSpec Z,
			      bool is_signed)
	{ // result
		int z_sz = Z.size();

		SigSpec one_int, two_int, s_int, sb_int;
		int encoder_count = 0;

		BuildBoothMultEncoders(Y, one_int, two_int, s_int, sb_int, module, encoder_count, is_signed);

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
		BuildBoothMultDecoderRow0(module, X, s_int, sb_int, one_int, two_int, ppij_row_0, is_signed);

		// data, shift, sign
		ppij_int.push_back(std::make_tuple(ppij_row_0, 0, s_int[0]));

		for (int i = 1; i < encoder_count; i++) {
			// format 1,S.Data.shift = encoder_ix*2,sign = sb_int[i]
			SigSpec ppij_row_n;

			BuildBoothMultDecoderRowN(module,
						   X, // multiplicand
						   one_int[i], two_int[i], s_int[i], sb_int[i], ppij_row_n, i,
						   is_signed
			);
			// data, shift, sign
			ppij_int.push_back(std::make_tuple(ppij_row_n, i * 2, s_int[i]));
		}


		//  Debug dump out partial products
		//  DebugDumpPP(ppij_int);

		// Summation of Partial Products (Wallace Tree)
		std::vector<SigSpec> aligned_pp;
		aligned_pp.resize(encoder_count + 1); // make an entirely redundant row
		// just for sign bit in lsb. (We then filter this out).

		// resize all to be same size as z
		for (int i = 0; i < encoder_count + 1; i++)
			aligned_pp[i].extend_u0(z_sz);

		AlignPP(z_sz, ppij_int, aligned_pp);

		// Debug: dump out aligned partial products.
		// Later on yosys will clean up unused constants
		//  DebugDumpAlignPP(aligned_pp);

		SigSig wtree_sum = WallaceSum(z_sz, aligned_pp);

		// Debug code: Dump out the csa trees
		// DumpCSATrees(debug_csa_trees);
		// Build the CPA to do the final accumulation.
		log_assert(wtree_sum.second[0] == State::S0);
		if (mapped_cpa)
			BuildCPA(module, wtree_sum.first, {State::S0, wtree_sum.second.extract_end(1)}, Z);
		else
			module->addAdd(NEW_ID, wtree_sum.first, {wtree_sum.second.extract_end(1), State::S0}, Z);
	}

	/*
	  Build Row 0 of decoders
	*/

	void BuildBoothMultDecoderRow0(RTLIL::Module *module,
					SigSpec X, // multiplicand
					SigSpec s_int, SigSpec sb_int, SigSpec one_int,
					SigSpec two_int, SigSpec &ppij_vec, bool is_signed)
	{
		(void)sb_int;
		(void)module;
		int x_sz = GetSize(X);
		SigBit ppij;

		// lsb
		ppij_vec.append(Bur4d_lsb("row0_lsb_dec", X[0], one_int[0], s_int[0]));

		// 1..xsize -1
		for (int i = 1; i < x_sz; i++)
			ppij_vec.append(Bur4d_n(stringf("row0_dec_%d", i), X[i], X[i - 1],
						one_int[0], two_int[0], s_int[0]));


		// The redundant bit. Duplicate decoding of last bit.
		if (!is_signed) {
			ppij_vec.append(Bur4d_msb("row0_dec_msb", X.msb(), two_int[0], s_int[0]));
		} else {
			ppij_vec.append(Bur4d_n("row0_dec_msb", X.msb(), X.msb(),
										  one_int[0], two_int[0], s_int[0]));
		}

		// append the sign bits
		if (is_signed) {
			SigBit e = module->XorGate(NEW_ID, s_int[0], module->AndGate(NEW_ID, X.msb(), module->OrGate(NEW_ID, two_int[0], one_int[0])));
			ppij_vec.append({module->NotGate(NEW_ID, e), e, e});
		} else {
			// append the sign bits
			ppij_vec.append({module->NotGate(NEW_ID, s_int[0]), s_int[0], s_int[0]});
		}
	}

	// Build a generic row of decoders.

	void BuildBoothMultDecoderRowN(RTLIL::Module *module,
					SigSpec X, // multiplicand
					SigSpec one_int, SigSpec two_int, SigSpec s_int, SigSpec sb_int,
					SigSpec &ppij_vec, int row_ix,
					bool is_signed)
	{
		(void)module;
		int x_sz = GetSize(X);

		// lsb
		ppij_vec.append(Bur4d_lsb(stringf("row_%d_lsb_dec", row_ix), X[0], one_int, s_int));

		// core bits
		for (int i = 1; i < x_sz; i++)
			ppij_vec.append(Bur4d_n(stringf("row_%d_dec_%d", row_ix, i), X[i], X[i - 1],
				     		one_int, two_int, s_int));

		if (!is_signed) {			// redundant bit
			ppij_vec.append(Bur4d_msb("row_dec_red", X[x_sz - 1], two_int, s_int));
		} else {
			ppij_vec.append(Bur4d_n(stringf("row_%d_dec_msb", row_ix), X[x_sz - 1], X[x_sz - 1],
				     					one_int, two_int, s_int));
		}

		ppij_vec.append(!is_signed ? sb_int[0] : module->XorGate(NEW_ID, sb_int, module->AndGate(NEW_ID, X.msb(), module->OrGate(NEW_ID, two_int, one_int))));
		ppij_vec.append(State::S1);
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
				if (bits_to_reduce[row_ix][column_ix] != State::S0)
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
	void AlignPP(int z_sz, std::vector<std::tuple<SigSpec, int, SigBit>> &ppij_int,
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
			int prior_row_idx = get<1>(ppij_int[aligned_pp_ix - 1]);
			SigBit prior_row_sign = get<2>(ppij_int[aligned_pp_ix - 1]);
			if (prior_row_idx < z_sz)
				aligned_pp[aligned_pp_ix][prior_row_idx] = prior_row_sign;
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
		log_assert(result.size() == s_vec.size());

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
				SigBit carry_out = module->addWire(NEW_ID, 1);
				module->addFa(NEW_ID_SUFFIX(stringf("cpa_%d_fa_%d", cpa_id, n)),
					/* A */ s_vec[n],
					/* B */ c_vec[n - 1],
					/* C */ carry,
					/* X */ carry_out,
					/* Y */ result[n]
				);
				carry = carry_out;

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
				SigBit carry_out = module->addWire(NEW_ID_SUFFIX(stringf("cpa_%d_carry_%d", cpa_id, n)), 1);
				module->addFa(NEW_ID_SUFFIX(stringf("cpa_%d_fa_%d", cpa_id, n)),
					/* A */ s_vec[n],
					/* B */ c_vec[n - 1],
					/* C */ carry,
					/* X */ carry_out,
					/* Y */ result[n]
				);
				carry = carry_out;
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

		if (column_size > 0) {
			int var_ix = 0;
			SigSpec first_csa_ips;
			// get the first 3 inputs, if possible
			for (var_ix = 0; var_ix < column_bits.size() && first_csa_ips.size() != 3; var_ix++) {
				if (column_bits[var_ix] != State::S0)
					first_csa_ips.append(column_bits[var_ix]);
			}

			if (first_csa_ips.size() > 0) {
				// build the first csa
				auto s_wire = module->addWire(NEW_ID_SUFFIX(stringf("csa_%d_%d_s", column_ix, csa_ix + 1)), 1);
				auto c_wire = module->addWire(NEW_ID_SUFFIX(stringf("csa_%d_%d_c", column_ix, csa_ix + 1)), 1);

				auto csa = module->addFa(NEW_ID_SUFFIX(stringf("csa_%d_%d", column_ix, csa_ix)),
					/* A */ first_csa_ips[0],
					/* B */ first_csa_ips.size() > 1 ? first_csa_ips[1] : State::S0,
					/* C */ first_csa_ips.size() > 2 ? first_csa_ips[2] : State::S0,
					/* X */ c_wire,
					/* Y */ s_wire
				);

				s_result = s_wire;
				c_result = c_wire;

				debug_csa_trees[column_ix].push_back(csa);
				csa_ix++;				

				if (var_ix <= column_bits.size() - 1)
					carry_bits_to_sum.append(c_wire);

				// Now build the rest of the tree if we can
				while (var_ix <= column_bits.size() - 1) {
					SigSpec csa_ips;
					// get the next two variables to sum
					for (; var_ix <= column_bits.size() - 1 && csa_ips.size() < 2;) {
						// skip any empty bits
						if (column_bits[var_ix] != State::S0)
							csa_ips.append(column_bits[var_ix]);
						var_ix++;
					}

					if (csa_ips.size() > 0) {
						auto c_wire = module->addWire(NEW_ID_SUFFIX(stringf("csa_%d_%d_c", column_ix, csa_ix + 1)), 1);
						auto s_wire = module->addWire(NEW_ID_SUFFIX(stringf("csa_%d_%d_s", column_ix, csa_ix + 1)), 1);

						auto csa = module->addFa(NEW_ID_SUFFIX(stringf("csa_%d_%d", column_ix, csa_ix)),
							/* A */ s_result,
							/* B */ csa_ips[0],
							/* C */ csa_ips.size() > 1 ? csa_ips[1] : State::S0,
							/* X */ c_wire,
							/* Y */ s_wire
						);

						debug_csa_trees[column_ix].push_back(csa);
						csa_ix++;

						if (var_ix <= column_bits.size() - 1)
							carry_bits_to_sum.append(c_wire);

						s_result = s_wire;
						c_result = c_wire;
					}
				}
			}
		}
	}

	void BuildBoothMultEncoders(SigSpec Y, SigSpec &one_int, SigSpec &two_int,
				     SigSpec &s_int, SigSpec &sb_int, RTLIL::Module *module, int &encoder_ix, bool is_signed)
	{
		int y_sz = GetSize(Y);

		for (int y_ix = 0; y_ix < (!is_signed ? y_sz : y_sz - 1);) {
			std::string enc_name = stringf("bur_enc_%d", encoder_ix);

			two_int.append(module->addWire(NEW_ID_SUFFIX(stringf("two_int_%d", encoder_ix)), 1));
			one_int.append(module->addWire(NEW_ID_SUFFIX(stringf("one_int_%d", encoder_ix)), 1));
			s_int.append(module->addWire(NEW_ID_SUFFIX(stringf("s_int_%d", encoder_ix)), 1));
			sb_int.append(module->addWire(NEW_ID_SUFFIX(stringf("sb_int_%d", encoder_ix)), 1));

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
					y0 = is_signed ? Y.msb() : State::S0;
					need_padded_cell = false;
				} else {
					y0 = Y[y_ix];
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y1 = is_signed ? Y.msb() : State::S0;
				} else {
					y1 = Y[y_ix];
					y_ix++;
				}

				if (y_ix > y_sz - 1) {
					need_padded_cell = false;
					y2 = is_signed ? Y.msb() : State::S0;
				} else {
					if (y_ix == y_sz - 1)
						need_padded_cell = !is_signed;
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

					std::string enc_name = stringf("br_enc_pad_%d", encoder_ix);

					two_int.append(module->addWire(NEW_ID_SUFFIX(stringf("two_int_%d", encoder_ix)), 1));
					one_int.append(module->addWire(NEW_ID_SUFFIX(stringf("one_int_%d", encoder_ix)), 1));
					s_int.append(module->addWire(NEW_ID_SUFFIX(stringf("s_int_%d", encoder_ix)), 1));
					sb_int.append(module->addWire(NEW_ID_SUFFIX(stringf("sb_int_%d", encoder_ix)), 1));

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
	  Low-power Multiplier
	*/
	void CreateBoothLowpowerMult(RTLIL::Module *module, SigSpec X, SigSpec Y, SigSpec Z, bool is_signed)
	{ // product
		int x_sz = X.size(), y_sz = Y.size(), z_sz = Z.size();

		if (!is_signed)
			log_error("Low-power Booth architecture is only supported on signed multipliers.\n");

		unsigned enc_count = (y_sz / 2) + (((y_sz % 2) != 0) ? 1 : 0);
		int dec_count = x_sz + 1;

		int fa_count = x_sz + 4;
		int fa_row_count = enc_count - 1;

		log_debug("Mapping %d x %d -> %d multiplier: %d encoders %d decoders\n", x_sz, y_sz, z_sz, enc_count, dec_count);

		SigSpec negi_n_int, twoi_n_int, onei_n_int, cori_n_int;

		negi_n_int.extend_u0(enc_count);
		twoi_n_int.extend_u0(enc_count);
		onei_n_int.extend_u0(enc_count);
		cori_n_int.extend_u0(enc_count);

		for (unsigned encoder_ix = 1; encoder_ix <= enc_count; encoder_ix++) {
			std::string enc_name = stringf("enc_%d", encoder_ix);
			negi_n_int[encoder_ix - 1] = module->addWire(NEW_ID_SUFFIX(stringf("negi_n_int_%d", encoder_ix)), 1);
			twoi_n_int[encoder_ix - 1] = module->addWire(NEW_ID_SUFFIX(stringf("twoi_n_int_%d", encoder_ix)), 1);
			onei_n_int[encoder_ix - 1] = module->addWire(NEW_ID_SUFFIX(stringf("onei_n_int_%d", encoder_ix)), 1);
			cori_n_int[encoder_ix - 1] = module->addWire(NEW_ID_SUFFIX(stringf("cori_n_int_%d", encoder_ix)), 1);

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
				PPij[((encoder_ix - 1) * dec_count) + decoder_ix - 1] =
					module->addWire(NEW_ID_SUFFIX(stringf("ppij_%d_%d", encoder_ix, decoder_ix)), 1);

				nxj[((encoder_ix - 1) * dec_count) + decoder_ix - 1] =
					module->addWire(NEW_ID_SUFFIX(stringf("nxj_%s%d_%d", decoder_ix == 1 ? "pre_dec_" : "",
									      encoder_ix, decoder_ix)), 1);
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
				module->addNotGate(NEW_ID_SUFFIX(stringf("pre_dec_%d", encoder_ix)),
					negi_n_int[encoder_ix - 1],
					nxj[(encoder_ix - 1) * dec_count]
				);
			}

			for (int decoder_ix = 1; decoder_ix < dec_count; decoder_ix++) {
				// range 1..8

				// quadrant 1 optimization.
				if ((decoder_ix == 1 || decoder_ix == 2) && encoder_ix == 1)
					continue;

				std::string dec_name = stringf("dec_%d_%d", encoder_ix, decoder_ix);
				BuildBr4d(dec_name, nxj[((encoder_ix - 1) * dec_count) + decoder_ix - 1], twoi_n_int[encoder_ix - 1],
					  X[decoder_ix - 1], negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
					  PPij[((encoder_ix - 1) * dec_count) + decoder_ix - 1], nxj[((encoder_ix - 1) * dec_count) + decoder_ix]);
			}

			// duplicate end for sign fix
			// applies to 9th decoder (xsz+1 decoder).
			std::string dec_name = stringf("dec_%d_%d", encoder_ix, x_sz + 1);
			SigBit unused_op;
			BuildBr4d(dec_name, nxj[((encoder_ix - 1) * dec_count) + dec_count - 1], twoi_n_int[encoder_ix - 1],
				  X[dec_count - 2], negi_n_int[encoder_ix - 1], onei_n_int[encoder_ix - 1],
				  PPij[((encoder_ix - 1) * dec_count) + dec_count - 1], unused_op);
		}

		//
		// instantiate the quadrant 1 cell. This is the upper right
		// quadrant which can be realized using non-booth encoded logic.
		//
		SigBit pp0_o_int, pp1_o_int, nxj_o_int, q1_carry_out;

		BuildBoothQ1("icb_booth_q1_",
			     negi_n_int[0], // negi
			     cori_n_int[0], // cori
			     X[0], X[1], Y[0], Y[1],
			     nxj_o_int, q1_carry_out, pp0_o_int, pp1_o_int);

		module->connect(Z[0], pp0_o_int);
		module->connect(Z[1], pp1_o_int);
		module->connect(nxj[(0 * dec_count) + 2], nxj_o_int);

		//
		// sum up the partial products
		//
		int fa_row_ix = 0;
		std::vector<SigSpec> fa_sum;
		std::vector<SigSpec> fa_carry;

		for (fa_row_ix = 0; fa_row_ix < fa_row_count; fa_row_ix++) {
			fa_sum.push_back(module->addWire(NEW_ID_SUFFIX(stringf("fa_sum_%d", fa_row_ix)), fa_count));
			fa_carry.push_back(module->addWire(NEW_ID_SUFFIX(stringf("fa_carry_%d", fa_row_ix)), fa_count));
		}

		// full adder creation
		// base case: 1st row: Inputs from decoders
		// 1st row exception: two localized inverters due to sign extension structure
		SigBit d08_inv = module->NotGate(NEW_ID_SUFFIX("bfa_0_exc_inv1"), PPij[(0 * dec_count) + dec_count - 1]);
		SigBit d18_inv = module->NotGate(NEW_ID_SUFFIX("bfa_0_exc_inv2"), PPij[(1 * dec_count) + dec_count - 1]);
		BuildBitwiseFa(module, NEW_ID_SUFFIX("fa_row_0").str(),
			/* A */ {State::S0, d08_inv, PPij[(0 * dec_count) + x_sz], PPij.extract((0 * dec_count) + 2, x_sz - 1)},
			/* B */ {State::S1, d18_inv, PPij.extract((1 * dec_count), x_sz)},
			/* C */ fa_carry[0].extract(1, x_sz + 2),
			/* X */ fa_carry[0].extract(2, x_sz + 2),
			/* Y */ fa_sum[0].extract(2, x_sz + 2)
		);
		module->connect(fa_carry[0][1], q1_carry_out);

		// step case: 2nd and rest of rows. (fa_row_ix == 1...n)
		// special because these are driven by a decoder and prior fa.
		for (fa_row_ix = 1; fa_row_ix < fa_row_count; fa_row_ix++) {
			// end two bits: sign extension
			SigBit d_inv = module->NotGate(NEW_ID_SUFFIX(stringf("bfa_se_inv_%d_L", fa_row_ix)),
						       PPij[((fa_row_ix + 1) * dec_count) + dec_count - 1]);

			BuildBitwiseFa(module, NEW_ID_SUFFIX(stringf("fa_row_%d", fa_row_ix)).str(),
				/* A */	{State::S0, fa_carry[fa_row_ix - 1][fa_count - 1], fa_sum[fa_row_ix - 1].extract(2, x_sz + 2)},
				/* B */ {State::S1, d_inv, PPij.extract((fa_row_ix + 1) * dec_count, x_sz), State::S0, State::S0},

				/* C */ {fa_carry[fa_row_ix].extract(0, x_sz + 3), cori_n_int[fa_row_ix]},
				/* X */ fa_carry[fa_row_ix],
				/* Y */ fa_sum[fa_row_ix]
			);
		}

		// instantiate the cpa
		SigSpec cpa_carry;
		if (z_sz > fa_row_count * 2)
			cpa_carry = module->addWire(NEW_ID_SUFFIX("cpa_carry"), z_sz - fa_row_count * 2);

		// The end case where we pass the last two summands
		// from prior row directly to product output
		// without using a cpa cell. This is always
		// 0,1 index of prior fa row
		for (int cpa_ix = 0; cpa_ix < fa_row_count * 2; cpa_ix += 2) {
			int fa_row_ix = cpa_ix / 2;
			module->connect(Z.extract(cpa_ix, 2), fa_sum[fa_row_ix].extract(0, 2));
		}

		for (int cpa_ix = fa_row_count * 2; cpa_ix < z_sz; cpa_ix++) {
			int offset = fa_row_count * 2;
			std::string cpa_name = stringf("cpa_%d", cpa_ix - offset);

			SigBit ci = (cpa_ix == offset) ? cori_n_int[enc_count - 1] : cpa_carry[cpa_ix - offset - 1];
			SigBit op;
			BuildHa(cpa_name, fa_sum[fa_row_count - 1][cpa_ix - offset + 2], ci, op, cpa_carry[cpa_ix - offset]);
			module->connect(Z[cpa_ix], op);
		}
	}
};

struct BoothPass : public Pass {
	BoothPass() : Pass("booth", "map $mul cells to Booth multipliers") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    booth [selection]\n");
		log("\n");
		log("This pass replaces multiplier cells with a radix-4 Booth-encoded implementation.\n");
		log("It operates on $mul cells whose width of operands is at least 4x4 and whose\n");
		log("width of result is at least 8.\n");
		log("\n");
		log("    -lowpower\n");
		log("        use an alternative low-power architecture for the generated multiplier\n");
		log("        (signed multipliers only)\n");
		log("\n");
	}
	void execute(vector<string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BOOTH pass (map to Booth multipliers).\n");

		size_t argidx;
		bool mapped_cpa = false;
		bool lowpower = false;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-mapped_cpa")
				// Have an undocumented option which helps with multiplier
				// verification using specialized tools (AMulet2 in particular)
				mapped_cpa = true;
			else if (args[argidx] == "-lowpower")
				lowpower = true;
			else
				break;
		}
		extra_args(args, argidx, design);

		int total = 0;

		for (auto mod : design->selected_modules()) {
			if (!mod->has_processes_warn()) {
				BoothPassWorker worker(mod);
				worker.mapped_cpa = mapped_cpa;
				worker.lowpower = lowpower;
				worker.run();
				total += worker.booth_counter;
			}
		}

		log("Mapped %d multipliers.\n", total);
	}
} MultPass;

PRIVATE_NAMESPACE_END
