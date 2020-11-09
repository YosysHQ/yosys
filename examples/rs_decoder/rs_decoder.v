// -------------------------------------------------------------------------
//Reed-Solomon decoder
//Copyright (C) Wed May 22 09:59:27 2002
//by Ming-Han Lei(hendrik@humanistic.org)
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU Lesser General Public License
//as published by the Free Software Foundation; either version 2
//of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU Lesser General Public License for more details.
//
//You should have received a copy of the GNU Lesser General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
// --------------------------------------------------------------------------

module rs_decoder(x, error, with_error, enable, valid, k, clk, clrn);
	input enable, clk, clrn;
	input [4:0] k, x;
	output [4:0] error;
	wire [4:0] error;
	output with_error, valid;
	reg valid;
	wire with_error;

	wire [4:0] s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11;
	wire [4:0] lambda, omega, alpha;
	reg [3:0] count;
	reg [12:0] phase;
	wire [4:0] D0, D1, DI;
	//reg [4:0] D, D2;
	wire [4:0] D, D2;
	reg [4:0] u, length0, length2;
	wire [4:0] length1, length3;
	reg syn_enable, syn_init, syn_shift, berl_enable;
	reg chien_search, chien_load, shorten;

	always @ (chien_search or shorten)
		valid = chien_search & ~shorten;

	wire bit1;
	assign bit1 = syn_shift&phase[0];
	rsdec_syn x0 (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, u, syn_enable, bit1, syn_init, clk, clrn);
	rsdec_berl x1 (lambda, omega, s0, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, D0, D2, count, phase[0], phase[12], berl_enable, clk, clrn);
	rsdec_chien x2 (error, alpha, lambda, omega, D1, DI, chien_search, chien_load, shorten, clk, clrn);
	inverse x3 (DI, D);

	always @ (posedge clk)// or negedge clrn)
	begin
		if (~clrn)
		begin
			syn_enable <= 0;
			syn_shift <= 0;
			berl_enable <= 0;
			chien_search <= 1;
			chien_load <= 0;
			length0 <= 0;
			length2 <= 31 - k;
			count <= -1;
			phase <= 1;
			u <= 0;
			shorten <= 1;
			syn_init <= 0;
		end
		else
		begin
			if (enable & ~syn_enable & ~syn_shift)
			begin
				syn_enable <= 1;
				syn_init <= 1;
			end
			else if (syn_enable)
			begin
				length0 <= length1;
				syn_init <= 0;
				if (length1 == k)
				begin
					syn_enable <= 0;
					syn_shift <= 1;
					berl_enable <= 1;
				end
			end
			else if (berl_enable & with_error)
			begin
				if (phase[0])
				begin
					count <= count + 1;
					if (count == 11)
					begin
						syn_shift <= 0;
						length0 <= 0;
						chien_load <= 1;
						length2 <= length0;
					end
				end
				phase <= {phase[11:0], phase[12]};
			end
			else if (berl_enable & ~with_error)
				if (&count)
				begin
					syn_shift <= 0;
					length0 <= 0;
					berl_enable <= 0;
				end
				else
					phase <= {phase[11:0], phase[12]};
			else if (chien_load & phase[12])
			begin
				berl_enable <= 0;
				chien_load <= 0;
				chien_search <= 1;
				count <= -1;
				phase <= 1;
			end
			else if (chien_search)
			begin
				length2 <= length3;
				if (length3 == 0)
					chien_search <= 0;
			end
			else if (enable) u <= x;
			else if (shorten == 1 && length2 == 0)
				shorten <= 0;
		end
	end

//	always @ (chien_search or D0 or D1)
//		if (chien_search) D = D1;
//		else D = D0;
	assign D = chien_search ? D1 : D0;

//	always @ (DI or alpha or chien_load)
//		if (chien_load) D2 = alpha;
//		else D2 = DI;
	assign D2 = chien_load ? alpha : DI;

	assign length1 = length0 + 1;
	assign length3 = length2 - 1;
//	always @ (syn_shift or s0 or s1 or s2 or s3 or s4 or s5 or s6 or s7 or s8 or s9 or s10 or s11)
//		if (syn_shift && (s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11)!= 0)
//			with_error = 1;
//		else with_error = 0;
wire temp;
	assign temp = syn_shift && (s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11);
	assign with_error = temp != 0 ? 1'b1 : 1'b0;

endmodule

// -------------------------------------------------------------------------
//The inverse lookup table for Galois field
//Copyright (C) Tue Apr  2 17:21:59 2002
//by Ming-Han Lei(hendrik@humanistic.org)
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU Lesser General Public License
//as published by the Free Software Foundation; either version 2
//of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU Lesser General Public License for more details.
//
//You should have received a copy of the GNU Lesser General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
// --------------------------------------------------------------------------

module inverse(y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	case (x) // synopsys full_case parallel_case
		1: y = 1; // 0 -> 31
		2: y = 18; // 1 -> 30
		4: y = 9; // 2 -> 29
		8: y = 22; // 3 -> 28
		16: y = 11; // 4 -> 27
		5: y = 23; // 5 -> 26
		10: y = 25; // 6 -> 25
		20: y = 30; // 7 -> 24
		13: y = 15; // 8 -> 23
		26: y = 21; // 9 -> 22
		17: y = 24; // 10 -> 21
		7: y = 12; // 11 -> 20
		14: y = 6; // 12 -> 19
		28: y = 3; // 13 -> 18
		29: y = 19; // 14 -> 17
		31: y = 27; // 15 -> 16
		27: y = 31; // 16 -> 15
		19: y = 29; // 17 -> 14
		3: y = 28; // 18 -> 13
		6: y = 14; // 19 -> 12
		12: y = 7; // 20 -> 11
		24: y = 17; // 21 -> 10
		21: y = 26; // 22 -> 9
		15: y = 13; // 23 -> 8
		30: y = 20; // 24 -> 7
		25: y = 10; // 25 -> 6
		23: y = 5; // 26 -> 5
		11: y = 16; // 27 -> 4
		22: y = 8; // 28 -> 3
		9: y = 4; // 29 -> 2
		18: y = 2; // 30 -> 1
	endcase
endmodule

// -------------------------------------------------------------------------
//Berlekamp circuit for Reed-Solomon decoder
//Copyright (C) Tue Apr  2 17:21:42 2002
//by Ming-Han Lei(hendrik@humanistic.org)
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU Lesser General Public License
//as published by the Free Software Foundation; either version 2
//of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU Lesser General Public License for more details.
//
//You should have received a copy of the GNU Lesser General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
// --------------------------------------------------------------------------

module rsdec_berl (lambda_out, omega_out, syndrome0, syndrome1, syndrome2, syndrome3, syndrome4, syndrome5, syndrome6, syndrome7, syndrome8, syndrome9, syndrome10, syndrome11, 
		D, DI, count, phase0, phase12, enable, clk, clrn);
	input clk, clrn, enable, phase0, phase12;
	input [4:0] syndrome0;
	input [4:0] syndrome1;
	input [4:0] syndrome2;
	input [4:0] syndrome3;
	input [4:0] syndrome4;
	input [4:0] syndrome5;
	input [4:0] syndrome6;
	input [4:0] syndrome7;
	input [4:0] syndrome8;
	input [4:0] syndrome9;
	input [4:0] syndrome10;
	input [4:0] syndrome11;
	input [4:0] DI;
	input [3:0] count;
	output [4:0] lambda_out;
	output [4:0] omega_out;
	reg [4:0] lambda_out;
	reg [4:0] omega_out;
	output [4:0] D;
	reg [4:0] D;

	reg init, delta;
	reg [2:0] L;
	reg [4:0] lambda0;
	reg [4:0] lambda1;
	reg [4:0] lambda2;
	reg [4:0] lambda3;
	reg [4:0] lambda4;
	reg [4:0] lambda5;
	reg [4:0] lambda6;
	reg [4:0] lambda7;
	reg [4:0] lambda8;
	reg [4:0] lambda9;
	reg [4:0] lambda10;
	reg [4:0] lambda11;
	reg [4:0] B0;
	reg [4:0] B1;
	reg [4:0] B2;
	reg [4:0] B3;
	reg [4:0] B4;
	reg [4:0] B5;
	reg [4:0] B6;
	reg [4:0] B7;
	reg [4:0] B8;
	reg [4:0] B9;
	reg [4:0] B10;
	reg [4:0] omega0;
	reg [4:0] omega1;
	reg [4:0] omega2;
	reg [4:0] omega3;
	reg [4:0] omega4;
	reg [4:0] omega5;
	reg [4:0] omega6;
	reg [4:0] omega7;
	reg [4:0] omega8;
	reg [4:0] omega9;
	reg [4:0] omega10;
	reg [4:0] omega11;
	reg [4:0] A0;
	reg [4:0] A1;
	reg [4:0] A2;
	reg [4:0] A3;
	reg [4:0] A4;
	reg [4:0] A5;
	reg [4:0] A6;
	reg [4:0] A7;
	reg [4:0] A8;
	reg [4:0] A9;
	reg [4:0] A10;

	wire [4:0] tmp0;
	wire [4:0] tmp1;
	wire [4:0] tmp2;
	wire [4:0] tmp3;
	wire [4:0] tmp4;
	wire [4:0] tmp5;
	wire [4:0] tmp6;
	wire [4:0] tmp7;
	wire [4:0] tmp8;
	wire [4:0] tmp9;
	wire [4:0] tmp10;
	wire [4:0] tmp11;

	always @ (tmp1) lambda_out = tmp1;
	always @ (tmp3) omega_out = tmp3;

	always @ (L or D or count)
		// delta = (D != 0 && 2*L <= i);
		if (D != 0 && count >= {L, 1'b0}) delta = 1;
		else delta = 0;

	rsdec_berl_multiply x0 (tmp0, B10, D, lambda0, syndrome0, phase0);
	rsdec_berl_multiply x1 (tmp1, lambda11, DI, lambda1, syndrome1, phase0);
	rsdec_berl_multiply x2 (tmp2, A10, D, lambda2, syndrome2, phase0);
	rsdec_berl_multiply x3 (tmp3, omega11, DI, lambda3, syndrome3, phase0);
	multiply x4 (tmp4, lambda4, syndrome4);
	multiply x5 (tmp5, lambda5, syndrome5);
	multiply x6 (tmp6, lambda6, syndrome6);
	multiply x7 (tmp7, lambda7, syndrome7);
	multiply x8 (tmp8, lambda8, syndrome8);
	multiply x9 (tmp9, lambda9, syndrome9);
	multiply x10 (tmp10, lambda10, syndrome10);
	multiply x11 (tmp11, lambda11, syndrome11);

	always @ (posedge clk)// or negedge clrn)
	begin
		// for (j = t-1; j >=0; j--)
		//	if (j != 0) lambda[j] += D * B[j-1];
/*		if (~clrn)
		begin
			lambda0 <= 0;
			lambda1 <= 0;
			lambda2 <= 0;
			lambda3 <= 0;
			lambda4 <= 0;
			lambda5 <= 0;
			lambda6 <= 0;
			lambda7 <= 0;
			lambda8 <= 0;
			lambda9 <= 0;
			lambda10 <= 0;
			lambda11 <= 0;
			B0 <= 0;
			B1 <= 0;
			B2 <= 0;
			B3 <= 0;
			B4 <= 0;
			B5 <= 0;
			B6 <= 0;
			B7 <= 0;
			B8 <= 0;
			B9 <= 0;
			B10 <= 0;
			omega0 <= 0;
			omega1 <= 0;
			omega2 <= 0;
			omega3 <= 0;
			omega4 <= 0;
			omega5 <= 0;
			omega6 <= 0;
			omega7 <= 0;
			omega8 <= 0;
			omega9 <= 0;
			omega10 <= 0;
			omega11 <= 0;
			A0 <= 0;
			A1 <= 0;
			A2 <= 0;
			A3 <= 0;
			A4 <= 0;
			A5 <= 0;
			A6 <= 0;
			A7 <= 0;
			A8 <= 0;
			A9 <= 0;
			A10 <= 0;
//			for (j = 0; j < 12; j = j + 1) lambda[j] <= 0;
//			for (j = 0; j < 11; j = j + 1) B[j] <= 0;
//			for (j = 0; j < 12; j = j + 1) omega[j] <= 0;
//			for (j = 0; j < 11; j = j + 1) A[j] <= 0;
		end
		else*/ if (~enable)
		begin
			lambda0 <= 1;
			lambda1 <= 0;
			lambda2 <= 0;
			lambda3 <= 0;
			lambda4 <= 0;
			lambda5 <= 0;
			lambda6 <= 0;
			lambda7 <= 0;
			lambda8 <= 0;
			lambda9 <= 0;
			lambda10 <= 0;
			lambda11 <= 0;
			//for (j = 1; j < 12; j = j +1) lambda[j] <= 0;
			B0 <= 1;
			B1 <= 0;
			B2 <= 0;
			B3 <= 0;
			B4 <= 0;
			B5 <= 0;
			B6 <= 0;
			B7 <= 0;
			B8 <= 0;
			B9 <= 0;
			B10 <= 0;
			//for (j = 1; j < 11; j = j +1) B[j] <= 0;
			omega0 <= 1;
			omega1 <= 0;
			omega2 <= 0;
			omega3 <= 0;
			omega4 <= 0;
			omega5 <= 0;
			omega6 <= 0;
			omega7 <= 0;
			omega8 <= 0;
			omega9 <= 0;
			omega10 <= 0;
			omega11 <= 0;
			//for (j = 1; j < 12; j = j +1) omega[j] <= 0;
			A0 <= 0;
			A1 <= 0;
			A2 <= 0;
			A3 <= 0;
			A4 <= 0;
			A5 <= 0;
			A6 <= 0;
			A7 <= 0;
			A8 <= 0;
			A9 <= 0;
			A10 <= 0;
			//for (j = 0; j < 11; j = j + 1) A[j] <= 0;
		end
		else
		begin
			if (~phase0)
			begin
				if (~phase12) lambda0 <= lambda11 ^ tmp0;
				else lambda0 <= lambda11;
				//for (j = 1; j < 12; j = j + 1)
					//lambda[j] <= lambda[j-1];
				lambda1 <= lambda0;
				lambda2 <= lambda1;
				lambda3 <= lambda2;
				lambda4 <= lambda3;
				lambda5 <= lambda4;
				lambda6 <= lambda5;
				lambda7 <= lambda6;
				lambda8 <= lambda7;
				lambda9 <= lambda8;
				lambda10 <= lambda9;
				lambda11 <= lambda10;
//			end

		// for (j = t-1; j >=0; j--)
		//	if (delta) B[j] = lambda[j] *DI;
		//	else if (j != 0) B[j] = B[j-1];
		//	else B[j] = 0;
//			if (~phase0)
//			begin
				if (delta)	B0 <= tmp1;
				else if (~phase12) B0 <= B10;
				else B0 <= 0;
				//for (j = 1; j < 11; j = j + 1)
				//	B[j] <= B[j-1];
				B1 <= B0;
				B2 <= B1;
				B3 <= B2;
				B4 <= B3;
				B5 <= B4;
				B6 <= B5;
				B7 <= B6;
				B8 <= B7;
				B9 <= B8;
				B10 <= B9;
//			end

		// for (j = t-1; j >=0; j--)
		//	if (j != 0) omega[j] += D * A[j-1];
//			if (~phase0)
//			begin
				if (~phase12) omega0 <= omega11 ^ tmp2;
				else omega0 <= omega11;
				//for (j = 1; j < 12; j = j + 1)
				//	omega[j] <= omega[j-1];
				omega1 <= omega0;
				omega2 <= omega1;
				omega3 <= omega2;
				omega4 <= omega3;
				omega5 <= omega4;
				omega6 <= omega5;
				omega7 <= omega6;
				omega8 <= omega7;
				omega9 <= omega8;
				omega10 <= omega9;
				omega11 <= omega10;
//			end

		// for (j = t-1; j >=0; j--)
		//	if (delta) A[j] = omega[j] *DI;
		//	else if (j != 0) A[j] = A[j-1];
		//	else A[j] = 0;
//			if (~phase0)
//			begin
				if (delta)	A0 <= tmp3;
				else if (~phase12) A0 <= A10;
				//for (j = 1; j < 11; j = j + 1)
				//	A[j] <= A[j-1];
				A1 <= A0;
				A2 <= A1;
				A3 <= A2;
				A4 <= A3;
				A5 <= A4;
				A6 <= A5;
				A7 <= A6;
				A8 <= A7;
				A9 <= A8;
				A10 <= A9;
//			end
			end
		end
	end

	always @ (posedge clk)// or negedge clrn)
	begin
		if (~clrn)
		begin
			L <= 0;
			D <= 0;
		end
		else
		begin
		// if (delta) L = i - L + 1;
			if ((phase0 & delta) && (count != -1)) L <= count - L + 1;
		//for (D = j = 0; j < t; j = j + 1)
		//	D += lambda[j] * syndrome[t-j-1];
			if (phase0)
				D <= tmp0 ^ tmp1 ^ tmp2 ^ tmp3 ^ tmp4 ^ tmp5 ^ tmp6 ^ tmp7 ^ tmp8 ^ tmp9 ^ tmp10 ^ tmp11;
		end
	end
	
endmodule


module rsdec_berl_multiply (y, a, b, c, d, e);
	input [4:0] a, b, c, d;
	input e;
	output [4:0] y;
	wire [4:0] y;
	reg [4:0] p, q;

	always @ (a or c or e)
		if (e) p = c;
		else p = a;
	always @ (b or d or e)
		if (e) q = d;
		else q = b;

	multiply x0 (y, p, q);

endmodule

module multiply (y, a, b);
	input [4:0] a, b;
	output [4:0] y;
	reg [9:0] tempy;
	wire [4:0] y;

	assign y = tempy[4:0];

	always @(a or b)
	begin
		tempy = a * b;
	end
/*
	always @ (a or b)
	begin
		y[0] = (a[0] & b[0]) ^ (a[1] & b[4]) ^ (a[2] & b[3]) ^ (a[3] & b[2]) ^ (a[4] & b[1]) ^ (a[4] & b[4]);
		y[1] = (a[0] & b[1]) ^ (a[1] & b[0]) ^ (a[2] & b[4]) ^ (a[3] & b[3]) ^ (a[4] & b[2]);
		y[2] = (a[0] & b[2]) ^ (a[1] & b[1]) ^ (a[1] & b[4]) ^ (a[2] & b[0]) ^ (a[2] & b[3]) ^ (a[3] & b[2]) ^ (a[3] & b[4]) ^ (a[4] & b[1]) ^ (a[4] & b[3]) ^ (a[4] & b[4]);
		y[3] = (a[0] & b[3]) ^ (a[1] & b[2]) ^ (a[2] & b[1]) ^ (a[2] & b[4]) ^ (a[3] & b[0]) ^ (a[3] & b[3]) ^ (a[4] & b[2]) ^ (a[4] & b[4]);
		y[4] = (a[0] & b[4]) ^ (a[1] & b[3]) ^ (a[2] & b[2]) ^ (a[3] & b[1]) ^ (a[3] & b[4]) ^ (a[4] & b[0]) ^ (a[4] & b[3]);
	endi 
*/
endmodule

// -------------------------------------------------------------------------
//Chien-Forney search circuit for Reed-Solomon decoder
//Copyright (C) Tue Apr  2 17:21:51 2002
//by Ming-Han Lei(hendrik@humanistic.org)
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU Lesser General Public License
//as published by the Free Software Foundation; either version 2
//of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU Lesser General Public License for more details.
//
//You should have received a copy of the GNU Lesser General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
// --------------------------------------------------------------------------

module rsdec_chien_scale0 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[0];
		y[1] = x[1];
		y[2] = x[2];
		y[3] = x[3];
		y[4] = x[4];
	end
endmodule

module rsdec_chien_scale1 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[4];
		y[1] = x[0];
		y[2] = x[1] ^ x[4];
		y[3] = x[2];
		y[4] = x[3];
	end
endmodule

module rsdec_chien_scale2 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[3];
		y[1] = x[4];
		y[2] = x[0] ^ x[3];
		y[3] = x[1] ^ x[4];
		y[4] = x[2];
	end
endmodule

module rsdec_chien_scale3 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[2];
		y[1] = x[3];
		y[2] = x[2] ^ x[4];
		y[3] = x[0] ^ x[3];
		y[4] = x[1] ^ x[4];
	end
endmodule

module rsdec_chien_scale4 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[1] ^ x[4];
		y[1] = x[2];
		y[2] = x[1] ^ x[3] ^ x[4];
		y[3] = x[2] ^ x[4];
		y[4] = x[0] ^ x[3];
	end
endmodule

module rsdec_chien_scale5 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[0] ^ x[3];
		y[1] = x[1] ^ x[4];
		y[2] = x[0] ^ x[2] ^ x[3];
		y[3] = x[1] ^ x[3] ^ x[4];
		y[4] = x[2] ^ x[4];
	end
endmodule

module rsdec_chien_scale6 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[2] ^ x[4];
		y[1] = x[0] ^ x[3];
		y[2] = x[1] ^ x[2];
		y[3] = x[0] ^ x[2] ^ x[3];
		y[4] = x[1] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_chien_scale7 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[1] ^ x[3] ^ x[4];
		y[1] = x[2] ^ x[4];
		y[2] = x[0] ^ x[1] ^ x[4];
		y[3] = x[1] ^ x[2];
		y[4] = x[0] ^ x[2] ^ x[3];
	end
endmodule

module rsdec_chien_scale8 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[0] ^ x[2] ^ x[3];
		y[1] = x[1] ^ x[3] ^ x[4];
		y[2] = x[0] ^ x[3] ^ x[4];
		y[3] = x[0] ^ x[1] ^ x[4];
		y[4] = x[1] ^ x[2];
	end
endmodule

module rsdec_chien_scale9 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[1] ^ x[2];
		y[1] = x[0] ^ x[2] ^ x[3];
		y[2] = x[2] ^ x[3] ^ x[4];
		y[3] = x[0] ^ x[3] ^ x[4];
		y[4] = x[0] ^ x[1] ^ x[4];
	end
endmodule

module rsdec_chien_scale10 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[0] ^ x[1] ^ x[4];
		y[1] = x[1] ^ x[2];
		y[2] = x[1] ^ x[2] ^ x[3] ^ x[4];
		y[3] = x[2] ^ x[3] ^ x[4];
		y[4] = x[0] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_chien_scale11 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;

	always @ (x)
	begin
		y[0] = x[0] ^ x[3] ^ x[4];
		y[1] = x[0] ^ x[1] ^ x[4];
		y[2] = x[0] ^ x[1] ^ x[2] ^ x[3] ^ x[4];
		y[3] = x[1] ^ x[2] ^ x[3] ^ x[4];
		y[4] = x[2] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_chien (error, alpha, lambda, omega, even, D, search, load, shorten, clk, clrn);
	input clk, clrn, load, search, shorten;
	input [4:0] D;
	input [4:0] lambda;
	input [4:0] omega;
	output [4:0] even, error;
	output [4:0] alpha;
	reg [4:0] even, error;
	reg [4:0] alpha;

	wire [4:0] scale0;
	wire [4:0] scale1;
	wire [4:0] scale2;
	wire [4:0] scale3;
	wire [4:0] scale4;
	wire [4:0] scale5;
	wire [4:0] scale6;
	wire [4:0] scale7;
	wire [4:0] scale8;
	wire [4:0] scale9;
	wire [4:0] scale10;
	wire [4:0] scale11;
	wire [4:0] scale12;
	wire [4:0] scale13;
	wire [4:0] scale14;
	wire [4:0] scale15;
	wire [4:0] scale16;
	wire [4:0] scale17;
	wire [4:0] scale18;
	wire [4:0] scale19;
	wire [4:0] scale20;
	wire [4:0] scale21;
	wire [4:0] scale22;
	wire [4:0] scale23;
	reg [4:0] data0;
	reg [4:0] data1;
	reg [4:0] data2;
	reg [4:0] data3;
	reg [4:0] data4;
	reg [4:0] data5;
	reg [4:0] data6;
	reg [4:0] data7;
	reg [4:0] data8;
	reg [4:0] data9;
	reg [4:0] data10;
	reg [4:0] data11;
	reg [4:0] a0;
	reg [4:0] a1;
	reg [4:0] a2;
	reg [4:0] a3;
	reg [4:0] a4;
	reg [4:0] a5;
	reg [4:0] a6;
	reg [4:0] a7;
	reg [4:0] a8;
	reg [4:0] a9;
	reg [4:0] a10;
	reg [4:0] a11;
	reg [4:0] l0;
	reg [4:0] l1;
	reg [4:0] l2;
	reg [4:0] l3;
	reg [4:0] l4;
	reg [4:0] l5;
	reg [4:0] l6;
	reg [4:0] l7;
	reg [4:0] l8;
	reg [4:0] l9;
	reg [4:0] l10;
	reg [4:0] l11;
	reg [4:0] o0;
	reg [4:0] o1;
	reg [4:0] o2;
	reg [4:0] o3;
	reg [4:0] o4;
	reg [4:0] o5;
	reg [4:0] o6;
	reg [4:0] o7;
	reg [4:0] o8;
	reg [4:0] o9;
	reg [4:0] o10;
	reg [4:0] o11;
	reg [4:0] odd, numerator;
	wire [4:0] tmp;

	rsdec_chien_scale0 x0 (scale0, data0);
	rsdec_chien_scale1 x1 (scale1, data1);
	rsdec_chien_scale2 x2 (scale2, data2);
	rsdec_chien_scale3 x3 (scale3, data3);
	rsdec_chien_scale4 x4 (scale4, data4);
	rsdec_chien_scale5 x5 (scale5, data5);
	rsdec_chien_scale6 x6 (scale6, data6);
	rsdec_chien_scale7 x7 (scale7, data7);
	rsdec_chien_scale8 x8 (scale8, data8);
	rsdec_chien_scale9 x9 (scale9, data9);
	rsdec_chien_scale10 x10 (scale10, data10);
	rsdec_chien_scale11 x11 (scale11, data11);
	rsdec_chien_scale0 x12 (scale12, o0);
	rsdec_chien_scale1 x13 (scale13, o1);
	rsdec_chien_scale2 x14 (scale14, o2);
	rsdec_chien_scale3 x15 (scale15, o3);
	rsdec_chien_scale4 x16 (scale16, o4);
	rsdec_chien_scale5 x17 (scale17, o5);
	rsdec_chien_scale6 x18 (scale18, o6);
	rsdec_chien_scale7 x19 (scale19, o7);
	rsdec_chien_scale8 x20 (scale20, o8);
	rsdec_chien_scale9 x21 (scale21, o9);
	rsdec_chien_scale10 x22 (scale22, o10);
	rsdec_chien_scale11 x23 (scale23, o11);

	always @ (shorten or a0 or l0)
		if (shorten) data0 = a0;
		else data0 = l0;

	always @ (shorten or a1 or l1)
		if (shorten) data1 = a1;
		else data1 = l1;

	always @ (shorten or a2 or l2)
		if (shorten) data2 = a2;
		else data2 = l2;

	always @ (shorten or a3 or l3)
		if (shorten) data3 = a3;
		else data3 = l3;

	always @ (shorten or a4 or l4)
		if (shorten) data4 = a4;
		else data4 = l4;

	always @ (shorten or a5 or l5)
		if (shorten) data5 = a5;
		else data5 = l5;

	always @ (shorten or a6 or l6)
		if (shorten) data6 = a6;
		else data6 = l6;

	always @ (shorten or a7 or l7)
		if (shorten) data7 = a7;
		else data7 = l7;

	always @ (shorten or a8 or l8)
		if (shorten) data8 = a8;
		else data8 = l8;

	always @ (shorten or a9 or l9)
		if (shorten) data9 = a9;
		else data9 = l9;

	always @ (shorten or a10 or l10)
		if (shorten) data10 = a10;
		else data10 = l10;

	always @ (shorten or a11 or l11)
		if (shorten) data11 = a11;
		else data11 = l11;

	always @ (posedge clk)// or negedge clrn)
	begin
		if (~clrn)
		begin
			l0 <= 0;
			l1 <= 0;
			l2 <= 0;
			l3 <= 0;
			l4 <= 0;
			l5 <= 0;
			l6 <= 0;
			l7 <= 0;
			l8 <= 0;
			l9 <= 0;
			l10 <= 0;
			l11 <= 0;
			o0 <= 0;
			o1 <= 0;
			o2 <= 0;
			o3 <= 0;
			o4 <= 0;
			o5 <= 0;
			o6 <= 0;
			o7 <= 0;
			o8 <= 0;
			o9 <= 0;
			o10 <= 0;
			o11 <= 0;
			a0 <= 1;
			a1 <= 1;
			a2 <= 1;
			a3 <= 1;
			a4 <= 1;
			a5 <= 1;
			a6 <= 1;
			a7 <= 1;
			a8 <= 1;
			a9 <= 1;
			a10 <= 1;
			a11 <= 1;
		end
		else if (shorten)
		begin
			a0 <= scale0;
			a1 <= scale1;
			a2 <= scale2;
			a3 <= scale3;
			a4 <= scale4;
			a5 <= scale5;
			a6 <= scale6;
			a7 <= scale7;
			a8 <= scale8;
			a9 <= scale9;
			a10 <= scale10;
			a11 <= scale11;
		end
		else if (search)
		begin
			l0 <= scale0;
			l1 <= scale1;
			l2 <= scale2;
			l3 <= scale3;
			l4 <= scale4;
			l5 <= scale5;
			l6 <= scale6;
			l7 <= scale7;
			l8 <= scale8;
			l9 <= scale9;
			l10 <= scale10;
			l11 <= scale11;
			o0 <= scale12;
			o1 <= scale13;
			o2 <= scale14;
			o3 <= scale15;
			o4 <= scale16;
			o5 <= scale17;
			o6 <= scale18;
			o7 <= scale19;
			o8 <= scale20;
			o9 <= scale21;
			o10 <= scale22;
			o11 <= scale23;
		end
		else if (load)
		begin
			l0 <= lambda;
			l1 <= l0;
			l2 <= l1;
			l3 <= l2;
			l4 <= l3;
			l5 <= l4;
			l6 <= l5;
			l7 <= l6;
			l8 <= l7;
			l9 <= l8;
			l10 <= l9;
			l11 <= l10;
			o0 <= omega;
			o1 <= o0;
			o2 <= o1;
			o3 <= o2;
			o4 <= o3;
			o5 <= o4;
			o6 <= o5;
			o7 <= o6;
			o8 <= o7;
			o9 <= o8;
			o10 <= o9;
			o11 <= o10;
			a0 <= a11;
			a1 <= a0;
			a2 <= a1;
			a3 <= a2;
			a4 <= a3;
			a5 <= a4;
			a6 <= a5;
			a7 <= a6;
			a8 <= a7;
			a9 <= a8;
			a10 <= a9;
			a11 <= a10;
		end
	end

	always @ (l0 or l2 or l4 or l6 or l8 or l10)
		even = l0 ^ l2 ^ l4 ^ l6 ^ l8 ^ l10;

	always @ (l1 or l3 or l5 or l7 or l9 or l11)
		odd = l1 ^ l3 ^ l5 ^ l7 ^ l9 ^ l11;

	always @ (o0 or o1 or o2 or o3 or o4 or o5 or o6 or o7 or o8 or o9 or o10 or o11)
		numerator = o0 ^ o1 ^ o2 ^ o3 ^ o4 ^ o5 ^ o6 ^ o7 ^ o8 ^ o9 ^ o10 ^ o11;

	multiply m0 (tmp, numerator, D);

	always @ (even or odd or tmp)
		if (even == odd) error = tmp;
		else error = 0;

	always @ (a11) alpha = a11;

endmodule

// -------------------------------------------------------------------------
//Syndrome generator circuit in Reed-Solomon Decoder
//Copyright (C) Tue Apr  2 17:22:07 2002
//by Ming-Han Lei(hendrik@humanistic.org)
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU Lesser General Public License
//as published by the Free Software Foundation; either version 2
//of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You should have received a copy of the GNU Lesser General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
// --------------------------------------------------------------------------

module rsdec_syn_m0 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[4];
		y[1] = x[0];
		y[2] = x[1] ^ x[4];
		y[3] = x[2];
		y[4] = x[3];
	end
endmodule

module rsdec_syn_m1 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[3];
		y[1] = x[4];
		y[2] = x[0] ^ x[3];
		y[3] = x[1] ^ x[4];
		y[4] = x[2];
	end
endmodule

module rsdec_syn_m2 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[2];
		y[1] = x[3];
		y[2] = x[2] ^ x[4];
		y[3] = x[0] ^ x[3];
		y[4] = x[1] ^ x[4];
	end
endmodule

module rsdec_syn_m3 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[1] ^ x[4];
		y[1] = x[2];
		y[2] = x[1] ^ x[3] ^ x[4];
		y[3] = x[2] ^ x[4];
		y[4] = x[0] ^ x[3];
	end
endmodule

module rsdec_syn_m4 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[0] ^ x[3];
		y[1] = x[1] ^ x[4];
		y[2] = x[0] ^ x[2] ^ x[3];
		y[3] = x[1] ^ x[3] ^ x[4];
		y[4] = x[2] ^ x[4];
	end
endmodule

module rsdec_syn_m5 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[2] ^ x[4];
		y[1] = x[0] ^ x[3];
		y[2] = x[1] ^ x[2];
		y[3] = x[0] ^ x[2] ^ x[3];
		y[4] = x[1] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_syn_m6 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[1] ^ x[3] ^ x[4];
		y[1] = x[2] ^ x[4];
		y[2] = x[0] ^ x[1] ^ x[4];
		y[3] = x[1] ^ x[2];
		y[4] = x[0] ^ x[2] ^ x[3];
	end
endmodule

module rsdec_syn_m7 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[0] ^ x[2] ^ x[3];
		y[1] = x[1] ^ x[3] ^ x[4];
		y[2] = x[0] ^ x[3] ^ x[4];
		y[3] = x[0] ^ x[1] ^ x[4];
		y[4] = x[1] ^ x[2];
	end
endmodule

module rsdec_syn_m8 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[1] ^ x[2];
		y[1] = x[0] ^ x[2] ^ x[3];
		y[2] = x[2] ^ x[3] ^ x[4];
		y[3] = x[0] ^ x[3] ^ x[4];
		y[4] = x[0] ^ x[1] ^ x[4];
	end
endmodule

module rsdec_syn_m9 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[0] ^ x[1] ^ x[4];
		y[1] = x[1] ^ x[2];
		y[2] = x[1] ^ x[2] ^ x[3] ^ x[4];
		y[3] = x[2] ^ x[3] ^ x[4];
		y[4] = x[0] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_syn_m10 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[0] ^ x[3] ^ x[4];
		y[1] = x[0] ^ x[1] ^ x[4];
		y[2] = x[0] ^ x[1] ^ x[2] ^ x[3] ^ x[4];
		y[3] = x[1] ^ x[2] ^ x[3] ^ x[4];
		y[4] = x[2] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_syn_m11 (y, x);
	input [4:0] x;
	output [4:0] y;
	reg [4:0] y;
	always @ (x)
	begin
		y[0] = x[2] ^ x[3] ^ x[4];
		y[1] = x[0] ^ x[3] ^ x[4];
		y[2] = x[0] ^ x[1] ^ x[2] ^ x[3];
		y[3] = x[0] ^ x[1] ^ x[2] ^ x[3] ^ x[4];
		y[4] = x[1] ^ x[2] ^ x[3] ^ x[4];
	end
endmodule

module rsdec_syn (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, u, enable, shift, init, clk, clrn);
	input [4:0] u;
	input clk, clrn, shift, init, enable;
	output [4:0] y0;
	output [4:0] y1;
	output [4:0] y2;
	output [4:0] y3;
	output [4:0] y4;
	output [4:0] y5;
	output [4:0] y6;
	output [4:0] y7;
	output [4:0] y8;
	output [4:0] y9;
	output [4:0] y10;
	output [4:0] y11;
	reg [4:0] y0;
	reg [4:0] y1;
	reg [4:0] y2;
	reg [4:0] y3;
	reg [4:0] y4;
	reg [4:0] y5;
	reg [4:0] y6;
	reg [4:0] y7;
	reg [4:0] y8;
	reg [4:0] y9;
	reg [4:0] y10;
	reg [4:0] y11;

	wire [4:0] scale0;
	wire [4:0] scale1;
	wire [4:0] scale2;
	wire [4:0] scale3;
	wire [4:0] scale4;
	wire [4:0] scale5;
	wire [4:0] scale6;
	wire [4:0] scale7;
	wire [4:0] scale8;
	wire [4:0] scale9;
	wire [4:0] scale10;
	wire [4:0] scale11;

	rsdec_syn_m0 m0 (scale0, y0);
	rsdec_syn_m1 m1 (scale1, y1);
	rsdec_syn_m2 m2 (scale2, y2);
	rsdec_syn_m3 m3 (scale3, y3);
	rsdec_syn_m4 m4 (scale4, y4);
	rsdec_syn_m5 m5 (scale5, y5);
	rsdec_syn_m6 m6 (scale6, y6);
	rsdec_syn_m7 m7 (scale7, y7);
	rsdec_syn_m8 m8 (scale8, y8);
	rsdec_syn_m9 m9 (scale9, y9);
	rsdec_syn_m10 m10 (scale10, y10);
	rsdec_syn_m11 m11 (scale11, y11);

	always @ (posedge clk)// or negedge clrn)
	begin
		if (~clrn)
		begin
			y0 <= 0;
			y1 <= 0;
			y2 <= 0;
			y3 <= 0;
			y4 <= 0;
			y5 <= 0;
			y6 <= 0;
			y7 <= 0;
			y8 <= 0;
			y9 <= 0;
			y10 <= 0;
			y11 <= 0;
		end
		else if (init)
		begin
			y0 <= u;
			y1 <= u;
			y2 <= u;
			y3 <= u;
			y4 <= u;
			y5 <= u;
			y6 <= u;
			y7 <= u;
			y8 <= u;
			y9 <= u;
			y10 <= u;
			y11 <= u;
		end
		else if (enable)
		begin
			y0 <= scale0 ^ u;
			y1 <= scale1 ^ u;
			y2 <= scale2 ^ u;
			y3 <= scale3 ^ u;
			y4 <= scale4 ^ u;
			y5 <= scale5 ^ u;
			y6 <= scale6 ^ u;
			y7 <= scale7 ^ u;
			y8 <= scale8 ^ u;
			y9 <= scale9 ^ u;
			y10 <= scale10 ^ u;
			y11 <= scale11 ^ u;
		end
		else if (shift)
		begin
			y0 <= y1;
			y1 <= y2;
			y2 <= y3;
			y3 <= y4;
			y4 <= y5;
			y5 <= y6;
			y6 <= y7;
			y7 <= y8;
			y8 <= y9;
			y9 <= y10;
			y10 <= y11;
			y11 <= y0;
		end
	end

endmodule

