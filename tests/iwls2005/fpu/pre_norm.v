/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Pre Normalize                                              ////
////  Pre Normalization Unit for Add/Sub Operations              ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000 Rudolf Usselmann                         ////
////                    rudi@asics.ws                            ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

`timescale 1ns / 100ps


module pre_norm(clk, rmode, add, opa, opb, opa_nan, opb_nan, fracta_out,
		fractb_out, exp_dn_out, sign, nan_sign, result_zero_sign,
		fasu_op);
input		clk;
input	[1:0]	rmode;
input		add;
input	[31:0]	opa, opb;
input		opa_nan, opb_nan;
output	[26:0]	fracta_out, fractb_out;
output	[7:0]	exp_dn_out;
output		sign;
output		nan_sign, result_zero_sign;
output		fasu_op;			// Operation Output

////////////////////////////////////////////////////////////////////////
//
// Local Wires and registers
//

wire		signa, signb;		// alias to opX sign
wire	[7:0]	expa, expb;		// alias to opX exponent
wire	[22:0]	fracta, fractb;		// alias to opX fraction
wire		expa_lt_expb;		// expa is larger than expb indicator
wire		fractb_lt_fracta;	// fractb is larger than fracta indicator
reg	[7:0]	exp_dn_out;		// de normalized exponent output
wire	[7:0]	exp_small, exp_large;
wire	[7:0]	exp_diff;		// Numeric difference of the two exponents
wire	[22:0]	adj_op;			// Fraction adjustment: input
wire	[26:0]	adj_op_tmp;
wire	[26:0]	adj_op_out;		// Fraction adjustment: output
wire	[26:0]	fracta_n, fractb_n;	// Fraction selection after normalizing
wire	[26:0]	fracta_s, fractb_s;	// Fraction Sorting out
reg	[26:0]	fracta_out, fractb_out;	// Fraction Output
reg		sign, sign_d;		// Sign Output
reg		add_d;			// operation (add/sub)
reg		fasu_op;		// operation (add/sub) register
wire		expa_dn, expb_dn;
reg		sticky;
reg		result_zero_sign;
reg		add_r, signa_r, signb_r;
wire	[4:0]	exp_diff_sft;
wire		exp_lt_27;
wire		op_dn;
wire	[26:0]	adj_op_out_sft;
reg		fracta_lt_fractb, fracta_eq_fractb;
wire		nan_sign1;
reg		nan_sign;

////////////////////////////////////////////////////////////////////////
//
// Aliases
//

assign  signa = opa[31];
assign  signb = opb[31];
assign   expa = opa[30:23];
assign   expb = opb[30:23];
assign fracta = opa[22:0];
assign fractb = opb[22:0];

////////////////////////////////////////////////////////////////////////
//
// Pre-Normalize exponents (and fractions)
//

assign expa_lt_expb = expa > expb;		// expa is larger than expb

// ---------------------------------------------------------------------
// Normalize

assign expa_dn = !(|expa);			// opa denormalized
assign expb_dn = !(|expb);			// opb denormalized

// ---------------------------------------------------------------------
// Calculate the difference between the smaller and larger exponent

wire	[7:0]	exp_diff1, exp_diff1a, exp_diff2;

assign exp_small  = expa_lt_expb ? expb : expa;
assign exp_large  = expa_lt_expb ? expa : expb;
assign exp_diff1  = exp_large - exp_small;
assign exp_diff1a = exp_diff1-1;
assign exp_diff2  = (expa_dn | expb_dn) ? exp_diff1a : exp_diff1;
assign  exp_diff  = (expa_dn & expb_dn) ? 8'h0 : exp_diff2;

always @(posedge clk)	// If numbers are equal we should return zero
	exp_dn_out <= #1 (!add_d & expa==expb & fracta==fractb) ? 8'h0 : exp_large;

// ---------------------------------------------------------------------
// Adjust the smaller fraction


assign op_dn	  = expa_lt_expb ? expb_dn : expa_dn;
assign adj_op     = expa_lt_expb ? fractb : fracta;
assign adj_op_tmp = { ~op_dn, adj_op, 3'b0 };	// recover hidden bit (op_dn) 

// adj_op_out is 27 bits wide, so can only be shifted 27 bits to the right
assign exp_lt_27	= exp_diff  > 8'd27;
assign exp_diff_sft	= exp_lt_27 ? 5'd27 : exp_diff[4:0];
assign adj_op_out_sft	= adj_op_tmp >> exp_diff_sft;
assign adj_op_out	= {adj_op_out_sft[26:1], adj_op_out_sft[0] | sticky };

// ---------------------------------------------------------------------
// Get truncated portion (sticky bit)

always @(exp_diff_sft or adj_op_tmp)
   case(exp_diff_sft)		// synopsys full_case parallel_case
	00: sticky = 1'h0;
	01: sticky =  adj_op_tmp[0]; 
	02: sticky = |adj_op_tmp[01:0];
	03: sticky = |adj_op_tmp[02:0];
	04: sticky = |adj_op_tmp[03:0];
	05: sticky = |adj_op_tmp[04:0];
	06: sticky = |adj_op_tmp[05:0];
	07: sticky = |adj_op_tmp[06:0];
	08: sticky = |adj_op_tmp[07:0];
	09: sticky = |adj_op_tmp[08:0];
	10: sticky = |adj_op_tmp[09:0];
	11: sticky = |adj_op_tmp[10:0];
	12: sticky = |adj_op_tmp[11:0];
	13: sticky = |adj_op_tmp[12:0];
	14: sticky = |adj_op_tmp[13:0];
	15: sticky = |adj_op_tmp[14:0];
	16: sticky = |adj_op_tmp[15:0];
	17: sticky = |adj_op_tmp[16:0];
	18: sticky = |adj_op_tmp[17:0];
	19: sticky = |adj_op_tmp[18:0];
	20: sticky = |adj_op_tmp[19:0];
	21: sticky = |adj_op_tmp[20:0];
	22: sticky = |adj_op_tmp[21:0];
	23: sticky = |adj_op_tmp[22:0];
	24: sticky = |adj_op_tmp[23:0];
	25: sticky = |adj_op_tmp[24:0];
	26: sticky = |adj_op_tmp[25:0];
	27: sticky = |adj_op_tmp[26:0];
   endcase

// ---------------------------------------------------------------------
// Select operands for add/sub (recover hidden bit)

assign fracta_n = expa_lt_expb ? {~expa_dn, fracta, 3'b0} : adj_op_out;
assign fractb_n = expa_lt_expb ? adj_op_out : {~expb_dn, fractb, 3'b0};

// ---------------------------------------------------------------------
// Sort operands (for sub only)

assign fractb_lt_fracta = fractb_n > fracta_n;	// fractb is larger than fracta
assign fracta_s = fractb_lt_fracta ? fractb_n : fracta_n;
assign fractb_s = fractb_lt_fracta ? fracta_n : fractb_n;

always @(posedge clk)
	fracta_out <= #1 fracta_s;

always @(posedge clk)
	fractb_out <= #1 fractb_s;

// ---------------------------------------------------------------------
// Determine sign for the output

// sign: 0=Positive Number; 1=Negative Number
always @(signa or signb or add or fractb_lt_fracta)
   case({signa, signb, add})		// synopsys full_case parallel_case

   	// Add
	3'b0_0_1: sign_d = 0;
	3'b0_1_1: sign_d = fractb_lt_fracta;
	3'b1_0_1: sign_d = !fractb_lt_fracta;
	3'b1_1_1: sign_d = 1;

	// Sub
	3'b0_0_0: sign_d = fractb_lt_fracta;
	3'b0_1_0: sign_d = 0;
	3'b1_0_0: sign_d = 1;
	3'b1_1_0: sign_d = !fractb_lt_fracta;
   endcase

always @(posedge clk)
	sign <= #1 sign_d;

// Fix sign for ZERO result
always @(posedge clk)
	signa_r <= #1 signa;

always @(posedge clk)
	signb_r <= #1 signb;

always @(posedge clk)
	add_r <= #1 add;

always @(posedge clk)
	result_zero_sign <= #1	( add_r &  signa_r &  signb_r) |
				(!add_r &  signa_r & !signb_r) |
				( add_r & (signa_r |  signb_r) & (rmode==3)) |
				(!add_r & (signa_r == signb_r) & (rmode==3));

// Fix sign for NAN result
always @(posedge clk)
	fracta_lt_fractb <= #1 fracta < fractb;

always @(posedge clk)
	fracta_eq_fractb <= #1 fracta == fractb;

assign nan_sign1 = fracta_eq_fractb ? (signa_r & signb_r) : fracta_lt_fractb ? signb_r : signa_r;

always @(posedge clk)
	nan_sign <= #1 (opa_nan & opb_nan) ? nan_sign1 : opb_nan ? signb_r : signa_r;

////////////////////////////////////////////////////////////////////////
//
// Decode Add/Sub operation
//

// add: 1=Add; 0=Subtract
always @(signa or signb or add)
   case({signa, signb, add})		// synopsys full_case parallel_case
   
   	// Add
	3'b0_0_1: add_d = 1;
	3'b0_1_1: add_d = 0;
	3'b1_0_1: add_d = 0;
	3'b1_1_1: add_d = 1;
	
	// Sub
	3'b0_0_0: add_d = 0;
	3'b0_1_0: add_d = 1;
	3'b1_0_0: add_d = 1;
	3'b1_1_0: add_d = 0;
   endcase

always @(posedge clk)
	fasu_op <= #1 add_d;

endmodule
