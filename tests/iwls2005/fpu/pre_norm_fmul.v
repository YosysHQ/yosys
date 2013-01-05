/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Pre Normalize                                              ////
////  Floating Point Pre Normalization Unit for FMUL             ////
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

module pre_norm_fmul(clk, fpu_op, opa, opb, fracta, fractb, exp_out, sign,
		sign_exe, inf, exp_ovf, underflow);
input		clk;
input	[2:0]	fpu_op;
input	[31:0]	opa, opb;
output	[23:0]	fracta, fractb;
output	[7:0]	exp_out;
output		sign, sign_exe;
output		inf;
output	[1:0]	exp_ovf;
output	[2:0]	underflow;

////////////////////////////////////////////////////////////////////////
//
// Local Wires and registers
//

reg	[7:0]	exp_out;
wire		signa, signb;
reg		sign, sign_d;
reg		sign_exe;
reg		inf;
wire	[1:0]	exp_ovf_d;
reg	[1:0]	exp_ovf;
wire	[7:0]	expa, expb;
wire	[7:0]	exp_tmp1, exp_tmp2;
wire		co1, co2;
wire		expa_dn, expb_dn;
wire	[7:0]	exp_out_a;
wire		opa_00, opb_00, fracta_00, fractb_00;
wire	[7:0]	exp_tmp3, exp_tmp4, exp_tmp5;
wire	[2:0]	underflow_d;
reg	[2:0]	underflow;
wire		op_div = (fpu_op == 3'b011);
wire	[7:0]	exp_out_mul, exp_out_div;

////////////////////////////////////////////////////////////////////////
//
// Aliases
//

assign  signa = opa[31];
assign  signb = opb[31];
assign   expa = opa[30:23];
assign   expb = opb[30:23];

////////////////////////////////////////////////////////////////////////
//
// Calculate Exponenet
//

assign expa_dn   = !(|expa);
assign expb_dn   = !(|expb);
assign opa_00    = !(|opa[30:0]);
assign opb_00    = !(|opb[30:0]);
assign fracta_00 = !(|opa[22:0]);
assign fractb_00 = !(|opb[22:0]);

assign fracta = {!expa_dn,opa[22:0]};	// Recover hidden bit
assign fractb = {!expb_dn,opb[22:0]};	// Recover hidden bit

assign {co1,exp_tmp1} = op_div ? (expa - expb)            : (expa + expb);
assign {co2,exp_tmp2} = op_div ? ({co1,exp_tmp1} + 8'h7f) : ({co1,exp_tmp1} - 8'h7f);

assign exp_tmp3 = exp_tmp2 + 1;
assign exp_tmp4 = 8'h7f - exp_tmp1;
assign exp_tmp5 = op_div ? (exp_tmp4+1) : (exp_tmp4-1);


always@(posedge clk)
	exp_out <= #1 op_div ? exp_out_div : exp_out_mul;

assign exp_out_div = (expa_dn | expb_dn) ? (co2 ? exp_tmp5 : exp_tmp3 ) : co2 ? exp_tmp4 : exp_tmp2;
assign exp_out_mul = exp_ovf_d[1] ? exp_out_a : (expa_dn | expb_dn) ? exp_tmp3 : exp_tmp2;
assign exp_out_a   = (expa_dn | expb_dn) ? exp_tmp5 : exp_tmp4;
assign exp_ovf_d[0] = op_div ? (expa[7] & !expb[7]) : (co2 & expa[7] & expb[7]);
assign exp_ovf_d[1] = op_div ? co2                  : ((!expa[7] & !expb[7] & exp_tmp2[7]) | co2);

always @(posedge clk)
	exp_ovf <= #1 exp_ovf_d;

assign underflow_d[0] =	(exp_tmp1 < 8'h7f) & !co1 & !(opa_00 | opb_00 | expa_dn | expb_dn);
assign underflow_d[1] =	((expa[7] | expb[7]) & !opa_00 & !opb_00) |
			 (expa_dn & !fracta_00) | (expb_dn & !fractb_00);
assign underflow_d[2] =	 !opa_00 & !opb_00 & (exp_tmp1 == 8'h7f);

always @(posedge clk)
	underflow <= #1 underflow_d;

always @(posedge clk)
	inf <= #1 op_div ? (expb_dn & !expa[7]) : ({co1,exp_tmp1} > 9'h17e) ;


////////////////////////////////////////////////////////////////////////
//
// Determine sign for the output
//

// sign: 0=Posetive Number; 1=Negative Number
always @(signa or signb)
   case({signa, signb})		// synopsys full_case parallel_case
	2'b0_0: sign_d = 0;
	2'b0_1: sign_d = 1;
	2'b1_0: sign_d = 1;
	2'b1_1: sign_d = 0;
   endcase

always @(posedge clk)
	sign <= #1 sign_d;

always @(posedge clk)
	sign_exe <= #1 signa & signb;

endmodule