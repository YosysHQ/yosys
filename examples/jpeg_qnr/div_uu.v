/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Non-restoring unsinged divider                             ////
////                                                             ////
////  Author: Richard Herveille                                  ////
////          richard@asics.ws                                   ////
////          www.asics.ws                                       ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2002 Richard Herveille                        ////
////                    richard@asics.ws                         ////
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

//  CVS Log
//
//  $Id: div_uu.v,v 1.3 2002-10-31 12:52:55 rherveille Exp $
//
//  $Date: 2002-10-31 12:52:55 $
//  $Revision: 1.3 $
//  $Author: rherveille $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: not supported by cvs2svn $
//               Revision 1.2  2002/10/23 09:07:03  rherveille
//               Improved many files.
//               Fixed some bugs in Run-Length-Encoder.
//               Removed dependency on ud_cnt and ro_cnt.
//               Started (Motion)JPEG hardware encoder project.
//

//synopsys translate_off
`include "timescale.v"
//synopsys translate_on

module div_uu(clk, ena, z, d, q, s, div0, ovf);

	//
	// parameters
	//
	parameter z_width = 16;
	parameter d_width = z_width /2;
	
	//
	// inputs & outputs
	//
	input clk;               // system clock
	input ena;               // clock enable

	input  [z_width -1:0] z; // divident
	input  [d_width -1:0] d; // divisor
	output [d_width -1:0] q; // quotient
	reg [d_width-1:0] q;
	output [d_width -1:0] s; // remainder
	reg [d_width-1:0] s;
	output div0;
	reg div0;
	output ovf;
	reg ovf;

	//	
	// functions
	//
	function [z_width:0] gen_s;
		input [z_width:0] si;
		input [z_width:0] di;
	begin
	  if(si[z_width])
	    gen_s = {si[z_width-1:0], 1'b0} + di;
	  else
	    gen_s = {si[z_width-1:0], 1'b0} - di;
	end
	endfunction

	function [d_width-1:0] gen_q;
		input [d_width-1:0] qi;
		input [z_width:0] si;
	begin
	  gen_q = {qi[d_width-2:0], ~si[z_width]};
	end
	endfunction

	function [d_width-1:0] assign_s;
		input [z_width:0] si;
		input [z_width:0] di;
		reg [z_width:0] tmp;
	begin
	  if(si[z_width])
	    tmp = si + di;
	  else
	    tmp = si;

	  assign_s = tmp[z_width-1:z_width-4];
	end
	endfunction

	//
	// variables
	//
	reg [d_width-1:0] q_pipe  [d_width-1:0];
	reg [z_width:0] s_pipe  [d_width:0];
	reg [z_width:0] d_pipe  [d_width:0];

	reg [d_width:0] div0_pipe, ovf_pipe;
	//
	// perform parameter checks
	//
	// synopsys translate_off
	initial
	begin
	  if(d_width !== z_width / 2)
	    $display("div.v parameter error (d_width != z_width/2).");
	end
	// synopsys translate_on

	integer n0, n1, n2, n3;

	// generate divisor (d) pipe
	always @(d)
	  d_pipe[0] <= {1'b0, d, {(z_width-d_width){1'b0}} };

	always @(posedge clk)
	  if(ena)
	    for(n0=1; n0 <= d_width; n0=n0+1)
	       d_pipe[n0] <= #1 d_pipe[n0-1];

	// generate internal remainder pipe
	always @(z)
	  s_pipe[0] <= z;

	always @(posedge clk)
	  if(ena)
	    for(n1=1; n1 <= d_width; n1=n1+1)
	       s_pipe[n1] <= #1 gen_s(s_pipe[n1-1], d_pipe[n1-1]);

	// generate quotient pipe
	always @(posedge clk)
	  q_pipe[0] <= #1 0;

	always @(posedge clk)
	  if(ena)
	    for(n2=1; n2 < d_width; n2=n2+1)
	       q_pipe[n2] <= #1 gen_q(q_pipe[n2-1], s_pipe[n2]);


	// flags (divide_by_zero, overflow)
	always @(z or d)
	begin
	  ovf_pipe[0]  <= !(z[z_width-1:d_width] < d);
	  div0_pipe[0] <= ~|d;
	end

	always @(posedge clk)
	  if(ena)
	    for(n3=1; n3 <= d_width; n3=n3+1)
	    begin
	        ovf_pipe[n3] <= #1 ovf_pipe[n3-1];
	        div0_pipe[n3] <= #1 div0_pipe[n3-1];
	    end

	// assign outputs
	always @(posedge clk)
	  if(ena)
	    ovf <= #1 ovf_pipe[d_width];

	always @(posedge clk)
	  if(ena)
	    div0 <= #1 div0_pipe[d_width];

	always @(posedge clk)
	  if(ena)
	    q <= #1 gen_q(q_pipe[d_width-1], s_pipe[d_width]);

	always @(posedge clk)
	  if(ena)
	    s <= #1 assign_s(s_pipe[d_width], d_pipe[d_width]);
endmodule



