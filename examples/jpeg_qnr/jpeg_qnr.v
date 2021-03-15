/////////////////////////////////////////////////////////////////////
////                                                             ////
////  JPEG Quantization & Rounding Core                          ////
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
//  $Id: jpeg_qnr.v,v 1.3 2002-10-31 12:52:55 rherveille Exp $
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

module jpeg_qnr(clk, ena, rst, dstrb, din, qnt_val, qnt_cnt, dout, douten);

	//
	// parameters
	//
	parameter d_width = 12;
	parameter z_width = 2 * d_width;

	//
	// inputs & outputs
	//
	input clk;                    // system clock
	input ena;                    // clock enable
	input rst;                    // asynchronous active low reset

	input                dstrb;   // present dstrb 1clk cycle before din
	input  [d_width-1:0] din;     // data input
	input  [ 7:0]        qnt_val; // quantization value

	output [ 5:0]        qnt_cnt; // sample number (get quantization value qnt_cnt)
	output [10:0]        dout;    // data output
	output               douten;

	//
	// variables
	//
	wire [z_width-1:0] iz; // intermediate divident value
	wire [d_width-1:0] id; // intermediate dividor value
	wire [d_width  :0] iq; // intermediate result divider
	reg  [d_width  :0] rq; // rounded q-value
	reg  [d_width+3:0] dep;// data enable pipeline

	// generate sample counter
	reg  [5:0] qnt_cnt;
	wire       dcnt     = &qnt_cnt;

	always @(posedge clk or negedge rst)
	  if (~rst)
	     qnt_cnt <= #1 6'h0;
	  else if (dstrb)
	     qnt_cnt <= #1 6'h0;
	  else if (ena)
	     qnt_cnt <= #1 qnt_cnt + 6'h1;

	// generate intermediate dividor/divident values
	assign id = { {(d_width - 8){1'b0}}, qnt_val};
	assign iz = { {(z_width - d_width){din[d_width-1]}}, din};

	// hookup division unit
	div_su #(z_width)
	divider (
		.clk(clk),
		.ena(ena),
		.z(iz),
		.d(id),
		.q(iq),
		.s(),
		.div0(),
		.ovf()
	);

	// round result to the nearest integer
	always @(posedge clk)
	  if (ena)
	    if (iq[0])
	      if (iq[d_width])
	         rq <= #1 iq - 1'h1;
	      else
	         rq <= #1 iq + 1'h1;
	    else
	       rq <= #1 iq;

	// assign dout signal
	assign dout = rq[d_width -1: d_width-11];


	// generate data-out enable signal
	// This is a pipeline, data is not dependant on sample-count
	integer n;
	always @(posedge clk or negedge rst)
	  if (!rst)
	     dep <= #1 0;
	  else if(ena)
	     begin
	         dep[0] <= #1 dstrb;

	         for (n=1; n <= d_width +3; n = n +1)
	             dep[n] <= #1 dep[n-1];
	     end

	assign douten = dep[d_width +3];
endmodule
