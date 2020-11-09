/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Non-restoring signed by unsigned divider                   ////
////  Uses the non-restoring unsigned by unsigned divider        ////
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
//  $Id: div_su.v,v 1.3 2002-10-31 12:52:54 rherveille Exp $
//
//  $Date: 2002-10-31 12:52:54 $
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

module div_su(clk, ena, z, d, q, s, div0, ovf);

	//
	// parameters
	//
	parameter z_width = 16;
	parameter d_width = z_width /2;
	
	//
	// inputs & outputs
	//
	input clk;              // system clock
	input ena;              // clock enable

	input  [z_width-1:0] z; // divident
	input  [d_width-1:0] d; // divisor
	output [d_width  :0] q; // quotient
	output [d_width-1:0] s; // remainder
	output div0;
	output ovf;

	reg [d_width :0] q;
	reg [d_width-1:0] s;
	reg div0;
	reg ovf;

	//
	// variables
	//
	reg [z_width -1:0] iz;
	reg [d_width -1:0] id;
	reg [d_width +1:0] spipe;

	wire [d_width -1:0] iq, is;
	wire                idiv0, iovf;

	//
	// module body
	//

	// delay d
	always @(posedge clk)
	  if (ena)
	    id <= #1 d;

	// check z, take abs value
	always @(posedge clk)
	  if (ena)
	    if (z[z_width-1])
	       iz <= #1 ~z +1'h1;
	    else
	       iz <= #1 z;

	// generate spipe (sign bit pipe)
	integer n;
	always @(posedge clk)
	  if(ena)
	  begin
	      spipe[0] <= #1 z[z_width-1];

	      for(n=1; n <= d_width+1; n=n+1)
	         spipe[n] <= #1 spipe[n-1];
	  end

	// hookup non-restoring divider
	div_uu #(z_width, d_width)
	divider (
		.clk(clk),
		.ena(ena),
		.z(iz),
		.d(id),
		.q(iq),
		.s(is),
		.div0(idiv0),
		.ovf(iovf)
	);

	// correct divider results if 'd' was negative
	always @(posedge clk)
	  if(ena)
	    if(spipe[d_width+1])
	    begin
	        q <= #1 (~iq) + 1'h1;
	        s <= #1 (~is) + 1'h1;
	    end
	    else
	    begin
	        q <= #1 {1'b0, iq};
	        s <= #1 {1'b0, is};
	    end

	// delay flags same as results
	always @(posedge clk)
	  if(ena)
	  begin
	      div0 <= #1 idiv0;
	      ovf  <= #1 iovf;
	  end
endmodule
