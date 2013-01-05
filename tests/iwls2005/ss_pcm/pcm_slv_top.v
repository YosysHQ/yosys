/////////////////////////////////////////////////////////////////////
////                                                             ////
////  PCM IO Slave Module                                        ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/ss_pcm/    ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000-2002 Rudolf Usselmann                    ////
////                         www.asics.ws                        ////
////                         rudi@asics.ws                       ////
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
//  $Id: pcm_slv_top.v,v 1.2 2002/09/17 15:32:50 rudi Exp $
//
//  $Date: 2002/09/17 15:32:50 $
//  $Revision: 1.2 $
//  $Author: rudi $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: pcm_slv_top.v,v $
//               Revision 1.2  2002/09/17 15:32:50  rudi
//               *** empty log message ***
//
//               Revision 1.1.1.1  2002/09/17 15:17:25  rudi
//               Initial Checkin
//
//
//
//
//
//
//
//

`include "timescale.v"

/*
PCM Interface
===============================
PCM_CLK
PCM_SYNC
PCM_DIN
PCM_DOUT
*/

module pcm_slv_top(	clk, rst,
	
			ssel,

			// PCM
			pcm_clk_i, pcm_sync_i, pcm_din_i, pcm_dout_o,

			// Internal Interface
			din_i, dout_o, re_i, we_i);

input		clk, rst;
input	[2:0]	ssel;	// Number of bits to delay (0-7)
input		pcm_clk_i, pcm_sync_i, pcm_din_i;
output		pcm_dout_o;
input	[7:0]	din_i;
output	[7:0]	dout_o;
input		re_i;
input	[1:0]	we_i;

///////////////////////////////////////////////////////////////////
//
// Local Wires and Registers
//

reg		pclk_t, pclk_s, pclk_r;
wire		pclk_ris, pclk_fal;
reg		psync;
reg		pcm_sync_r1, pcm_sync_r2, pcm_sync_r3;
reg		tx_go;
wire		tx_data_le;
reg	[15:0]	tx_hold_reg;
reg	[7:0]	tx_hold_byte_h, tx_hold_byte_l;
reg	[3:0]	tx_cnt;
wire		tx_done;
reg	[15:0]	rx_hold_reg, rx_reg;
wire		rx_data_le;
reg		rxd_t, rxd;
reg		tx_go_r1, tx_go_r2;
reg	[7:0]	psa;

///////////////////////////////////////////////////////////////////
//
// Misc Logic
//

always @(posedge clk)
	pclk_t <= #1 pcm_clk_i;

always @(posedge clk)
	pclk_s <= #1 pclk_t;

always @(posedge clk)
	pclk_r <= #1 pclk_s;

assign pclk_ris = !pclk_r &  pclk_s;
assign pclk_fal =  pclk_r & !pclk_s;

///////////////////////////////////////////////////////////////////
//
// Retrieve Sync Signal
//

always @(posedge clk)	// Latch it at falling edge
	if(pclk_fal)	pcm_sync_r1 <= #1 pcm_sync_i;

always @(posedge clk)	// resync to rising edge
	if(pclk_ris)	psa <= #1 {psa[6:0], pcm_sync_r1};

always @(posedge clk)	//delay bit N
	pcm_sync_r2 <= #1 psa[ssel];

always @(posedge clk)	// edge detector
	pcm_sync_r3 <= #1 pcm_sync_r2;

always @(posedge clk)
	psync <= #1 !pcm_sync_r3 & pcm_sync_r2;

///////////////////////////////////////////////////////////////////
//
// Transmit Logic
//

assign tx_data_le = tx_go & pclk_ris;

always @(posedge clk)
	if(we_i[1])	tx_hold_byte_h <= #1 din_i;

always @(posedge clk)
	if(we_i[0])	tx_hold_byte_l <= #1 din_i;

always @(posedge clk)
	if(!rst)	tx_go <= #1 1'b0;
	else
	if(psync)	tx_go <= #1 1'b1;
	else
	if(tx_done)	tx_go <= #1 1'b0;

always @(posedge clk)
	if(!rst)	tx_hold_reg <= #1 16'h0;
	else
	if(psync)	tx_hold_reg <= #1 {tx_hold_byte_h, tx_hold_byte_l};
	else
	if(tx_data_le)	tx_hold_reg <= #1 {tx_hold_reg[14:0],1'b0};

assign	pcm_dout_o = tx_hold_reg[15];
	
always @(posedge clk)
	if(!rst)	tx_cnt <= #1 4'h0;
	else
	if(tx_data_le)	tx_cnt <= tx_cnt + 4'h1;

assign tx_done = (tx_cnt == 4'hf) & tx_data_le;

///////////////////////////////////////////////////////////////////
//
// Recieve Logic
//

always @(posedge clk)
	if(pclk_ris)	tx_go_r1 <= #1 tx_go;

always @(posedge clk)
	if(pclk_ris)	tx_go_r2 <= #1 tx_go_r1;

// Receive is in sync with transmit ...
always @(posedge clk)
	if(pclk_fal)	rxd_t <= #1 pcm_din_i;

always @(posedge clk)
	rxd <= #1 rxd_t;

assign rx_data_le = (tx_go_r1 | tx_go) & pclk_fal;

always @(posedge clk)
	if(!rst)	rx_hold_reg <= #1 16'h0;
	else
	if(rx_data_le)	rx_hold_reg <= #1 {rx_hold_reg[14:0], rxd};

always @(posedge clk)
	if(!rst)				rx_reg <= #1 16'h0;
	else
	if(tx_go_r1 & !tx_go & pclk_ris)	rx_reg <= #1 rx_hold_reg;

assign dout_o = re_i ? rx_reg[15:8] : rx_reg[7:0];

endmodule

