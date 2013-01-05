/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Simple Asynchronous Serial Comm. Device                    ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/sasc/      ////
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
//  $Id: sasc_top.v,v 1.1.1.1 2002/09/16 16:16:42 rudi Exp $
//
//  $Date: 2002/09/16 16:16:42 $
//  $Revision: 1.1.1.1 $
//  $Author: rudi $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: sasc_top.v,v $
//               Revision 1.1.1.1  2002/09/16 16:16:42  rudi
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
Serial IO Interface
===============================
RTS I Request To Send
CTS O Clear to send
TD  I Transmit Data
RD  O Receive Data
*/

module sasc_top(	clk, rst,
	
			// SIO
			rxd_i, txd_o, cts_i, rts_o, 

			// External Baud Rate Generator
			sio_ce, sio_ce_x4,

			// Internal Interface
			din_i, dout_o, re_i, we_i, full_o, empty_o);

input		clk;
input		rst;
input		rxd_i;
output		txd_o;
input		cts_i;
output		rts_o; 
input		sio_ce;
input		sio_ce_x4;
input	[7:0]	din_i;
output	[7:0]	dout_o;
input		re_i, we_i;
output		full_o, empty_o;

///////////////////////////////////////////////////////////////////
//
// Local Wires and Registers
//

parameter	START_BIT	= 1'b0,
		STOP_BIT	= 1'b1,
		IDLE_BIT	= 1'b1;

wire	[7:0]	txd_p;
reg		load;
reg		load_r;
wire		load_e;
reg	[9:0]	hold_reg;
wire		txf_empty;
reg		txd_o;
reg		shift_en;
reg	[3:0]	tx_bit_cnt;
reg		rxd_s, rxd_r;
wire		start;
reg	[3:0]	rx_bit_cnt;
reg		rx_go;
reg	[9:0]	rxr;
reg		rx_valid, rx_valid_r;
wire		rx_we;
wire		rxf_full;
reg		rts_o;
reg		txf_empty_r;
reg		shift_en_r;
reg		rxd_r1, rxd_r2;
wire		lock_en;
reg		change;
reg		rx_sio_ce_d, rx_sio_ce_r1, rx_sio_ce_r2, rx_sio_ce;
reg	[1:0]	dpll_state, dpll_next_state;

///////////////////////////////////////////////////////////////////
//
// IO Fifo's
//

sasc_fifo4 tx_fifo(	.clk(		clk		),
			.rst(		rst		),
			.clr(		1'b0		),
			.din(		din_i		),
			.we(		we_i		),
			.dout(		txd_p		),
			.re(		load_e		),
			.full(		full_o		),
			.empty(		txf_empty	)
			);

sasc_fifo4 rx_fifo(	.clk(		clk		),
			.rst(		rst		),
			.clr(		1'b0		),
			.din(		rxr[9:2]	),
			.we(		rx_we		),
			.dout(		dout_o		),
			.re(		re_i		),
			.full(		rxf_full	),
			.empty(		empty_o		)
			);

///////////////////////////////////////////////////////////////////
//
// Transmit Logic
//
always @(posedge clk)
	if(!rst)	txf_empty_r <= #1 1'b1;
	else
	if(sio_ce)	txf_empty_r <= #1 txf_empty;

always @(posedge clk)
	load <= #1 !txf_empty_r & !shift_en & !cts_i;

always @(posedge clk)
	load_r <= #1 load;

assign load_e = load & sio_ce;

always @(posedge clk)
	if(load_e)		hold_reg <= #1 {STOP_BIT, txd_p, START_BIT};
	else
	if(shift_en & sio_ce)	hold_reg <= #1 {IDLE_BIT, hold_reg[9:1]};

always @(posedge clk)
	if(!rst)				txd_o <= #1 IDLE_BIT;
	else
	if(sio_ce)
		if(shift_en | shift_en_r)	txd_o <= #1 hold_reg[0];
		else				txd_o <= #1 IDLE_BIT;

always @(posedge clk)
        if(!rst)		tx_bit_cnt <= #1 4'h9;
	else
	if(load_e)		tx_bit_cnt <= #1 4'h0;
	else
	if(shift_en & sio_ce)	tx_bit_cnt <= #1 tx_bit_cnt + 4'h1;

always @(posedge clk)
	shift_en <= #1 (tx_bit_cnt != 4'h9);

always @(posedge clk)
	if(!rst)	shift_en_r <= #1 1'b0;
	else
	if(sio_ce)	shift_en_r <= #1 shift_en;

///////////////////////////////////////////////////////////////////
//
// Recieve Logic
//

always @(posedge clk)
	rxd_s <= #1 rxd_i;

always @(posedge clk)
	rxd_r <= #1 rxd_s;

assign start = (rxd_r == IDLE_BIT) & (rxd_s == START_BIT);

always @(posedge clk)
        if(!rst)		rx_bit_cnt <= #1 4'ha;
	else
	if(!rx_go & start)	rx_bit_cnt <= #1 4'h0;
	else
	if(rx_go & rx_sio_ce)	rx_bit_cnt <= #1 rx_bit_cnt + 4'h1;

always @(posedge clk)
	rx_go <= #1 (rx_bit_cnt != 4'ha);

always @(posedge clk)
	rx_valid <= #1 (rx_bit_cnt == 4'h9);

always @(posedge clk)
	rx_valid_r <= #1 rx_valid;

assign rx_we = !rx_valid_r & rx_valid & !rxf_full;

always @(posedge clk)
	if(rx_go & rx_sio_ce)	rxr <= {rxd_s, rxr[9:1]};

always @(posedge clk)
	rts_o <= #1 rxf_full;

///////////////////////////////////////////////////////////////////
//
// Reciever DPLL
//

// Uses 4x baud clock to lock to incoming stream

// Edge detector
always @(posedge clk)
	if(sio_ce_x4)	rxd_r1 <= #1 rxd_s;

always @(posedge clk)
	if(sio_ce_x4)	rxd_r2 <= #1 rxd_r1;

always @(posedge clk)
	if(!rst)		change <= #1 1'b0;
	else
	if(rxd_r != rxd_s)	change <= #1 1'b1;
	else
	if(sio_ce_x4)		change <= #1 1'b0;

// DPLL FSM
always @(posedge clk or negedge rst)
	if(!rst)	dpll_state <= #1 2'h1;
	else
	if(sio_ce_x4)	dpll_state <= #1 dpll_next_state;

always @(dpll_state or change)
   begin
	rx_sio_ce_d = 1'b0;
	case(dpll_state)
	   2'h0:
		if(change)	dpll_next_state = 3'h0;
		else		dpll_next_state = 3'h1;
	   2'h1:begin
		rx_sio_ce_d = 1'b1;
		if(change)	dpll_next_state = 3'h3;
		else		dpll_next_state = 3'h2;
		end
	   2'h2:
		if(change)	dpll_next_state = 3'h0;
		else		dpll_next_state = 3'h3;
	   2'h3:
		if(change)	dpll_next_state = 3'h0;
		else		dpll_next_state = 3'h0;
	endcase
   end

// Compensate for sync registers at the input - allign sio 
// clock enable to be in the middle between two bit changes ...
always @(posedge clk)
	rx_sio_ce_r1 <= #1 rx_sio_ce_d;

always @(posedge clk)
	rx_sio_ce_r2 <= #1 rx_sio_ce_r1;

always @(posedge clk)
	rx_sio_ce <= #1 rx_sio_ce_r1 & !rx_sio_ce_r2;

endmodule


