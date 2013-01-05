/////////////////////////////////////////////////////////////////////
////                                                             ////
////  USB 1.1 PHY                                                ////
////  RX & DPLL                                                  ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/usb_phy/   ////
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
//  $Id: usb_rx_phy.v,v 1.5 2004/10/19 09:29:07 rudi Exp $
//
//  $Date: 2004/10/19 09:29:07 $
//  $Revision: 1.5 $
//  $Author: rudi $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: usb_rx_phy.v,v $
//               Revision 1.5  2004/10/19 09:29:07  rudi
//               Fixed DPLL alignment in the rx_phy and bit stuffing errors in the tx_phy (if last bit bit was a stuff bit in a packet it was omitted).
//
//               Revision 1.4  2003/12/02 04:56:00  rudi
//               Fixed a bug reported by Karl C. Posch from Graz University of Technology. Thanks Karl !
//
//               Revision 1.3  2003/10/19 18:07:45  rudi
//               - Fixed Sync Error to be only checked/generated during the sync phase
//
//               Revision 1.2  2003/10/19 17:40:13  rudi
//               - Made core more robust against line noise
//               - Added Error Checking and Reporting
//               (See README.txt for more info)
//
//               Revision 1.1.1.1  2002/09/16 14:27:01  rudi
//               Created Directory Structure
//
//
//
//
//
//
//
//

`include "timescale.v"

module usb_rx_phy(	clk, rst, fs_ce,
	
			// Transciever Interface
			rxd, rxdp, rxdn,

			// UTMI Interface
			RxValid_o, RxActive_o, RxError_o, DataIn_o,
			RxEn_i, LineState);

input		clk;
input		rst;
output		fs_ce;
input		rxd, rxdp, rxdn;
output	[7:0]	DataIn_o;
output		RxValid_o;
output		RxActive_o;
output		RxError_o;
input		RxEn_i;
output	[1:0]	LineState;

///////////////////////////////////////////////////////////////////
//
// Local Wires and Registers
//

reg		rxd_s0, rxd_s1,  rxd_s;
reg		rxdp_s0, rxdp_s1, rxdp_s, rxdp_s_r;
reg		rxdn_s0, rxdn_s1, rxdn_s, rxdn_s_r;
reg		synced_d;
wire		k, j, se0;
reg		rxd_r;
reg		rx_en;
reg		rx_active;
reg	[2:0]	bit_cnt;
reg		rx_valid1, rx_valid;
reg		shift_en;
reg		sd_r;
reg		sd_nrzi;
reg	[7:0]	hold_reg;
wire		drop_bit;	// Indicates a stuffed bit
reg	[2:0]	one_cnt;

reg	[1:0]	dpll_state, dpll_next_state;
reg		fs_ce_d;
reg		fs_ce;
wire		change;
wire		lock_en;
reg	[2:0]	fs_state, fs_next_state;
reg		rx_valid_r;
reg		sync_err_d, sync_err;
reg		bit_stuff_err;
reg		se0_r, byte_err;
reg		se0_s;

///////////////////////////////////////////////////////////////////
//
// Misc Logic
//

assign RxActive_o = rx_active;
assign RxValid_o = rx_valid;
assign RxError_o = sync_err | bit_stuff_err | byte_err;
assign DataIn_o = hold_reg;
assign LineState = {rxdn_s1, rxdp_s1};

always @(posedge clk)	rx_en <= RxEn_i;
always @(posedge clk)	sync_err <= !rx_active & sync_err_d;

///////////////////////////////////////////////////////////////////
//
// Synchronize Inputs
//

// First synchronize to the local system clock to
// avoid metastability outside the sync block (*_s0).
// Then make sure we see the signal for at least two
// clock cycles stable to avoid glitches and noise

always @(posedge clk)	rxd_s0  <= rxd;
always @(posedge clk)	rxd_s1  <= rxd_s0;
always @(posedge clk)							// Avoid detecting Line Glitches and noise
	if(rxd_s0 && rxd_s1)	rxd_s <= 1'b1;
	else
	if(!rxd_s0 && !rxd_s1)	rxd_s <= 1'b0;

always @(posedge clk)	rxdp_s0  <= rxdp;
always @(posedge clk)	rxdp_s1  <= rxdp_s0;
always @(posedge clk)	rxdp_s_r <= rxdp_s0 & rxdp_s1;
always @(posedge clk)	rxdp_s   <= (rxdp_s0 & rxdp_s1) | rxdp_s_r;	// Avoid detecting Line Glitches and noise

always @(posedge clk)	rxdn_s0  <= rxdn;
always @(posedge clk)	rxdn_s1  <= rxdn_s0;
always @(posedge clk)	rxdn_s_r <= rxdn_s0 & rxdn_s1;
always @(posedge clk)	rxdn_s   <= (rxdn_s0 & rxdn_s1) | rxdn_s_r;	// Avoid detecting Line Glitches and noise

assign k = !rxdp_s &  rxdn_s;
assign j =  rxdp_s & !rxdn_s;
assign se0 = !rxdp_s & !rxdn_s;

always @(posedge clk)	if(fs_ce)	se0_s <= se0;

///////////////////////////////////////////////////////////////////
//
// DPLL
//

// This design uses a clock enable to do 12Mhz timing and not a
// real 12Mhz clock. Everything always runs at 48Mhz. We want to
// make sure however, that the clock enable is always exactly in
// the middle between two virtual 12Mhz rising edges.
// We monitor rxdp and rxdn for any changes and do the appropiate
// adjustments.
// In addition to the locking done in the dpll FSM, we adjust the
// final latch enable to compensate for various sync registers ...

// Allow lockinf only when we are receiving
assign	lock_en = rx_en;

always @(posedge clk)	rxd_r <= rxd_s;

// Edge detector
assign change = rxd_r != rxd_s;

// DPLL FSM
`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)	dpll_state <= 2'h1;
	else		dpll_state <= dpll_next_state;

always @(dpll_state or lock_en or change)
   begin
	fs_ce_d = 1'b0;
	case(dpll_state)	// synopsys full_case parallel_case
	   2'h0:
		if(lock_en && change)	dpll_next_state = 2'h0;
		else			dpll_next_state = 2'h1;
	   2'h1:begin
		fs_ce_d = 1'b1;
		if(lock_en && change)	dpll_next_state = 2'h3;
		else			dpll_next_state = 2'h2;
		end
	   2'h2:
		if(lock_en && change)	dpll_next_state = 2'h0;
		else			dpll_next_state = 2'h3;
	   2'h3:
		if(lock_en && change)	dpll_next_state = 2'h0;
		else			dpll_next_state = 2'h0;
	endcase
   end

// Compensate for sync registers at the input - allign full speed
// clock enable to be in the middle between two bit changes ...
reg	fs_ce_r1, fs_ce_r2;

always @(posedge clk)	fs_ce_r1 <= fs_ce_d;
always @(posedge clk)	fs_ce_r2 <= fs_ce_r1;
always @(posedge clk)	fs_ce <= fs_ce_r2;


///////////////////////////////////////////////////////////////////
//
// Find Sync Pattern FSM
//

parameter	FS_IDLE	= 3'h0,
		K1	= 3'h1,
		J1	= 3'h2,
		K2	= 3'h3,
		J2	= 3'h4,
		K3	= 3'h5,
		J3	= 3'h6,
		K4	= 3'h7;

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)	fs_state <= FS_IDLE;
	else		fs_state <= fs_next_state;

always @(fs_state or fs_ce or k or j or rx_en or rx_active or se0 or se0_s)
   begin
	synced_d = 1'b0;
	sync_err_d = 1'b0;
	fs_next_state = fs_state;
	if(fs_ce && !rx_active && !se0 && !se0_s)
	   case(fs_state)	// synopsys full_case parallel_case
		FS_IDLE:
		     begin
			if(k && rx_en)	fs_next_state = K1;
		     end
		K1:
		     begin
			if(j && rx_en)	fs_next_state = J1;
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		J1:
		     begin
			if(k && rx_en)	fs_next_state = K2;
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		K2:
		     begin
			if(j && rx_en)	fs_next_state = J2;
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		J2:
		     begin
			if(k && rx_en)	fs_next_state = K3;
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		K3:
		     begin
			if(j && rx_en)	fs_next_state = J3;
			else
			if(k && rx_en)
			   begin
					fs_next_state = FS_IDLE;	// Allow missing first K-J
					synced_d = 1'b1;
			   end
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		J3:
		     begin
			if(k && rx_en)	fs_next_state = K4;
			else
			   begin
					sync_err_d = 1'b1;
					fs_next_state = FS_IDLE;
			   end
		     end
		K4:
		     begin
			if(k)	synced_d = 1'b1;
			fs_next_state = FS_IDLE;
		     end
	   endcase
   end

///////////////////////////////////////////////////////////////////
//
// Generate RxActive
//

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)		rx_active <= 1'b0;
	else
	if(synced_d && rx_en)	rx_active <= 1'b1;
	else
	if(se0 && rx_valid_r)	rx_active <= 1'b0;

always @(posedge clk)
	if(rx_valid)	rx_valid_r <= 1'b1;
	else
	if(fs_ce)	rx_valid_r <= 1'b0;

///////////////////////////////////////////////////////////////////
//
// NRZI Decoder
//

always @(posedge clk)
	if(fs_ce)	sd_r <= rxd_s;

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)		sd_nrzi <= 1'b0;
	else
	if(!rx_active)		sd_nrzi <= 1'b1;
	else
	if(rx_active && fs_ce)	sd_nrzi <= !(rxd_s ^ sd_r);

///////////////////////////////////////////////////////////////////
//
// Bit Stuff Detect
//

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)	one_cnt <= 3'h0;
	else
	if(!shift_en)	one_cnt <= 3'h0;
	else
	if(fs_ce)
	   begin
		if(!sd_nrzi || drop_bit)	one_cnt <= 3'h0;
		else				one_cnt <= one_cnt + 3'h1;
	   end

assign drop_bit = (one_cnt==3'h6);

always @(posedge clk)	bit_stuff_err <= drop_bit & sd_nrzi & fs_ce & !se0 & rx_active; // Bit Stuff Error

///////////////////////////////////////////////////////////////////
//
// Serial => Parallel converter
//

always @(posedge clk)
	if(fs_ce)	shift_en <= synced_d | rx_active;

always @(posedge clk)
	if(fs_ce && shift_en && !drop_bit)
		hold_reg <= {sd_nrzi, hold_reg[7:1]};

///////////////////////////////////////////////////////////////////
//
// Generate RxValid
//

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)		bit_cnt <= 3'b0;
	else
	if(!shift_en)		bit_cnt <= 3'h0;
	else
	if(fs_ce && !drop_bit)	bit_cnt <= bit_cnt + 3'h1;

`ifdef USB_ASYNC_REST
always @(posedge clk or negedge rst)
`else
always @(posedge clk)
`endif
	if(!rst)					rx_valid1 <= 1'b0;
	else
	if(fs_ce && !drop_bit && (bit_cnt==3'h7))	rx_valid1 <= 1'b1;
	else
	if(rx_valid1 && fs_ce && !drop_bit)		rx_valid1 <= 1'b0;

always @(posedge clk)	rx_valid <= !drop_bit & rx_valid1 & fs_ce;

always @(posedge clk)	se0_r <= se0;

always @(posedge clk)	byte_err <= se0 & !se0_r & (|bit_cnt[2:1]) & rx_active;

endmodule

