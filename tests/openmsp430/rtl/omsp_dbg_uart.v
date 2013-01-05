//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
//
// *File Name: omsp_dbg_uart.v
// 
// *Module Description:
//                       Debug UART communication interface (8N1, Half-duplex)
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 134 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2012-03-22 21:31:06 +0100 (Thu, 22 Mar 2012) $
//----------------------------------------------------------------------------
`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_defines.v"
`endif

module  omsp_dbg_uart (

// OUTPUTs
    dbg_addr,                       // Debug register address
    dbg_din,                        // Debug register data input
    dbg_rd,                         // Debug register data read
    dbg_uart_txd,                   // Debug interface: UART TXD
    dbg_wr,                         // Debug register data write
			     
// INPUTs
    dbg_clk,                        // Debug unit clock
    dbg_dout,                       // Debug register data output
    dbg_rd_rdy,                     // Debug register data is ready for read
    dbg_rst,                        // Debug unit reset
    dbg_uart_rxd,                   // Debug interface: UART RXD
    mem_burst,                      // Burst on going
    mem_burst_end,                  // End TX/RX burst
    mem_burst_rd,                   // Start TX burst
    mem_burst_wr,                   // Start RX burst
    mem_bw                          // Burst byte width
);

// OUTPUTs
//=========
output        [5:0] dbg_addr;       // Debug register address
output       [15:0] dbg_din;        // Debug register data input
output              dbg_rd;         // Debug register data read
output              dbg_uart_txd;   // Debug interface: UART TXD
output              dbg_wr;         // Debug register data write

// INPUTs
//=========
input               dbg_clk;        // Debug unit clock
input        [15:0] dbg_dout;       // Debug register data output
input               dbg_rd_rdy;     // Debug register data is ready for read
input               dbg_rst;        // Debug unit reset
input               dbg_uart_rxd;   // Debug interface: UART RXD
input               mem_burst;      // Burst on going
input               mem_burst_end;  // End TX/RX burst
input               mem_burst_rd;   // Start TX burst
input               mem_burst_wr;   // Start RX burst
input               mem_bw;         // Burst byte width


//=============================================================================
// 1)  UART RECEIVE LINE SYNCHRONIZTION & FILTERING
//=============================================================================

// Synchronize RXD input
//--------------------------------
`ifdef SYNC_DBG_UART_RXD

    wire uart_rxd_n;

    omsp_sync_cell sync_cell_uart_rxd (
        .data_out  (uart_rxd_n),
        .data_in   (~dbg_uart_rxd),
        .clk       (dbg_clk),
        .rst       (dbg_rst)
    );
    wire uart_rxd = ~uart_rxd_n;
`else
    wire uart_rxd = dbg_uart_rxd;
`endif
   
// RXD input buffer
//--------------------------------
reg  [1:0] rxd_buf;
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst) rxd_buf <=  2'h3;
  else         rxd_buf <=  {rxd_buf[0], uart_rxd};

// Majority decision
//------------------------
reg        rxd_maj;

wire       rxd_maj_nxt = (uart_rxd   & rxd_buf[0]) |
			 (uart_rxd   & rxd_buf[1]) |
			 (rxd_buf[0] & rxd_buf[1]);
   
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst) rxd_maj <=  1'b1;
  else         rxd_maj <=  rxd_maj_nxt;

wire rxd_s    =  rxd_maj;
wire rxd_fe   =  rxd_maj & ~rxd_maj_nxt;
wire rxd_re   = ~rxd_maj &  rxd_maj_nxt;
wire rxd_edge =  rxd_maj ^  rxd_maj_nxt;
   
//=============================================================================
// 2)  UART STATE MACHINE
//=============================================================================

// Receive state
//------------------------
reg   [2:0] uart_state;
reg   [2:0] uart_state_nxt;

wire        sync_done;
wire        xfer_done;
reg  [19:0] xfer_buf;
wire [19:0] xfer_buf_nxt;

// State machine definition
parameter  RX_SYNC  = 3'h0;
parameter  RX_CMD   = 3'h1;
parameter  RX_DATA1 = 3'h2;
parameter  RX_DATA2 = 3'h3;
parameter  TX_DATA1 = 3'h4;
parameter  TX_DATA2 = 3'h5;

// State transition
always @(uart_state or xfer_buf_nxt or mem_burst or mem_burst_wr or mem_burst_rd or mem_burst_end or mem_bw)
  case (uart_state)
    RX_SYNC  : uart_state_nxt =  RX_CMD;
    RX_CMD   : uart_state_nxt =  mem_burst_wr                ?
                                (mem_bw                      ? RX_DATA2 : RX_DATA1) :
                                 mem_burst_rd                ?
                                (mem_bw                      ? TX_DATA2 : TX_DATA1) :
                                (xfer_buf_nxt[`DBG_UART_WR]  ?
                                (xfer_buf_nxt[`DBG_UART_BW]  ? RX_DATA2 : RX_DATA1) :
                                (xfer_buf_nxt[`DBG_UART_BW]  ? TX_DATA2 : TX_DATA1));
    RX_DATA1 : uart_state_nxt =  RX_DATA2;
    RX_DATA2 : uart_state_nxt = (mem_burst & ~mem_burst_end) ?
                                (mem_bw                      ? RX_DATA2 : RX_DATA1) :
                                 RX_CMD;
    TX_DATA1 : uart_state_nxt =  TX_DATA2;
    TX_DATA2 : uart_state_nxt = (mem_burst & ~mem_burst_end) ?
                                (mem_bw                      ? TX_DATA2 : TX_DATA1) :
                                 RX_CMD;
  // pragma coverage off
    default  : uart_state_nxt =  RX_CMD;
  // pragma coverage on
  endcase
   
// State machine
always @(posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                          uart_state <= RX_SYNC;
  else if (xfer_done    | sync_done |
           mem_burst_wr | mem_burst_rd) uart_state <= uart_state_nxt;

// Utility signals
wire cmd_valid = (uart_state==RX_CMD) & xfer_done;
wire rx_active = (uart_state==RX_DATA1) | (uart_state==RX_DATA2) | (uart_state==RX_CMD);
wire tx_active = (uart_state==TX_DATA1) | (uart_state==TX_DATA2);

   
//=============================================================================
// 3)  UART SYNCHRONIZATION
//=============================================================================
// After DBG_RST, the host needs to fist send a synchronization character (0x80)
// If this feature doesn't work properly, it is possible to disable it by
// commenting the DBG_UART_AUTO_SYNC define in the openMSP430.inc file.

reg        sync_busy;
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                             sync_busy <=  1'b0;
  else if ((uart_state==RX_SYNC) & rxd_fe) sync_busy <=  1'b1;
  else if ((uart_state==RX_SYNC) & rxd_re) sync_busy <=  1'b0;

assign sync_done =  (uart_state==RX_SYNC) & rxd_re & sync_busy;

`ifdef DBG_UART_AUTO_SYNC

reg [`DBG_UART_XFER_CNT_W+2:0] sync_cnt;
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                                     sync_cnt <=  {{`DBG_UART_XFER_CNT_W{1'b1}}, 3'b000};
  else if (sync_busy | (~sync_busy & sync_cnt[2])) sync_cnt <=  sync_cnt+{{`DBG_UART_XFER_CNT_W+2{1'b0}}, 1'b1};

wire [`DBG_UART_XFER_CNT_W-1:0] bit_cnt_max = sync_cnt[`DBG_UART_XFER_CNT_W+2:3];
`else
wire [`DBG_UART_XFER_CNT_W-1:0] bit_cnt_max = `DBG_UART_CNT;
`endif
   
   
//=============================================================================
// 4)  UART RECEIVE / TRANSMIT
//=============================================================================
   
// Transfer counter
//------------------------
reg                      [3:0] xfer_bit;
reg [`DBG_UART_XFER_CNT_W-1:0] xfer_cnt;

wire       txd_start    = dbg_rd_rdy | (xfer_done & (uart_state==TX_DATA1));
wire       rxd_start    = (xfer_bit==4'h0) & rxd_fe & ((uart_state!=RX_SYNC));
wire       xfer_bit_inc = (xfer_bit!=4'h0) & (xfer_cnt=={`DBG_UART_XFER_CNT_W{1'b0}});
assign     xfer_done    = rx_active ? (xfer_bit==4'ha) : (xfer_bit==4'hb);
   
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                       xfer_bit <=  4'h0;
  else if (txd_start | rxd_start)    xfer_bit <=  4'h1;
  else if (xfer_done)                xfer_bit <=  4'h0;
  else if (xfer_bit_inc)             xfer_bit <=  xfer_bit+4'h1;

always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                       xfer_cnt <=  {`DBG_UART_XFER_CNT_W{1'b0}};
  else if (rx_active & rxd_edge)     xfer_cnt <=  {1'b0, bit_cnt_max[`DBG_UART_XFER_CNT_W-1:1]};
  else if (txd_start | xfer_bit_inc) xfer_cnt <=  bit_cnt_max;
  else if (|xfer_cnt)                xfer_cnt <=  xfer_cnt+{`DBG_UART_XFER_CNT_W{1'b1}};


// Receive/Transmit buffer
//-------------------------
assign xfer_buf_nxt =  {rxd_s, xfer_buf[19:1]};

always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)           xfer_buf <=  20'h00000;
  else if (dbg_rd_rdy)   xfer_buf <=  {1'b1, dbg_dout[15:8], 2'b01, dbg_dout[7:0], 1'b0};
  else if (xfer_bit_inc) xfer_buf <=  xfer_buf_nxt;


// Generate TXD output
//------------------------
reg dbg_uart_txd;
   
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)                       dbg_uart_txd <=  1'b1;
  else if (xfer_bit_inc & tx_active) dbg_uart_txd <=  xfer_buf[0];

 
//=============================================================================
// 5) INTERFACE TO DEBUG REGISTERS
//=============================================================================

reg [5:0] dbg_addr;
 always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)        dbg_addr <=  6'h00;
  else if (cmd_valid) dbg_addr <=  xfer_buf_nxt[`DBG_UART_ADDR];

reg       dbg_bw;
always @ (posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst)        dbg_bw   <=  1'b0;
  else if (cmd_valid) dbg_bw   <=  xfer_buf_nxt[`DBG_UART_BW];

wire        dbg_din_bw =  mem_burst  ? mem_bw : dbg_bw;

wire [15:0] dbg_din    =  dbg_din_bw ? {8'h00,           xfer_buf_nxt[18:11]} :
                                       {xfer_buf_nxt[18:11], xfer_buf_nxt[9:2]};
wire        dbg_wr     = (xfer_done & (uart_state==RX_DATA2));
wire        dbg_rd     = mem_burst ? (xfer_done & (uart_state==TX_DATA2)) :
                                     (cmd_valid & ~xfer_buf_nxt[`DBG_UART_WR]) | mem_burst_rd;

	    
   
endmodule // omsp_dbg_uart

`ifdef OMSP_NO_INCLUDE
`else
`include "openMSP430_undefines.v"
`endif
