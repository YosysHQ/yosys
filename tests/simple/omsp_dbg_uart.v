
module  omsp_dbg_uart (dbg_clk, dbg_rst, mem_burst, cmd_valid);

input dbg_clk;
input dbg_rst;
input mem_burst;
output cmd_valid;

reg [2:0] uart_state;
reg [2:0] uart_state_nxt;

wire xfer_done;

parameter  RX_SYNC  = 3'h0;
parameter  RX_CMD   = 3'h1;
parameter  RX_DATA = 3'h2;

always @(uart_state or mem_burst)
  case (uart_state)
    RX_SYNC  : uart_state_nxt =  RX_CMD;
    RX_CMD   : uart_state_nxt =  mem_burst ? RX_DATA : RX_SYNC;
    RX_DATA : uart_state_nxt =  RX_SYNC;
    default  : uart_state_nxt =  RX_CMD;
  endcase

always @(posedge dbg_clk or posedge dbg_rst)
  if (dbg_rst) uart_state <= RX_SYNC;
  else if (xfer_done | mem_burst) uart_state <= uart_state_nxt;

assign cmd_valid = (uart_state==RX_CMD) & xfer_done;
assign xfer_done = uart_state!=RX_SYNC;

endmodule

