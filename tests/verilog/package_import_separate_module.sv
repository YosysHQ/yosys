import config_pkg::*;

module top;
  logic [DATA_WIDTH-1:0] data;
  logic [ADDR_WIDTH-1:0] addr;
  logic [2:0] state;
  
  always_comb begin
    case (state)
      IDLE: data = 8'h00;
      START: data = 8'h01;
      DATA: data = 8'h02;
      ODD_PARITY: data = 8'h03;
      STOP: data = 8'h04;
      DONE: data = 8'h05;
      default: data = 8'hFF;
    endcase
  end
endmodule 