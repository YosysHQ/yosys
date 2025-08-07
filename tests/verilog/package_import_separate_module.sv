import package_import_separate::*;

module package_import_separate_module;
  logic [DATAWIDTH-1:0] data;
  logic [ADDRWIDTH-1:0] addr;
  logic [2:0] state;

  always_comb begin
    case (state)
      IDLE: data = 8'h00;
      START: data = 8'h01;
      DATA: data = 8'h02;
      STOP: data = 8'h04;
      DONE: data = 8'h05;
      default: data = 8'hFF;
    endcase
  end

endmodule
