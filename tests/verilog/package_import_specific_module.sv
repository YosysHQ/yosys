import package_import_specific::DATA_WIDTH;
import package_import_specific::IDLE;

module package_import_specific_module;
  logic [DATA_WIDTH-1:0] data;
  logic [3:0] addr;
  logic [2:0] state;

  always_comb begin
    case (state)
      IDLE: data = 8'h00;
      default: data = 8'hFF;
    endcase
  end

endmodule
