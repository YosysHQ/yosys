
`default_nettype none
module sync_ram_sdp_dc #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
   (input  wire                      clkw, clkr, write_enable,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in_r, address_in_w,
    output wire  [DATA_WIDTH-1:0]    data_out);

  localparam WORD  = (DATA_WIDTH-1);
  localparam DEPTH = (2**ADDRESS_WIDTH-1);

  reg [WORD:0] data_out_r;
  reg [WORD:0] memory [0:DEPTH];

  always @(posedge clkw) begin
    if (write_enable)
      memory[address_in_w] <= data_in;
  end
  always @(posedge clkr) begin
    data_out_r <= memory[address_in_r];
  end

  assign data_out = data_out_r;

endmodule // sync_ram_sdp_dc
