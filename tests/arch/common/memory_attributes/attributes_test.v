`default_nettype none
module block_ram #(parameter DATA_WIDTH=4, ADDRESS_WIDTH=10)
   (input  wire                      write_enable, clk,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in,
    output wire  [DATA_WIDTH-1:0]    data_out);

   localparam WORD  = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);

   reg [WORD:0] data_out_r;
   reg [WORD:0] memory [0:DEPTH];

   always @(posedge clk) begin
      if (write_enable)
        memory[address_in] <= data_in;
      data_out_r <= memory[address_in];
   end

   assign data_out = data_out_r;
endmodule // block_ram

`default_nettype none
module distributed_ram #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=4)
   (input  wire                      write_enable, clk,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in,
    output wire  [DATA_WIDTH-1:0]    data_out);

   localparam WORD  = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);

   reg [WORD:0] data_out_r;
   reg [WORD:0] memory [0:DEPTH];

   always @(posedge clk) begin
      if (write_enable)
        memory[address_in] <= data_in;
      data_out_r <= memory[address_in];
   end

   assign data_out = data_out_r;
endmodule // distributed_ram

`default_nettype none
module distributed_ram_manual #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=4)
   (input  wire                      write_enable, clk,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in,
    output wire  [DATA_WIDTH-1:0]    data_out);

   localparam WORD  = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);

   reg [WORD:0] data_out_r;
   (* ram_style = "block" *) reg [WORD:0] memory [0:DEPTH];

   always @(posedge clk) begin
      if (write_enable)
        memory[address_in] <= data_in;
      data_out_r <= memory[address_in];
   end

   assign data_out = data_out_r;
endmodule // distributed_ram

`default_nettype none
module distributed_ram_manual_syn #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=4)
   (input  wire                      write_enable, clk,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in,
    output wire  [DATA_WIDTH-1:0]    data_out);

   localparam WORD  = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);

   reg [WORD:0] data_out_r;
   (* synthesis, ram_block *) reg [WORD:0] memory [0:DEPTH];

   always @(posedge clk) begin
      if (write_enable)
        memory[address_in] <= data_in;
      data_out_r <= memory[address_in];
   end

   assign data_out = data_out_r;
endmodule // distributed_ram

