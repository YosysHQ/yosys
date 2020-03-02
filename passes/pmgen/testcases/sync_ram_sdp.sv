`default_nettype none
module sync_ram_sdp #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=8)
   (input  wire                      clk, write_enable, en,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in_r, address_in_w,
    output logic [DATA_WIDTH-1:0]    data_out);
   
   localparam NUMWORDS = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);
   
   logic [NUMWORDS:0] 		     data_out_r;
   logic [NUMWORDS:0] 		     memory [0:DEPTH];
   
   always_ff @(posedge clk) begin
      if (write_enable)
	memory[address_in_w] <= data_in;
      data_out_r <= memory[address_in_r];
      /*if (en)*/ data_out <= data_out_r;
   end
   
   //assign data_out = data_out_r;
endmodule // sync_ram_sdp
