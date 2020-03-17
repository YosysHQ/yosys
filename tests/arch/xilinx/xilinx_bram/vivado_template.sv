`default_nettype none
// This RAM is derived from Vivado's Synthesis template, with another
// register for Yosys to infer a BRAM instead of LUT due "async read output"
module ram_vivado #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=8)
   (input  wire                    clk, write_enable, en, rst,
    input wire [DATA_WIDTH-1:0]    data_in,
    input wire [ADDRESS_WIDTH-1:0] address_in_r, address_in_w,
    output logic [DATA_WIDTH-1:0]  data_out);
   
   localparam NUMWORDS = (DATA_WIDTH-1);
   localparam DEPTH = (2**ADDRESS_WIDTH-1);
   
   logic [NUMWORDS:0] 		   data_out_r;
   logic [NUMWORDS:0] 		   memory [0:DEPTH];
   
   always_ff @(posedge clk) begin
      if (en) begin
	 if (write_enable)
	   memory[address_in_w] <= data_in;
	 data_out_r <= memory[address_in_r];
`ifdef WITH_RESET
	 if (rst) data_out <= 0;
	 else data_out <= data_out_r;
`else
         data_out <= data_out_r;
`endif
      end
   end
endmodule // ram_vivado
// There are still suboptimal inference when using both en and rst AND 
// with more than one BRAM memory
