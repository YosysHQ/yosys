
// test_simulation_seq_ff_1_test.v
module f1_test(input in,  input clk, output reg out);
always @(posedge clk)
    out <= in;
endmodule	

// test_simulation_seq_ff_2_test.v
module f2_test(input  in,  input clk,  output reg out);
always @(negedge clk)
   out <= in;
endmodule	
