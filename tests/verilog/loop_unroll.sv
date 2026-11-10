module top #(parameter int unsigned NUM = 10) (input logic a, output logic y);
  always_comb begin
    y = a;
    for (int i = 0; i < NUM - 1; i = i + 1)   // PIPE - 1 is unsigned 32-bit: 2^32 - 1 iterations at PIPE = 0
    	y = y ^ 1'b1;
  end
endmodule
