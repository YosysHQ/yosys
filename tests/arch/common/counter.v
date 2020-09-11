module top ( out, clk, reset );
    output [7:0] out;
    input clk, reset;
    reg [7:0] out;

    always @(posedge clk, posedge reset)
      if (reset)
          out <= 8'b0;
      else
          out <= out + 1;
endmodule
