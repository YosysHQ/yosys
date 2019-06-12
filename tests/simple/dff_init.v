module dff0_test(n1, n1_inv, clk);
  input clk;
  output n1;
  reg n1 = 32'd0;
  output n1_inv;
  always @(posedge clk)
      n1 <= n1_inv;
  assign n1_inv = ~n1;
endmodule

module dff1_test(n1, n1_inv, clk);
  input clk;
  (* init = 32'd1 *)
  output n1;
  reg n1 = 32'd1;
  output n1_inv;
  always @(posedge clk)
      n1 <= n1_inv;
  assign n1_inv = ~n1;
endmodule

module dff0a_test(n1, n1_inv, clk);
  input clk;
  (* init = 32'd0 *) // Must be consistent with reg initialiser below
  output n1;
  reg n1 = 32'd0;
  output n1_inv;
  always @(posedge clk)
      n1 <= n1_inv;
  assign n1_inv = ~n1;
endmodule

module dff1a_test(n1, n1_inv, clk);
  input clk;
  (* init = 32'd1 *) // Must be consistent with reg initialiser below
  output n1;
  reg n1 = 32'd1;
  output n1_inv;
  always @(posedge clk)
      n1 <= n1_inv;
  assign n1_inv = ~n1;
endmodule

module dff_test_997 (y, clk, wire4);
// https://github.com/YosysHQ/yosys/issues/997
   output wire [1:0] y;
   input             clk;
   input signed      wire4;
   reg [1:0]  reg10 = 0;
   always @(posedge clk) begin
      reg10 <= wire4;
   end
   assign y = reg10;
endmodule
