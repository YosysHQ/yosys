`timescale 1ns / 1ps
module testbench;
  reg clk;
  reg signed [5:0] wire0;
  wire y;

  top uut (.y(y), .clk(clk), .wire0(wire0));

  initial begin
    clk = 0;
    wire0 = 6'b111101;
    forever #5 clk = ~clk;
  end

  initial begin
    #100;
    $display("y = %d", y);
    $finish;
  end
endmodule
