module counter_tb;

  /* Make a reset pulse and specify dump file */
  reg reset = 0;
  initial begin
     $dumpfile("counter_tb.vcd");
     $dumpvars(0,counter_tb);

     # 0 reset = 1;
     # 4 reset = 0;
     # 36 reset = 1;
     # 4  reset = 0;
     # 6 $finish;
  end
  
  /* Make enable with period of 8 and 6,7 low */
  reg en = 1;
  always begin
    en = 1;
    #6;
    en = 0;
    #2;
  end

  /* Make a regular pulsing clock. */
  reg clk = 0;
  always #1 clk = !clk;
  
  /* UUT */
  wire [2:0] count;
  counter c1 (clk, reset, en, count);

endmodule
