module tb;
    reg clk = 0;

    top uut1 (.clk(clk));
    top uut2 (.clk(clk));

    always #1 clk <= ~clk;
    initial #20 $finish;
endmodule
