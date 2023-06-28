module tb;
    reg clk = 0;

    top uut (.clk(clk));

    always #1 clk <= ~clk;
    initial #20 $finish;
endmodule
