module always_full_tb;

    reg clk = 0;

    always_full uut (.clk(clk));

    always begin
        #1 clk <= ~clk;
        #1 $finish;
    end

endmodule
