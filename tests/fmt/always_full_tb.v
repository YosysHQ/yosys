module always_full_tb;

    reg clk = 0;
    wire fin;

    always_full uut (.clk(clk), .fin(fin));

    always begin
        #1 clk <= ~clk;

        if (fin) $finish;
    end

endmodule
