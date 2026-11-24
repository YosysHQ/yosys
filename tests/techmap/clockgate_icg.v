module pos_small(input CE, CLK, output GCLK);
    reg ce_latched;
    always @* begin
        if (!CLK) ce_latched = CE;
    end
    assign GCLK = CLK & ce_latched;
endmodule

module neg_small(input CE, CLK, output GCLK);
    reg ce_latched;
    always @* begin
        if (CLK) ce_latched = CE;
    end
    assign GCLK = CLK | !ce_latched;
endmodule
