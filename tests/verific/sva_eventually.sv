module cover_immediate (input clk, rst);
    cover property (@(posedge clk) disable iff (rst) s_eventually 1'b0);
endmodule

module cover_mixed (input clk, rst);
    always @(posedge clk)
        cover property (disable iff (rst) s_eventually 1'b0);
endmodule

module cover_sequential (input clk, rst);
    always @(posedge clk)
        if (!rst)
            cover property (s_eventually 1'b0);
endmodule

module assert_immediate (input clk, rst);
    assert property (@(posedge clk) disable iff (rst) s_eventually 1'b0);
endmodule

module assert_sequential (input clk, rst);
    always @(posedge clk)
        if (!rst)
            assert property (s_eventually 1'b0);
endmodule

module assert_bounded (input clk);
    assert property (@(posedge clk) s_eventually [1:4] 1'b0);
endmodule

module cover_sequential_disable (input clk, rst, en);
    always @(posedge clk)
        if (en)
            cover property (disable iff (rst) s_eventually 1'b0);
endmodule

module cover_implication_disable (input clk, rst, en);
    always @(posedge clk)
        cover property (disable iff (rst) en |-> s_eventually 1'b0);
endmodule

module cover_and (input clk, rst, en);
    always @(posedge clk)
        cover property (en and s_eventually 1'b0);
endmodule

module cover_if (input clk, rst, en);
    always @(posedge clk)
        cover property (if (en) s_eventually 1'b0);
endmodule

module assert_bounded_implication (input clk, en, a);
    assert property (@(posedge clk) en |-> s_eventually [1:4] a);
endmodule
