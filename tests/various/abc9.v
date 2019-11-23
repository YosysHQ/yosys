module abc9_test027(output reg o);
initial o = 1'b0;
always @*
    o <= ~o;
endmodule

module abc9_test028(input i, output o);
wire w;
unknown u(~i, w);
unknown2 u2(w, o);
endmodule

module abc9_test032(input clk, d, r, output reg q);
initial q = 1'b0;
always @(negedge clk or negedge r)
    if (!r) q <= 1'b0;
    else q <= d;
endmodule
