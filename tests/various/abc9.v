module abc9_test027(output reg o);
initial o = 1'b0;
always @*
    o <= ~o;
endmodule

module abc9_test028(input i, output o);
unknown u(~i, o);
endmodule
