module top(input clk);
    reg a = 0;
    reg b = 0;
    wire y;

    sub s (.a(a), .b(b), .y(y));

	always @(posedge clk) begin
        a <= (!a && !b) || (a && !b);
        b <= (a && !b) || (a && b);
    end
endmodule

module sub(input a, input b, output wire y);
    assign y = a & b;

    // Not fit for our purposes: always @* if (a) $display(a, b, y);
    //
    // We compare output against iverilog, but async iverilog $display fires
    // even before values have propagated -- i.e. combinations of a/b/y will be
    // shown where a & b are both 1, but y has not yet taken the value 1.  We
    // don't, so we specify it in the conditional.
    always @* if (y & (y == (a & b))) $display(a, b, y);
endmodule
