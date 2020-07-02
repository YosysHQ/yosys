`timescale 1ns/1ps
`default_nettype none

`ifndef VCDFILE
`define VCDFILE "test_arith_tb.vcd"
`endif

module test;

task tbassert(input a, input reg [512:0] s);
begin
    if (a==0) begin
        $display("**********************************************************");
        $display("* ASSERT FAILURE (@%d): %-s", $time, s);
        $display("**********************************************************");
        $dumpflush;
        $finish_and_return(-1);
    end
end
endtask

reg [7:0] a = 0;
reg [7:0] b = 0;
wire [7:0] add;
wire add_cout;
wire [7:0] minus;
wire minus_cout;
wire threshold;

test_arith #(
    .INCREMENT(8),
    .THRESHOLD(16)
) unt (
    .a(a),
    .b(b),
    .add(add),
    .add_cout(add_cout),
    .minus(minus),
    .minus_cout(minus_cout),
    .threshold(threshold)
);

initial begin
    $dumpfile(`VCDFILE);
    $dumpvars;
#0.9
    a = 8'b0000_0000;
    b = 8'b0000_0000;
#0.1
    tbassert(add == 8'b0000_0000, "zero add");
    tbassert(add_cout == 1'b0, "zero add carry");
    tbassert(minus == 8'b0000_0000, "zero subtract");
    tbassert(minus_cout == 1'b0, "zero subtract carry");
    tbassert(threshold == 1'b0, "threshold not met");
#0.9 // 2
    a = 8'b0000_0001;
    b = 8'b0000_0001;
#0.1
    tbassert(add == 8'b0000_0010, "simple add");
    tbassert(add_cout == 1'b0, "simple add carry");
    tbassert(minus == 8'b0000_0000, "simple subtract");
    tbassert(minus_cout == 1'b0, "simple subtract carry");
#0.9 // 3
    a = 8'b1111_1111;
    b = 8'b0000_0001;
#0.1
    tbassert(add == 8'b0000_0000, "overflow add");
    tbassert(add_cout == 1'b1, "overflow add carry");
    tbassert(minus == 8'b1111_1110, "simple subtract carry 2");
    tbassert(minus_cout == 1'b0, "simple subtract carry 2");
#0.9 // 4
    a = 8'b0000_0001;
    b = 8'b1111_1111;
#0.1
    tbassert(add == 8'b0000_0000, "overflow add 2");
    tbassert(add_cout == 1'b1, "overflow add 2 carry");
    tbassert(minus == 8'b0000_0010, "underflow subtract");
    tbassert(minus_cout == 1'b1, "underflow subtract carry");
#0.9 // 5
    a = 8'd8;
#0.1
    tbassert(threshold, "threshold met");
#0.9 // 6
    a = 8'd7;
#0.1
    tbassert(!threshold, "threshold not met");
#1  $finish;
end

endmodule
