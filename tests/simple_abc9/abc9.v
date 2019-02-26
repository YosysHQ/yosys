module abc9_test001(input a, output o);
assign o = a;
endmodule

module abc9_test002(input [1:0] a, output o);
assign o = a[1];
endmodule

module abc9_test003(input [1:0] a, output [1:0] o);
assign o = a;
endmodule

module abc9_test004(input [1:0] a, output o);
assign o = ^a;
endmodule

module abc9_test005(input [1:0] a, output o, output p);
assign o = ^a;
assign p = ~o;
endmodule

module abc9_test006(input [1:0] a, output [2:0] o);
assign o[0] = ^a;
assign o[1] = ~o[0];
assign o[2] = o[1];
endmodule

module abc9_test007(input a, output o);
wire b, c;
assign c = ~a;
assign b = c;
abc9_test007_sub s(b, o);
endmodule

module abc9_test007_sub(input a, output b);
assign b = a;
endmodule

module abc9_test008(input a, output o);
wire b, c;
assign b = ~a;
assign c = b;
abc9_test008_sub s(b, o);
endmodule

module abc9_test008_sub(input a, output b);
assign b = ~a;
endmodule

module abc9_test009(inout io, input oe);
reg latch;
always @(io or oe)
    if (!oe)
        latch <= io;
assign io = oe ? ~latch : 1'bz;
endmodule

module abc9_test010(inout [7:0] io, input oe);
reg [7:0] latch;
always @(io or oe)
    if (!oe)
        latch <= io;
assign io = oe ? ~latch : 8'bz;
endmodule

// TODO
//module abc9_test011(inout [7:0] io, input oe);
//reg [7:0] latch;
//always @(io or oe)
//    if (!oe)
//        latch[3:0] <= io;
//    else
//        latch[7:4] <= io;
//assign io[3:0] = oe ? ~latch[3:0] : 4'bz;
//assign io[7:4] = !oe ? {latch[4], latch[7:3]} : 4'bz;
//endmodule

// TODO
//module abc9_test012(inout [7:0] io, input oe);
//abc9_test012_sub sub(io, oe);
//endmodule
//
//module abc9_test012_sub(inout [7:0] io, input oe);
//reg [7:0] latch;
//always @(io or oe)
//    if (!oe)
//        latch[3:0] <= io;
//    else
//        latch[7:4] <= io;
//assign io[3:0] = oe ? ~latch[3:0] : 4'bz;
//assign io[7:4] = !oe ? {latch[4], latch[7:3]} : 4'bz;
//endmodule
