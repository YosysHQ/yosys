// test_simulation_mod_1_xx.v
module f1_test(in1, in2, out);
input in1;
input in2;
output out;

wire  synth_net_0;
wire  synth_net_1;
BUF synth_BUF_0(.in(synth_net_1), .out(out
    ));
DIV1 synth_DIV(.in1(in1), .in2(in2), .rem(synth_net_0), .out(synth_net_1
    ));
endmodule

// test_simulation_always_31_tt.v
module f2_test(clk, cond, data);
input cond;
input clk;
output data;

wire  synth_net;
wire  synth_net_0;
wire  synth_net_1;
wire  synth_net_2;

wire  synth_net_3;
wire  synth_net_4;
wire  synth_net_5;
wire  synth_net_6;

wire  synth_net_7;
wire  synth_net_8;
wire  synth_net_9;
wire  synth_net_10;

wire  synth_net_11;
wire  tmp;
AND2 synth_AND(.in({synth_net_0, synth_net_1}), .
    out(synth_net_2));
AND2 synth_AND_0(.in({synth_net_3, synth_net_4}), .out(
    synth_net_5));
AND2 synth_AND_1(.in({synth_net_6, synth_net_7}), .out(
    synth_net_8));
AND2 synth_AND_2(.in({synth_net_9, synth_net_10}), .out(
    synth_net_11));
BUF synth_BUF(.in(synth_net), .out(synth_net_0));
BUF 
    synth_BUF_0(.in(data), .out(synth_net_3));
BUF synth_BUF_1(.in(synth_net_8)
    , .out(tmp));
BUF synth_BUF_2(.in(tmp), .out(synth_net_9));
MUX2 synth_MUX(.
    in({synth_net_2, synth_net_5}), .select(cond), .out(synth_net_6));
MUX2 
    synth_MUX_0(.in({synth_net_1, synth_net_4}), .select(cond), .out(synth_net_7
    ));
FF synth_FF(.d(synth_net_11), .clk(clk), .q(data));
VCC synth_VCC(.out(
    synth_net));
VCC synth_VCC_0(.out(synth_net_1));
VCC synth_VCC_1(.out(
    synth_net_4));
VCC synth_VCC_2(.out(synth_net_10));
endmodule

