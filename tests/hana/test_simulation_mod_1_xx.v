module test(in1, in2, out);
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

