(* cxxrtl_blackbox *)
module blackbox(...);
    (* cxxrtl_edge = "p" *)
    input clk;

    (* cxxrtl_sync *)
    output [7:0] out1;

    (* cxxrtl_sync *)
    output [7:0] out2;
endmodule

module unconnected_output(
    input  clk,
           in,
    output out
);
    blackbox bb (
        .clock (clock),
        .in    (in),
        .out1  (out),
        .out2  (/* unconnected */),
    );
endmodule
