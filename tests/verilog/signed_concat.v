`define OUTPUTS(mode) \
    o``mode``0, \
    o``mode``1, \
    o``mode``2, \
    o``mode``3, \
    o``mode``4

module gate(
    input [1:0] iu,
    input signed [1:0] is,
    output [2:0] `OUTPUTS(u),
    output signed [2:0] `OUTPUTS(s)
);
`define INSTANCES(mode) \
    mod m``mode``0({i``mode}, {o``mode``0}); \
    mod m``mode``1($unsigned(i``mode), o``mode``1); \
    mod m``mode``2({i``mode[1:0]}, o``mode``2); \
    mod m``mode``3({$signed(i``mode)}, o``mode``3); \
    mod m``mode``4($unsigned({i``mode}), o``mode``4);
`INSTANCES(u)
`INSTANCES(s)
`undef INSTANCES
endmodule

module gold(
    input [1:0] iu, is,
    output [2:0] `OUTPUTS(u), `OUTPUTS(s)
);
`define INSTANCES(mode) \
    assign o``mode``0 = i``mode; \
    assign o``mode``1 = i``mode; \
    assign o``mode``2 = i``mode; \
    assign o``mode``3 = i``mode; \
    assign o``mode``4 = i``mode;
`INSTANCES(u)
`INSTANCES(s)
`undef INSTANCES
endmodule

module mod(
    input [2:0] inp,
    output [2:0] out
);
    assign out = inp;
endmodule
