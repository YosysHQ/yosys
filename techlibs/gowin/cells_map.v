//TODO all DFF* have INIT

// DFFN      D Flip-Flop with Negative-Edge Clock
module  \$_DFF_N_ (input D, C, output Q); DFFN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C)); endmodule
// DFF       D Flip-Flop
module  \$_DFF_P_ #(parameter INIT = 1'b0) (input D, C, output Q); DFF  #(.INIT(INIT)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C)); endmodule

// DFFE      D Flip-Flop with Clock Enable
module  \$_DFFE_PP_ (input D, C, E, output Q); DFFE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(E)); endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q); DFFE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(!E)); endmodule

// DFFNE     D Flip-Flop with Negative-Edge Clock and Clock Enable
module  \$_DFFE_NP_ (input D, C, E, output Q); DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(E)); endmodule
module  \$_DFFE_NN_ (input D, C, E, output Q); DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(!E)); endmodule

// DFFR      D Flip-Flop with Synchronous Reset
module  \$__DFFS_PN0_ (input D, C, R, output Q); DFFR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(!R)); endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q); DFFR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R)); endmodule

// DFFNR     D Flip-Flop with Negative-Edge Clock and Synchronous Reset
module  \$__DFFS_NN0_ (input D, C, R, output Q); DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(!R)); endmodule
module  \$__DFFS_NP0_ (input D, C, R, output Q); DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R)); endmodule

// DFFRE     D Flip-Flop with Clock Enable and Synchronous Reset
module  \$__DFFSE_PN0 (input D, C, R, E, output Q); DFFRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(!R), .CE(E)); endmodule
module  \$__DFFSE_PP0 (input D, C, R, E, output Q); DFFRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R), .CE(!E)); endmodule

// DFFNRE    D Flip-Flop with Negative-Edge Clock,Clock Enable, and Synchronous Reset
module  \$__DFFNSE_PN0 (input D, C, R, E, output Q); DFFNRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(!R), .CE(E)); endmodule
module  \$__DFFNSE_PP0 (input D, C, R, E, output Q); DFFNRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R), .CE(!E)); endmodule

// DFFS      D Flip-Flop with Synchronous Set
module  \$__DFFS_PN1_ (input D, C, R, output Q); DFFS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(!R)); endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q); DFFS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R)); endmodule

// DFFNS     D Flip-Flop with Negative-Edge Clock and Synchronous Set
module  \$__DFFS_NN1_ (input D, C, R, output Q); DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(!R)); endmodule
module  \$__DFFS_NP1_ (input D, C, R, output Q); DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R)); endmodule

// DFFSE     D Flip-Flop with Clock Enable and Synchronous Set
module  \$__DFFSE_PN1 (input D, C, R, E, output Q); DFFSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(!R), .CE(E)); endmodule
module  \$__DFFSE_PP1 (input D, C, R, E, output Q); DFFSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R), .CE(!E)); endmodule

// DFFNSE    D Flip-Flop with Negative-Edge Clock,Clock Enable,and Synchronous Set
module  \$__DFFSE_NN1 (input D, C, R, E, output Q); DFFNSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(!R), .CE(E)); endmodule
module  \$__DFFSE_NP1 (input D, C, R, E, output Q); DFFNSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R), .CE(!E)); endmodule

// DFFP      D Flip-Flop with Asynchronous Preset
module  \$_DFF_PP1_ (input D, C, R, output Q); DFFP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); DFFP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(!R)); endmodule

// DFFNP     D Flip-Flop with Negative-Edge Clock and Asynchronous Preset
module  \$_DFF_NP1_ (input D, C, R, output Q); DFFNP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); DFFNP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(!R)); endmodule

// DFFC      D Flip-Flop with Asynchronous Clear
module  \$_DFF_PP0_ (input D, C, R, output Q); DFFC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); DFFC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(!R)); endmodule

// DFFNC     D Flip-Flop with Negative-Edge Clock and Asynchronous Clear
module  \$_DFF_NP0_ (input D, C, R, output Q); DFFNC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R)); endmodule
module  \$_DFF_NN0_ (input D, C, R, output Q); DFFNC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(!R)); endmodule

// DFFPE     D Flip-Flop with Clock Enable and Asynchronous Preset
module  \$__DFFE_PP1 (input D, C, R, E, output Q); DFFPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R), .CE(E)); endmodule
module  \$__DFFE_PN1 (input D, C, R, E, output Q); DFFPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(!R), .CE(E)); endmodule

// DFFNPE    D Flip-Flop with Negative-Edge Clock,Clock Enable, and Asynchronous Preset
module  \$__DFFE_NP1 (input D, C, R, E, output Q); DFFNPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R), .CE(E)); endmodule
module  \$__DFFE_NN1 (input D, C, R, E, output Q); DFFNPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(!R), .CE(E)); endmodule

// DFFCE     D Flip-Flop with Clock Enable and Asynchronous Clear
module  \$__DFFE_PP0 (input D, C, R, E, output Q); DFFCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R), .CE(E)); endmodule
module  \$__DFFE_PN0 (input D, C, R, E, output Q); DFFCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(!R), .CE(E)); endmodule

// DFFNCE    D Flip-Flop with Negative-Edge Clock,Clock Enable and Asynchronous Clear
module  \$__DFFE_NP0 (input D, C, R, E, output Q); DFFNCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R), .CE(E)); endmodule
module  \$__DFFE_NN0 (input D, C, R, E, output Q); DFFNCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(!R), .CE(E)); endmodule


module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]));
    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]));
    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]));
    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
