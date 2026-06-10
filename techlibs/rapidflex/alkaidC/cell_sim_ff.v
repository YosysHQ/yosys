//-----------------------------
// Rising-edge D-type flip-flop
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dff(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                Q <= D;
          1'b1:
            always @(negedge C)
                Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-high asynchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffr(
    output reg Q,
    input D,
    input R,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or posedge R)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or posedge R)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-high asynchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffs(
    output reg Q,
    input D,
    input S,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or posedge S)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or posedge S)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-low asynchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffrn(
    output reg Q,
    input D,
    input RN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or negedge RN)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or negedge RN)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-low asynchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffsn(
    output reg Q,
    input D,
    input SN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or negedge SN)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or negedge SN)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-high synchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffr(
    output reg Q,
    input D,
    input R,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-high synchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffs(
    output reg Q,
    input D,
    input S,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-low synchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffrn(
    output reg Q,
    input D,
    input RN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Rising-edge D-type flip-flop with active-low synchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffsn(
    output reg Q,
    input D,
    input SN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b0;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffn(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                Q <= D;
          1'b1:
            always @(negedge C)
                Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-high asynchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffnr(
    output reg Q,
    input D,
    input R,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or posedge R)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or posedge R)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-high asynchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffns(
    output reg Q,
    input D,
    input S,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or posedge S)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or posedge S)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-low asynchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffnrn(
    output reg Q,
    input D,
    input RN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or negedge RN)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or negedge RN)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-low asynchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module dffnsn(
    output reg Q,
    input D,
    input SN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C or negedge SN)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C or negedge SN)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-high synchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffnr(
    output reg Q,
    input D,
    input R,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (R == 1'b1)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-high synchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffns(
    output reg Q,
    input D,
    input S,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (S == 1'b1)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-low synchronous reset
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffnrn(
    output reg Q,
    input D,
    input RN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (RN == 1'b0)
                        Q <= 1'b0;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Falling-edge D-type flip-flop with active-low synchronous set
//-----------------------------
(* abc9_flop, lib_whitebox *)
module sdffnsn(
    output reg Q,
    input D,
    input SN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_C_INVERTED" *)
    input C
);
    parameter [0:0] INIT = 1'b0;
    parameter [0:0] IS_C_INVERTED = 1'b1;
    initial Q = INIT;
    case(|IS_C_INVERTED)
          1'b0:
            always @(posedge C)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
          1'b1:
            always @(negedge C)
                if (SN == 1'b0)
                        Q <= 1'b1;
                else
                        Q <= D;
    endcase
endmodule

//-----------------------------
// Two-bit D-type flip-flop with active-high asynchronous reset
// 1st stage is positive-edge triggered
// 2nd stage is negative-edge triggered
//-----------------------------
// Do not allow ABC or other optimization to touch the ff!
//(* abc9_flop, lib_whitebox *)
module dffnr_dffr(
  output Q,
  input D,
  input R,
  input C
);

wire Q0;

  dffnr FF_0 (.D(D), .C(C), .R(R), .Q(Q0));
  dffr  FF_1 (.D(Q0), .C(C), .R(R), .Q(Q));

endmodule

//-----------------------------
// Two-bit D-type flip-flop with active-high asynchronous reset
// 1st stage is positive-edge triggered
// 2nd stage is negative-edge triggered
//-----------------------------
// Do not allow ABC or other optimization to touch the ff!
//(* abc9_flop, lib_whitebox *)
module dffr_dffnr(
  output Q,
  input D,
  input R,
  input C
);

wire Q0;

  dffr FF_0 (.D(D), .C(C), .R(R), .Q(Q0));
  dffnr  FF_1 (.D(Q0), .C(C), .R(R), .Q(Q));

endmodule

