(* techmap_celltype = "$_DFF_N_ $_DFF_P_" *)
module  \$_DFF_x_ (input D, C, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        if (_TECHMAP_WIREINIT_Q_ === 1'b1)
            localparam REGSET = "SET";
        else
            localparam REGSET = "RESET";
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(1'b0), .DI(D), .Q(Q));
endmodule

(* techmap_celltype = "$_DFFE_NN_ $_DFFE_PN_ $_DFFE_NP_ $_DFFE_PP_" *)
module  \$_DFFE_xx_ (input D, C, E, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "N")
            localparam CEMUX = "INV";
        else
            localparam CEMUX = "CE";
        if (_TECHMAP_WIREINIT_Q_ === 1'b1)
            localparam REGSET = "SET";
        else
            localparam REGSET = "RESET";
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX(CEMUX), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(1'b0), .DI(D), .Q(Q));
endmodule

(* techmap_celltype = "$_DFF_NN0_ $_DFF_NN1_ $_DFF_PN0_ $_DFF_PN1_ $_DFF_NP0_ $_DFF_NP1_ $_DFF_PP0_ $_DFF_PP1_" *)
module  \$_DFF_xxx_ (input D, C, R, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[3*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        // TODO: Why not use LSRMUX param?
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            wire LSR_ = !R;
        else
            wire LSR_ = R;
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "1") begin
            localparam REGSET = "SET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b0)
                $error("ECP5 doesn't support FFs with asynchronous set initialized to 0");
        end
        else begin
            localparam REGSET = "RESET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b1)
                $error("ECP5 doesn't support FFs with asynchronous reset initialized to 1");
        end
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(LSR_), .DI(D), .Q(Q));
endmodule

(* techmap_celltype = "$__DFFS_NN0_ $__DFFS_NN1_ $__DFFS_PN0_ $__DFFS_PN1_ $__DFFS_NP0_ $__DFFS_NP1_ $__DFFS_PP0_ $__DFFS_PP1_" *)
module  \$__DFFS_xxx_ (input D, C, R, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[3*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        // TODO: Why not use LSRMUX param?
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            wire LSR_ = !R;
        else
            wire LSR_ = R;
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "1") begin
            localparam REGSET = "SET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b0)
                // init is 0, reset to 1
                wire D_ = D || LSR_;
            else
                wire D_ = D;
        end
        else begin
            localparam REGSET = "RESET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b1)
                // init is 1, reset to 0
                wire D_ = !(D && LSR_);
            else
                wire D_ = D;
        end
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX("1"), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(LSR_), .DI(D_), .Q(Q));
endmodule

(* techmap_celltype = "$__DFFE_NN0 $__DFFE_NN1 $__DFFE_PN0 $__DFFE_PN1 $__DFFE_NP0 $__DFFE_NP1 $__DFFE_PP0 $__DFFE_PP1" *)
module  \$__DFFE_xxx_ (input D, C, E, R, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[3*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        // TODO: Why not use LSRMUX param?
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            wire LSR_ = !R;
        else
            wire LSR_ = R;
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "1") begin
            if (_TECHMAP_WIREINIT_Q_ === 1'b0)
                $error("ECP5 doesn't support FFs with asynchronous set initialized to 0");
            else
                localparam REGSET = "SET";
        end
        else begin
            if (_TECHMAP_WIREINIT_Q_ === 1'b1)
                $error("ECP5 doesn't support FFs with asynchronous reset initialized to 1");
            else
                localparam REGSET = "RESET";
        end
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E), .LSR(LSR_), .DI(D), .Q(Q));
endmodule

(* techmap_celltype = "$__DFFSE_NN0 $__DFFSE_NN1 $__DFFSE_PN0 $__DFFSE_PN1 $__DFFSE_NP0 $__DFFSE_NP1 $__DFFSE_PP0 $__DFFSE_PP1" *)
module  \$__DFFSE_xxx_ (input D, C, E, R, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[3*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        // TODO: Why not use LSRMUX param?
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            wire LSR_ = !R;
        else
            wire LSR_ = R;
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "1") begin
            localparam REGSET = "SET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b0) begin
                // init is 0, reset to 1
                wire D_ = D || LSR_;
                wire E_ = E || LSR_;
            end
            else begin
                wire D_ = D;
                wire E_ = E;
            end
        end
        else begin
            localparam REGSET = "RESET";
            if (_TECHMAP_WIREINIT_Q_ === 1'b1) begin
                // init is 1, reset to 0
                wire D_ = !(D && LSR_);
                wire E_ = !(E && LSR_);
            end
            else begin
                wire D_ = D;
                wire E_ = E;
            end
        end
    endgenerate
    TRELLIS_FF #(.GSR("AUTO"), .CEMUX("CE"), .CLKMUX(CLKMUX), .LSRMUX("LSR"), .REGSET(REGSET), .SRMODE("LSR_OVER_CE"))  _TECHMAP_REPLACE_ (.CLK(C), .CE(E_), .LSR(LSR_), .DI(D_), .Q(Q));
endmodule

`ifdef ASYNC_PRLD
(* techmap_celltype = "$_DLATCH_N_ $_DLATCH_P_" *)
module  \$_DLATCH_x_ (input E, input D, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        // TODO: Why not use LSRMUX param?
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "N")
            wire LSR_ = !E;
        else
            wire LSR_ = E;
        if (_TECHMAP_WIREINIT_Q_ !== 1'bx)
            $error("ECP5 doesn't support latches with initial values"); // TODO: Check
    endgenerate
    TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.LSR(LSR_), .DI(1'b0), .M(D), .Q(Q));
endmodule

(* techmap_celltype = "$_DFFSR_NNN_ $_DFFSR_NNP_ $_DFFSR_PNN_ $_DFFSR_PNP_ $_DFFSR_NPN_ $_DFFSR_NPP_ $_DFFSR_PPN_ $_DFFSR_PPP_" *)
module \$_DFFSR_xxx_ (input C, S, R, D, output Q);
    parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
	parameter _TECHMAP_CELLTYPE_ = "";
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    generate
        if (_TECHMAP_CELLTYPE_[3*8+:8] == "N")
            localparam CLKMUX = "INV";
        else
            localparam CLKMUX = "CLK";
        if (_TECHMAP_CELLTYPE_[2*8+:8] == "N")
            wire S_ = !S;
        else
            wire S_ = S;
        if (_TECHMAP_CELLTYPE_[1*8+:8] == "N")
            wire R_ = !R;
        else
            wire R_ = R;
        if (_TECHMAP_WIREINIT_Q_ !== 1'bx)
            $error("ECP5 doesn't support FFs with asynchronous set and reset with initial values");
    endgenerate

    TRELLIS_FF #(.GSR("DISABLED"), .CEMUX("1"), .CLKMUX(CLKINV), .LSRMODE("PRLD"), .LSRMUX("LSR"), .REGSET("RESET"), .SRMODE("ASYNC"))  _TECHMAP_REPLACE_ (.CLK(C), .LSR(S_ || R_), .DI(D), .M(!R_), .Q(Q));
endmodule
`endif

`include "cells_ff.vh"
`include "cells_io.vh"

`ifndef NO_LUT
module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    generate
        if (WIDTH == 1) begin
            localparam [15:0] INIT = {{8{LUT[1]}}, {8{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(1'b0), .D(A[0]));
        end else
        if (WIDTH == 2) begin
            localparam [15:0] INIT = {{4{LUT[3]}}, {4{LUT[2]}}, {4{LUT[1]}}, {4{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(1'b0), .C(A[0]), .D(A[1]));
        end else
        if (WIDTH == 3) begin
            localparam [15:0] INIT = {{2{LUT[7]}}, {2{LUT[6]}}, {2{LUT[5]}}, {2{LUT[4]}}, {2{LUT[3]}}, {2{LUT[2]}}, {2{LUT[1]}}, {2{LUT[0]}}};
            LUT4 #(.INIT(INIT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(1'b0), .B(A[0]), .C(A[1]), .D(A[2]));
        end else
        if (WIDTH == 4) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
        `ifndef NO_PFUMUX
        end else
        if (WIDTH == 5) begin
            wire f0, f1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            PFUMX mux5(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(Y));
        end else
        if (WIDTH == 6) begin
            wire f0, f1, f2, f3, g0, g1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[4]), .Z(g1));
            L6MUX21 mux6 (.D0(g0), .D1(g1), .SD(A[5]), .Z(Y));
        end else
        if (WIDTH == 7) begin
            wire f0, f1, f2, f3, f4, f5, f6, f7, g0, g1, g2, g3, h0, h1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[79:64])) lut4 (.Z(f4),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[95:80])) lut5 (.Z(f5),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[111: 96])) lut6 (.Z(f6),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[127:112])) lut7 (.Z(f7),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .C0(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .C0(A[4]), .Z(g1));
            PFUMX mux52(.ALUT(f5), .BLUT(f4), .C0(A[4]), .Z(g2));
            PFUMX mux53(.ALUT(f7), .BLUT(f6), .C0(A[4]), .Z(g3));
            L6MUX21 mux60 (.D0(g0), .D1(g1), .SD(A[5]), .Z(h0));
            L6MUX21 mux61 (.D0(g2), .D1(g3), .SD(A[5]), .Z(h1));
            L6MUX21 mux7  (.D0(h0), .D1(h1), .SD(A[6]), .Z(Y));
        `endif
        end else begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule
`endif
