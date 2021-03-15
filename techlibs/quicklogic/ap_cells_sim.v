//                FZ        FS
module LUT1(output O, input I0);
    parameter [1:0] INIT = 0;
    parameter EQN = "(I0)";
    assign O = I0 ? INIT[1] : INIT[0];
endmodule

//               TZ        TSL TAB
module LUT2(output O, input I0, I1);
    parameter [3:0] INIT = 4'h0;
	parameter EQN = "(I0)";
    assign O = INIT[{I1, I0}];
endmodule

// O:  TZ
// I0: TA1 TA2 TB1 TB2
// I1: TSL
// I2: TAB
module LUT3(output O, input I0, I1, I2);
    parameter [7:0] INIT = 8'h0;
	parameter EQN = "(I0)";
    assign O = INIT[{I2, I1, I0}];
endmodule

// O:  CZ
// I0: TA1 TA2 TB1 TB2 BA1 BA2 BB1 BB2
// I1: TSL BSL
// I2: TAB BAB
// I3: TBS
module LUT4(output O, input I0, I1, I2, I3);
    parameter [15:0] INIT = 16'h0;
    parameter EQN = "(I0)";
    assign O = INIT[{I3, I2, I1, I0}];
endmodule

module ck_buff ( 
	output Q,
    (* iopad_external_pin *)
	input A
);
    
	assign Q = A;

endmodule /* ck buff */

module in_buff ( 
	output Q,
    (* iopad_external_pin *)
	input A
);

    assign Q = A;

endmodule /* in buff */

module out_buff ( 
    (* iopad_external_pin *)
	output Q,
	input A
);

	assign Q = A;

endmodule /* out buff */

module d_buff ( 
    (* iopad_external_pin *)
	output Q
);
	parameter DSEL = 1'b0;
	assign Q = DSEL ? 1'b1 : 1'b0;
	
endmodule /* d buff */

module dff(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;
    always @(posedge CLK)
        Q <= D;
endmodule

module dffc(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    (* clkbuf_sink *)
    input CLR
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;

    always @(posedge CLK or posedge CLR)
        if (CLR)
            Q <= 1'b0;
        else
            Q <= D;
endmodule

module dffp(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    (* clkbuf_sink *)
    input PRE
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;

    always @(posedge CLK or posedge PRE)
        if (PRE)
            Q <= 1'b1;
        else
            Q <= D;
endmodule

module dffpc(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    (* clkbuf_sink *)
    input CLR,
    (* clkbuf_sink *)
    input PRE
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;

    always @(posedge CLK or posedge CLR or posedge PRE)
        if (CLR)
            Q <= 1'b0;
        else if (PRE)
            Q <= 1'b1;
        else
            Q <= D;
endmodule

module dffe(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    input EN
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;
    always @(posedge CLK)
        if (EN)
            Q <= D;
endmodule

module dffec(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    input EN,
    (* clkbuf_sink *)
    input CLR
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;

    always @(posedge CLK or posedge CLR)
        if (CLR)
            Q <= 1'b0;
        else if (EN)
            Q <= D;
endmodule

module dffepc(
    output reg Q,
    input D,
    (* clkbuf_sink *)
    input CLK,
    input EN,
    (* clkbuf_sink *)
    input CLR,
    (* clkbuf_sink *)
    input PRE
);
    parameter [0:0] INIT = 1'b0;
    initial Q = INIT;

    always @(posedge CLK or posedge CLR or posedge PRE)
        if (CLR)
            Q <= 1'b0;
        else if (PRE)
            Q <= 1'b1;
        else if (EN)
            Q <= D;
endmodule

//                  FZ       FS F2 (F1 TO 0)
module AND2I0(output Q, input A, B);
    assign Q = A ? B : 0;
endmodule

//                  FZ       FS F1 F2
module mux2x0(output Q, input S, A, B);
    assign Q = S ? B : A;
endmodule

//                  FZ       FS F1 F2
module mux2x1(output Q, input S, A, B);
    assign Q = S ? B : A;
endmodule

//                  TZ       TSL TABTA1TA2TB1TB2 
module mux4x0(output Q, input S0, S1, A, B, C, D);
    assign Q = S1 ? (S0 ? D : C) : (S0 ? B : A);
endmodule

// S0 BSL TSL
// S1 BAB TAB
// S2 TBS
// A TA1
// B TA2
// C TB1
// D TB2
// E BA1
// F BA2
// G BB1
// H BB2
// Q CZ
module mux8x0(output Q, input S0, S1, S2, A, B, C, D, E, F, G, H);
    assign Q = S2 ? (S1 ? (S0 ? H : G) : (S0 ? F : E)) : (S1 ? (S0 ? D : C) : (S0 ? B : A));
endmodule

module io_reg(
    A2F_reg, IE, OQI, OQE, IQE, 
    IQC, IQR, IQZ, IZ, F2A_reg_0, F2A_reg_1);

    parameter ESEL = 1'b1;
    parameter OSEL = 1'b1;
    parameter FIXHOLD = 1'b0;
    parameter INEN = 1'b0;

    input A2F_reg, IE, OQI;
    input OQE; 
    input IQC, IQE, IQR;
    output IQZ, IZ, F2A_reg_0, F2A_reg_1;

endmodule /* io_reg */

module logic_cell_macro(
    input BA1,
    input BA2,
    input BAB,
    input BAS1,
    input BAS2,
    input BB1,
    input BB2,
    input BBS1,
    input BBS2,
    input BSL,
    input F1,
    input F2,
    input FS,
    input QCK,
    input QCKS,
    input QDI,
    input QDS,
    input QEN,
    input QRT,
    input QST,
    input TA1,
    input TA2,
    input TAB,
    input TAS1,
    input TAS2,
    input TB1,
    input TB2,
    input TBS,
    input TBS1,
    input TBS2,
    input TSL,
    output CZ,
    output FZ,
    output QZ,
    output TZ
);

    wire TAP1,TAP2,TBP1,TBP2,BAP1,BAP2,BBP1,BBP2,QCKP,TAI,TBI,BAI,BBI,TZI,BZI,CZI,QZI;
    reg QZ_r;
	
    initial
    begin
        QZ_r=1'b0;
    end
    assign QZ = QZ_r;
    assign TAP1 = TAS1 ? ~TA1 : TA1; 
    assign TAP2 = TAS2 ? ~TA2 : TA2; 
    assign TBP1 = TBS1 ? ~TB1 : TB1; 
    assign TBP2 = TBS2 ? ~TB2 : TB2;
    assign BAP1 = BAS1 ? ~BA1 : BA1;
    assign BAP2 = BAS2 ? ~BA2 : BA2;
    assign BBP1 = BBS1 ? ~BB1 : BB1;
    assign BBP2 = BBS2 ? ~BB2 : BB2;

    assign TAI = TSL ? TAP2 : TAP1;
    assign TBI = TSL ? TBP2 : TBP1;
    assign BAI = BSL ? BAP2 : BAP1;
    assign BBI = BSL ? BBP2 : BBP1;
    assign TZI = TAB ? TBI : TAI;
    assign BZI = BAB ? BBI : BAI;
    assign CZI = TBS ? BZI : TZI;
    assign QZI = QDS ? QDI : CZI ;
    assign FZ = FS ? F2 : F1;
    assign TZ = TZI;
    assign CZ = CZI;
    assign QCKP = QCKS ? QCK : ~QCK;


    always @(posedge QCKP)
        if(~QRT && ~QST)
            if(QEN)
                QZ_r = QZI;
    always @(QRT or QST)
        if(QRT)
            QZ_r = 1'b0;
        else if (QST)
            QZ_r = 1'b1;

endmodule
