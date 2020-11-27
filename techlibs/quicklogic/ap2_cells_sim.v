(* abc9_lut=1, lib_whitebox *)
module LUT4(
   output O, 
   input I0,
   input I1,
   input I2,
   input I3
);
    parameter [15:0] INIT = 16'h0;
    parameter EQN = "(I0)";
    
    assign O = INIT[{I3, I2, I1, I0}];
endmodule

(* abc9_lut=1, lib_whitebox *)
module LUT5(
    output O, 
    input I0, 
    input I1,
    input I2,
    input I3,
    input I4
);
    parameter [31:0] INIT = 32'h0;
    parameter EQN = "(I0)";

    assign O = INIT[{I4, I3, I2, I1, I0}];
endmodule

(* abc9_flop, lib_whitebox *)
module ff(
    output reg CQZ,
    input D,
    //(* clkbuf_sink *)
    input QCK,
    input QEN,
    //(* clkbuf_sink *)
    input QRT,
    //(* clkbuf_sink *)
    input QST
);
    parameter [0:0] INIT = 1'b0;
    initial CQZ = INIT;

    always @(posedge QCK or posedge QRT or posedge QST)
        if (QRT)
            CQZ <= 1'b0;
        else if (QST)
            CQZ <= 1'b1;
        else if (QEN)
            CQZ <= D;
endmodule

module full_adder(
   output S,
   output CO,
   input A,
   input B,
   input CI
);

   assign {CO, S} = A + B + CI;
endmodule

(* lib_whitebox *)
module QL_CARRY(
	output CO,
	input I0,
	input I1,
	input CI
);
	assign CO = ((I0 ^ I1) & CI) | (~(I0 ^ I1) & (I0 & I1)); 
endmodule

module carry(
	output CO,
	input A,
	input B,
	input CI
);
	assign CO = (I0 && I1) || ((I0 || I1) && CI);
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


(* blackbox *)
module RAM (RADDR,RRLSEL,REN,RMODE,
	    WADDR,WDATA,WEN,WMODE,
	    FMODE,FFLUSH,RCLK,WCLK,RDATA,
	    FFLAGS,FIFO_DEPTH,ENDIAN,POWERDN,PROTECT,
	    UPAE,UPAF,SBOG);

   input [10:0] RADDR,WADDR;
   input [1:0] 	RRLSEL,RMODE,WMODE;
   input 	REN,WEN,FFLUSH,RCLK,WCLK;
   input [31:0] WDATA;
   input [1:0] 	SBOG, ENDIAN, UPAF, UPAE;
   output [31:0] RDATA;
   output [3:0]  FFLAGS;
   input [2:0] 	 FIFO_DEPTH;
   input 	 FMODE, POWERDN, PROTECT;
   

     DPRAM_FIFO U1(
		 .RCLK(RCLK), .REN(REN), .WCLK(WCLK), .WEN(WEN),
		 .WADDR(WADDR),.WDATA(WDATA),.RADDR(RADDR), .RDATA(RDATA),
		 .RMODE(RMODE), .WMODE(WMODE),
		 .TLD(), .TRD(),          // SideBand bus outputs
		 .FRD(32'h0), .FLD(32'h0),  // SideBand bus inputs
		 .FFLAGS(FFLAGS), // unused FIFO flags
		 .FMODE(FMODE), .FFLUSH(FFLUSH),.RRLSEL(RRLSEL),
		 .PROTECT(PROTECT),
		 .PL_INIT(1'b0), .PL_ENA(1'b0), .PL_CLK(1'b0),
		 .PL_REN(1'b0), .PL_WEN(1'b0),
		 .PL_ADDR(20'h0), .PL_DATA_IN(32'h0), .PL_DATA_OUT(),
		 .ENDIAN(ENDIAN), .FIFO_DEPTH(FIFO_DEPTH), .RAM_ID(8'h00),
		 .POWERDN(POWERDN), .SBOG(SBOG),
		 .UPAE(UPAE), .UPAF(UPAF),
		 .DFT_SCAN_CLK_DAISYIN(1'b0), .DFT_SCAN_RST_DAISYIN(1'b0),
		 .DFT_SCAN_MODE_DAISYIN(1'b0), .DFT_SCAN_EN_DAISYIN(1'b0),
		 .DFT_SCAN_IN_DAISYIN(1'b0), .dft_FFB_scan_out()
		 );
endmodule 
