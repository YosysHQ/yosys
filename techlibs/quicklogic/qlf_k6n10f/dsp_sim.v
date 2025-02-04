`timescale 1ps/1ps

`default_nettype none

// ---------------------------------------- //
// ----- DSP cells simulation modules ----- //
// --------- Control bits in ports -------- //
// ---------------------------------------- //

module QL_DSPV2 ( // TODO: Name subject to change
    input  wire [31:0] a,
    input  wire [17:0] b,
	input  wire [17:0] c,
	input  wire        load_acc,
    input  wire [2:0]  feedback,
	input  wire [2:0]  output_select,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire       clk,
    input  wire       reset,
	input  wire       acc_reset,
   
	input  wire [31:0] 	a_cin,
    input  wire [17:0] 	b_cin,
	input  wire [49:0] 	z_cin,
	output wire [49:0] 	z_cout,
	output wire [31:0] 	a_cout,
	output wire [17:0] 	b_cout
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];
	
    localparam NBITS_ACC = 64;
    localparam NBITS_A  = 32;
    localparam NBITS_BC = 18;
    localparam NBITS_Z  = 50;

    wire [NBITS_Z-1:0] dsp_full_z;
    wire [(NBITS_Z/2)-1:0] dsp_frac0_z;
    wire [(NBITS_Z/2)-1:0] dsp_frac1_z;
	
    wire [NBITS_Z-1:0] dsp_full_z_cout;
    wire [(NBITS_Z/2)-1:0] dsp_frac0_z_cout;
    wire [(NBITS_Z/2)-1:0] dsp_frac1_z_cout;

    wire [NBITS_A-1:0] dsp_full_a_cout;
    wire [(NBITS_A/2)-1:0] dsp_frac0_a_cout;
    wire [(NBITS_A/2)-1:0] dsp_frac1_a_cout;
	
    wire [NBITS_BC-1:0] dsp_full_b_cout;
    wire [(NBITS_BC/2)-1:0] dsp_frac0_b_cout;
    wire [(NBITS_BC/2)-1:0] dsp_frac1_b_cout;

    assign z = FRAC_MODE ? {dsp_frac1_z, dsp_frac0_z} : dsp_full_z;
	assign z_cout = FRAC_MODE ? {dsp_frac1_z_cout, dsp_frac0_z_cout} : dsp_full_z_cout;
    assign a_cout = FRAC_MODE ? {dsp_frac1_a_cout, dsp_frac0_a_cout} : dsp_full_a_cout;
	assign b_cout = FRAC_MODE ? {dsp_frac1_b_cout, dsp_frac0_b_cout} : dsp_full_b_cout;

    // Output used when fmode == 1
        dspv2_sim_cfg_ports #(
			.NBITS_A(NBITS_A/2),
            .NBITS_BC(NBITS_BC/2),
            .NBITS_ACC(NBITS_ACC/2),
            .NBITS_Z(NBITS_Z/2)
        ) dsp_frac0 (
			// active/fabric ports 
			.clock_i(clk),
			.s_reset(reset),
			.a_i(a[(NBITS_A/2)-1:0]),
			.b_i(b[(NBITS_BC/2)-1:0]),
			.c_i(c[(NBITS_BC/2)-1:0]),
			.feedback_i(feedback),
			.output_select_i(output_select),
			.load_acc_i(load_acc),
			.rst_acc_i(acc_reset),
			.z_o(dsp_frac0_z),
			// cascade ports (connect to dedicated cascade routing)
			.a_cin_i(a_cin[(NBITS_A/2)-1:0]),
			.b_cin_i(b_cin[(NBITS_BC/2)-1:0]),
			.z_cin_i(z_cin[(NBITS_Z/2)-1:0]),
			.z_cout_o(dsp_frac0_z_cout),
			.a_cout_o(dsp_frac0_a_cout),
			.b_cout_o(dsp_frac0_b_cout),
		    // configuration ports (tie-offs)
			.coeff_i(COEFF_0[(NBITS_A/2)-1:0]),
			.acc_fir_i(ACC_FIR),
			.round_i(ROUND),
			.zc_shift_i(ZC_SHIFT),
			.zreg_shift_i(ZREG_SHIFT),
			.shift_right_i(SHIFT_REG),
			.saturate_enable_i(SATURATE),
			.subtract_i(SUBTRACT),
			.pre_add_sel_i(PRE_ADD),
			.a_sel_i(A_SEL),
			.a_reg_i(A_REG),
			.b_sel_i(B_SEL),
			.b_reg_i(B_REG),
			.c_reg_i(C_REG),
			.bc_reg_i(BC_REG),
			.m_reg_i(M_REG)
        );

    // Output used when fmode == 1        
	dspv2_sim_cfg_ports #(
			.NBITS_A(NBITS_A/2),
            .NBITS_BC(NBITS_BC/2),
            .NBITS_ACC(NBITS_ACC/2),
            .NBITS_Z(NBITS_Z/2)
        ) dsp_frac1 (
			// active/fabric ports 
			.clock_i(clk),
			.s_reset(reset),
			.a_i(a[NBITS_A-1:NBITS_A/2]),
			.b_i(b[NBITS_BC-1:NBITS_BC/2]),
			.c_i(c[NBITS_BC-1:NBITS_BC/2]),
			.feedback_i(feedback),
			.output_select_i(output_select),
			.load_acc_i(load_acc),
			.rst_acc_i(acc_reset),
			.z_o(dsp_frac1_z),
			// cascade ports (connect to dedicated cascade routing)
			.a_cin_i(a_cin[NBITS_A-1:NBITS_A/2]),
			.b_cin_i(b_cin[NBITS_BC-1:NBITS_BC/2]),
			.z_cin_i(z_cin[NBITS_Z-1:NBITS_Z/2]),
			.z_cout_o(dsp_frac1_z_cout),
			.a_cout_o(dsp_frac1_a_cout),
			.b_cout_o(dsp_frac1_b_cout),
		    // configuration ports (tie-offs)
			.coeff_i(COEFF_0[NBITS_A-1:NBITS_A/2]),
			.acc_fir_i(ACC_FIR),
			.round_i(ROUND),
			.zc_shift_i(ZC_SHIFT),
			.zreg_shift_i(ZREG_SHIFT),
			.shift_right_i(SHIFT_REG),
			.saturate_enable_i(SATURATE),
			.subtract_i(SUBTRACT),
			.pre_add_sel_i(PRE_ADD),
			.a_sel_i(A_SEL),
			.a_reg_i(A_REG),
			.b_sel_i(B_SEL),
			.b_reg_i(B_REG),
			.c_reg_i(C_REG),
			.bc_reg_i(BC_REG),
			.m_reg_i(M_REG)
        );

    // Output used when fmode == 0
        dspv2_sim_cfg_ports #(
			.NBITS_A(NBITS_A),
            .NBITS_BC(NBITS_BC),
            .NBITS_ACC(NBITS_ACC),
            .NBITS_Z(NBITS_Z)
        ) dsp_full (
			// active/fabric ports 
			.clock_i(clk),
			.s_reset(reset),
			.a_i(a),
			.b_i(b),
			.c_i(c),
			.feedback_i(feedback),
			.output_select_i(output_select),
			.load_acc_i(load_acc),
			.rst_acc_i(acc_reset),
			.z_o(dsp_full_z),
			// cascade ports (connect to dedicated cascade routing)
			.a_cin_i(a_cin),
			.b_cin_i(b_cin),
			.z_cin_i(z_cin),
			.z_cout_o(dsp_full_z_cout),
			.a_cout_o(dsp_full_a_cout),
			.b_cout_o(dsp_full_b_cout),
		    // configuration ports (tie-offs)
			.coeff_i(COEFF_0),
			.acc_fir_i(ACC_FIR),
			.round_i(ROUND),
			.zc_shift_i(ZC_SHIFT),
			.zreg_shift_i(ZREG_SHIFT),
			.shift_right_i(SHIFT_REG),
			.saturate_enable_i(SATURATE),
			.subtract_i(SUBTRACT),
			.pre_add_sel_i(PRE_ADD),
			.a_sel_i(A_SEL),
			.a_reg_i(A_REG),
			.b_sel_i(B_SEL),
			.b_reg_i(B_REG),
			.c_reg_i(C_REG),
			.bc_reg_i(BC_REG),
			.m_reg_i(M_REG)						
        );

endmodule


module QL_DSPV2_MULT ( 
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    input  wire [2:0] feedback,
	input  wire [2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(),
        .reset(),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULT_REGIN ( 
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire       clk,
    input  wire       reset,

    input  wire [2:0] feedback,
    input  wire [2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h0A000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULT_REGOUT ( 
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire       clk,
    input  wire       reset,

    input  wire [2:0] feedback,
    input  wire [2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULT_REGIN_REGOUT ( // TODO: Name subject to change
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire       clk,
    input  wire       reset,

    input  wire [2:0] feedback,
    input  wire [2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h0A000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTADD (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(),
        .reset(),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );

endmodule

module QL_DSPV2_MULTADD_REGIN (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,

    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h0A000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );

endmodule

module QL_DSPV2_MULTADD_REGOUT (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,

    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTADD_REGIN_REGOUT (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,

    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h0A000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(1'b0),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(1'b0),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTACC (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,
	input  wire        acc_reset,
    input  wire        load_acc,
    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(load_acc),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(acc_reset),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTACC_REGIN (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,
	input  wire        acc_reset,
    input  wire        load_acc,
    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h04000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(load_acc),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(acc_reset),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTACC_REGOUT (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,
	input  wire        acc_reset,
    input  wire        load_acc,
    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h00000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(load_acc),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(acc_reset),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module QL_DSPV2_MULTACC_REGIN_REGOUT (
    input  wire [31:0] a,
    input  wire [17:0] b,
    output wire [49:0] z,

    (* clkbuf_sink *)
    input  wire        clk,
    input  wire        reset,
	input  wire        acc_reset,
    input  wire        load_acc,
    input  wire [ 2:0] feedback,
    input  wire [ 2:0] output_select
);

    parameter [67:0] MODE_BITS = 68'h04000000000000000;

    localparam [31:0] COEFF_0 	= MODE_BITS[31:0];
	localparam [5:0]  ACC_FIR   = MODE_BITS[37:32];
    localparam [2:0]  ROUND 	= MODE_BITS[40:38];
    localparam [4:0]  ZC_SHIFT	= MODE_BITS[45:41];
    localparam [4:0]  ZREG_SHIFT= MODE_BITS[50:46];
	localparam [5:0]  SHIFT_REG = MODE_BITS[56:51];
	localparam  SATURATE  = MODE_BITS[57];
	localparam  SUBTRACT  = MODE_BITS[58];
	localparam  PRE_ADD   = MODE_BITS[59];
	localparam  A_SEL     = MODE_BITS[60];
	localparam  A_REG     = MODE_BITS[61];
	localparam  B_SEL     = MODE_BITS[62];
	localparam  B_REG     = MODE_BITS[63];
	localparam  C_REG     = MODE_BITS[64];
	localparam  BC_REG    = MODE_BITS[65];
	localparam  M_REG     = MODE_BITS[66];
	localparam  FRAC_MODE = MODE_BITS[67];

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a),
        .b(b),
		.c(18'h0),
        .load_acc(load_acc),
		.feedback(feedback),
		.output_select(output_select),
        .z(z),
        
		.clk(clk),
        .reset(reset),
		.acc_reset(acc_reset),

        .a_cin(),
        .b_cin(),
		.z_cin(),

        .z_cout(),
        .a_cout(),
        .b_cout()
    );
	
endmodule

module dspv2_32x18x64_cfg_ports (
    input  wire [31:0] a_i,
    input  wire [17:0] b_i,
    input  wire [17:0] c_i,
    output wire [49:0] z_o,

    (* clkbuf_sink *)
    input  wire        clock_i,
    input  wire        reset_i,
	input  wire        acc_reset_i,

    input  wire [ 2:0] feedback_i,
    input  wire        load_acc_i,
    input  wire [ 2:0] output_select_i,
	
	input  wire [31:0] a_cin_i,
	input  wire [17:0] b_cin_i,
	input  wire [49:0] z_cin_i,
	
	output  wire [31:0] a_cout_o,
	output  wire [17:0] b_cout_o,
	output  wire [49:0] z_cout_o

);

    parameter [31:0] COEFF_0 	= 32'h0;
	parameter [5:0]  ACC_FIR   	= 6'h0;
    parameter [2:0]  ROUND 		= 3'h0;
    parameter [4:0]  ZC_SHIFT	= 5'h0;
    parameter [4:0]  ZREG_SHIFT	= 5'h0;
	parameter [5:0]  SHIFT_REG 	= 6'h0;
	parameter  SATURATE  = 1'b0;
	parameter  SUBTRACT  = 1'b0;
	parameter  PRE_ADD   = 1'b0;
	parameter  A_SEL     = 1'b0;
	parameter  A_REG     = 1'b0;
	parameter  B_SEL     = 1'b0;
	parameter  B_REG     = 1'b0;
	parameter  C_REG     = 1'b0;
	parameter  BC_REG    = 1'b0;
	parameter  M_REG     = 1'b0;
	parameter  FRAC_MODE = 1'b0;  // 32x18x64 DSP

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
    ) dsp (
        .a(a_i),
        .b(b_i),
		.c(c_i),
        .load_acc(load_acc_i),
		.feedback(feedback_i),
		.output_select(output_select_i),
        .z(z_o),
        
		.clk(clock_i),
        .reset(reset_i),
		.acc_reset(acc_reset_i),

        .a_cin(a_cin_i),
        .b_cin(b_cin_i),
		.z_cin(z_cin_i),

        .z_cout(a_cout_o),
        .a_cout(b_cout_o),
        .b_cout(z_cout_o)
    );
	
endmodule

module dspv2_16x9x32_cfg_ports (
    input  wire [15:0] a_i,
    input  wire [8:0] b_i,
    input  wire [9:0] c_i,
    output wire [24:0] z_o,

    (* clkbuf_sink *)
    input  wire        clock_i,
    input  wire        reset_i,
	input  wire        acc_reset_i,

    input  wire [ 2:0] feedback_i,
    input  wire        load_acc_i,
    input  wire [ 2:0] output_select_i,
	
	input  wire [15:0] a_cin_i,
	input  wire [8:0] b_cin_i,
	input  wire [24:0] z_cin_i,
	
	output  wire [15:0] a_cout_o,
	output  wire [8:0] b_cout_o,
	output  wire [24:0] z_cout_o

);

    parameter [15:0] COEFF_0 	= 16'h0;
	parameter [5:0]  ACC_FIR   	= 6'h0;
    parameter [2:0]  ROUND 		= 3'h0;
    parameter [4:0]  ZC_SHIFT	= 5'h0;
    parameter [4:0]  ZREG_SHIFT	= 5'h0;
	parameter [5:0]  SHIFT_REG 	= 6'h0;
	parameter  SATURATE  = 1'b0;
	parameter  SUBTRACT  = 1'b0;
	parameter  PRE_ADD   = 1'b0;
	parameter  A_SEL     = 1'b0;
	parameter  A_REG     = 1'b0;
	parameter  B_SEL     = 1'b0;
	parameter  B_REG     = 1'b0;
	parameter  C_REG     = 1'b0;
	parameter  BC_REG    = 1'b0;
	parameter  M_REG     = 1'b0;
	parameter  FRAC_MODE = 1'b1;  // 16x9x32 DSP

    QL_DSPV2 #(
        .MODE_BITS({FRAC_MODE,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,16'h0,COEFF_0})
    ) dsp (
        .a(a_i),
        .b(b_i),
		.c(c_i),
        .load_acc(load_acc_i),
		.feedback(feedback_i),
		.output_select(output_select_i),
        .z(z_o),
        
		.clk(clock_i),
        .reset(reset_i),
		.acc_reset(acc_reset_i),

        .a_cin(a_cin_i),
        .b_cin(b_cin_i),
		.z_cin(z_cin_i),

        .z_cout(a_cout_o),
        .a_cout(b_cout_o),
        .b_cout(z_cout_o)
    );
	
endmodule


module dspv2_sim_cfg_ports # (
    parameter NBITS_ACC  = 64,
    parameter NBITS_A    = 32,
    parameter NBITS_BC   = 18,
    parameter NBITS_Z    = 50
)(
	// active/fabric ports 
    input  wire               	clock_i,
    input  wire               	s_reset,
    input  wire [NBITS_A-1:0] 	a_i,
    input  wire [NBITS_BC-1:0] 	b_i,
	input  wire [NBITS_BC-1:0] 	c_i,
	input  wire [2:0]           feedback_i,
	input  wire [2:0]           output_select_i,
	input  wire                 load_acc_i,
	input  wire                 rst_acc_i,
    output wire [NBITS_Z-1:0] 	z_o,
	
    // cascade ports (connect to dedicated cascade routing)
	input  wire [NBITS_A-1:0] 	a_cin_i,
    input  wire [NBITS_BC-1:0] 	b_cin_i,
	input  wire [NBITS_Z-1:0] 	z_cin_i,
	output wire [NBITS_Z-1:0] 	z_cout_o,
	output wire [NBITS_A-1:0] 	a_cout_o,
	output wire [NBITS_BC-1:0] 	b_cout_o,
	
	// configuration ports (tie-offs)
    input  wire [NBITS_A-1:0] coeff_i,
    input  wire [5:0]         acc_fir_i,
    input  wire [2:0]         round_i,
	input  wire [4:0]         zc_shift_i,
	input  wire [4:0]         zreg_shift_i,
    input  wire [5:0]         shift_right_i,
	input  wire               saturate_enable_i,
	input  wire               subtract_i,
	input  wire               pre_add_sel_i,
	input  wire               a_sel_i,
	input  wire               a_reg_i,
	input  wire               b_sel_i,
	input  wire               b_reg_i,
	input  wire               c_reg_i,
	input  wire               bc_reg_i,
	input  wire               m_reg_i
);

    // Input registers
    reg  [NBITS_A-1:0]   r_a;
    reg  [NBITS_BC-1:0]  r_b;
	reg  [NBITS_BC-1:0]  r_c;

    reg [NBITS_ACC-1:0] acc;
	
	wire [NBITS_A-1:0] a_acin_dat;
	wire [NBITS_BC-1:0] b_bcin_dat;
	
	wire [NBITS_A-1:0]  a;
	wire [NBITS_BC-1:0] b;
	wire [NBITS_BC-1:0] c;
	
	wire [NBITS_BC:0] preadd_raw;
	
	reg  [NBITS_BC-1:0]  preadd_sat;	
	reg  [NBITS_BC-1:0]  preadd_sat_r;
	wire [NBITS_BC-1:0]  preadd;

    initial begin
        r_a          <= 0;
        r_b          <= 0;
		r_c          <= 0;
    end
	
	assign a_acin_dat = (a_sel_i)? a_cin_i: a_i;
	assign b_bcin_dat = (b_sel_i)? b_cin_i: b_i;

    always @(posedge clock_i or posedge s_reset) begin
        if (s_reset) begin
            r_a <= 0;
            r_b <= 0;
			r_c <= 0;
        end else begin
            r_a <= a_acin_dat;
            r_b <= b_bcin_dat;
			r_c <= c_i;
        end
    end

    // Registered / non-registered input path select
    assign a = (a_reg_i) ? r_a : a_acin_dat;
    assign b = (b_reg_i) ? r_b : b_bcin_dat;
	assign c = (c_reg_i) ? r_c : c_i;
	
	assign preadd_raw = b + c;
	
	always @(*) begin
		if (!b[(NBITS_BC-1)] && !c[(NBITS_BC-1)]) begin         // pos+pos
			if (preadd_raw[(NBITS_BC-1)]) begin
				preadd_sat = {1'b0, {(NBITS_BC-1){1'b1}}};      // max pos #
			end else begin
				preadd_sat = preadd_raw[(NBITS_BC-1):0];
			end
		end else begin
			if (b[(NBITS_BC-1)] && c[(NBITS_BC-1)]) begin         // neg+neg
				if (!preadd_raw[(NBITS_BC-1)]) begin
					preadd_sat = {1'b1, {(NBITS_BC-1){1'b0}}};  // max neg #
				end else begin
					preadd_sat = preadd_raw[(NBITS_BC-1):0];
				end
			end else begin                                      // pos+neg or neg+pos
				preadd_sat = preadd_raw[(NBITS_BC-1):0];
			end
		end
	end
	
    always @(posedge clock_i or posedge s_reset) begin
        if (s_reset) begin
            preadd_sat_r <= 0;
        end else begin
            preadd_sat_r <= preadd_sat;
        end
    end
	
	assign preadd = (bc_reg_i)? preadd_sat_r : preadd_sat;


    // Multiplier
    wire [NBITS_A-1:0] mult_a;
	wire [NBITS_BC-1:0] mult_b;
	wire  mult_sgn_a;
	wire [NBITS_A-1:0] mult_mag_a;
	wire  mult_sgn_b;
	wire [NBITS_BC-1:0] mult_mag_b;
	
	wire [NBITS_A+NBITS_BC-1:0] mult_mag;
	wire  mult_sgn;
	wire [NBITS_A+NBITS_BC-1:0] mult;
	wire [NBITS_ACC-1:0] mult_xtnd;
	
	reg [NBITS_ACC-1:0] mult_xtnd_r;
	wire [NBITS_ACC-1:0] mult_xtnd_sel; 
	wire [NBITS_ACC-1:0] mult_xtnd_sub;
	wire [NBITS_ACC-1:0] add_a;
	wire [NBITS_ACC-1:0] add_b;
	wire [NBITS_ACC-1:0] add_o;
	wire [NBITS_ACC-1:0] acc_fir_int; 
	
	wire [NBITS_ACC-1:0] acc_out;
	
	wire [NBITS_ACC-1:0] zcin_rshift; 
	wire [NBITS_ACC-1:0] zcin_xtnd; 
	wire [NBITS_ACC-1:0] zreg_rshift;
		
    // Output signals
    wire [NBITS_Z-1:0]  z0;
    reg  [NBITS_Z-1:0]  z1;
    wire [NBITS_Z-1:0]  z2;
	
    assign mult_a = (feedback_i == 3'h0) ?   a :
                    (feedback_i == 3'h1) ?   a :
                    (feedback_i == 3'h2) ?   a :
                    (feedback_i == 3'h3) ?   a :
                    (feedback_i == 3'h4) ?   a :
                    (feedback_i == 3'h5) ?   a :
                    (feedback_i == 3'h6) ?   acc[NBITS_A-1:0]:
                       coeff_i;    // if feedback_i == 3'h7

    assign mult_b = (pre_add_sel_i) ? preadd : b;

    assign mult_sgn_a = mult_a[NBITS_A-1];
    assign mult_mag_a = (mult_sgn_a) ? (~mult_a + 1) : mult_a;
    assign mult_sgn_b = mult_b[NBITS_BC-1];
    assign mult_mag_b = (mult_sgn_b) ? (~mult_b + 1) : mult_b;

    assign mult_mag =  mult_mag_a * mult_mag_b;
    assign mult_sgn = (mult_sgn_a ^ mult_sgn_b);

    assign mult = (mult_sgn)? (~mult_mag + 1) : mult_mag;

    // Sign extension
    assign mult_xtnd = {{(NBITS_ACC-NBITS_A-NBITS_BC){mult[NBITS_A+NBITS_BC-1]}}, mult[NBITS_A+NBITS_BC-1:0]};
	
    always @(posedge clock_i or posedge s_reset) begin
        if (s_reset) begin
            mult_xtnd_r <= 0;
        end else begin
            mult_xtnd_r <= mult_xtnd;
        end
    end
	
	assign mult_xtnd_sel = m_reg_i ? mult_xtnd_r : mult_xtnd;
	
	// Adder
	assign mult_xtnd_sub = subtract_i ? (~mult_xtnd_sel + 1) : mult_xtnd_sel;
	assign add_a = (feedback_i[2:0] == 2) ? {a,b} : mult_xtnd_sub;
	
	assign acc_fir_int = a <<< acc_fir_i;
	
	assign zcin_rshift = z_cin_i >>> zc_shift_i;
	assign zcin_xtnd = {{(NBITS_ACC-NBITS_Z){z_cin_i[NBITS_Z-1]}}, z_cin_i};
	
	assign zreg_rshift = z1 >>> zreg_shift_i;
	
    assign add_b = (feedback_i == 3'h0) ? acc :
				   (feedback_i == 3'h1) ? zcin_rshift :
				   (feedback_i == 3'h2) ? zcin_xtnd :
				   (feedback_i == 3'h3) ? zcin_xtnd :
				   (feedback_i == 3'h4) ? z1 :
				   (feedback_i == 3'h5) ? zreg_rshift :
                    acc_fir_int;
		
    assign add_o = add_a + add_b;

    // Accumulator
    initial acc <= 0;

    always @(posedge clock_i or posedge s_reset)
        if (s_reset) 
			acc <= 'h0;
        else begin
            if (rst_acc_i)
				acc <= 'h0;
			else if (load_acc_i)
                acc <= add_o;
            else
                acc <= acc;
        end

    // Adder/accumulator output selection
    assign acc_out = (output_select_i[1]) ? add_o : acc;

    // Round, shift, saturate
	wire a_sign;
	wire [NBITS_ACC-1:0] onehalf;
	wire [NBITS_ACC-1:0] int_mask;
	wire [NBITS_ACC-1:0] frac_mask;
	wire [NBITS_ACC-1:0] a_frac;
	wire [NBITS_ACC-1:0] a_int;
	
	reg  [NBITS_ACC-1:0] acc_rnd;
	wire [NBITS_ACC-1:0] acc_shr;
	wire [NBITS_ACC-1:0] acc_sat_s;
	wire [NBITS_ACC-1:0] acc_sat;
	
	assign a_sign = acc_out[(NBITS_ACC-1)];
	assign onehalf = (shift_right_i == 6'b0) ? {NBITS_ACC{1'b0}} : ({{(NBITS_ACC-1){1'b0}},1'b1} << (shift_right_i-1));
	assign int_mask = ({NBITS_ACC{1'b1}} << shift_right_i);
	assign frac_mask = ~int_mask;
	assign a_frac = acc_out & frac_mask;
	assign a_int = acc_out >>> shift_right_i;
	
	always @(*) begin
      case(round_i)
        3'b000  :   // no rounding
                    acc_rnd = acc_out;

        3'b001  :   // round half up, asymmetrical
                    // add 1/2
                    acc_rnd = acc_out + onehalf;

        3'b010  :   // round half up, symmetrical
                    // if a is neg and a_frac = 1/2, do nothing, else add 1/2
                    if ((a_sign == 1'b1) && (a_frac == onehalf))
                        acc_rnd = acc_out;
                    else
                        acc_rnd = acc_out + onehalf;

        3'b011  :   // round half down, symmetrical
                    // if a is pos and a_frac = 1/2, do nothing, else add 1/2
                    if ((a_sign == 1'b0) && (a_frac == onehalf))
                        acc_rnd = acc_out;
                    else
                        acc_rnd = acc_out + onehalf;

        3'b100  :   // round half even
                    // if a is even and a_frac = 1/2, do nothing, else add 1/2
                    if ((a_int[0] == 1'b0) && (a_frac == onehalf))
                        acc_rnd = acc_out;
                    else
                        acc_rnd = acc_out + onehalf;

        3'b100  :   // round half odd
                    // if a is odd and a_frac = 1/2, do nothing, else add 1/2
                    if ((a_int[0] == 1'b1) && (a_frac == onehalf))
                        acc_rnd = acc_out;
                    else
                        acc_rnd = acc_out + onehalf;

        default :   // no rounding
                    acc_rnd = acc_out;

      endcase
    end
	
    assign acc_shr = (acc_rnd >>> shift_right_i);

    assign acc_sat_s = ((|acc_shr[NBITS_ACC-1:NBITS_Z-1] == 1'b0) ||
                        (&acc_shr[NBITS_ACC-1:NBITS_Z-1] == 1'b1)) ? {{(NBITS_ACC-NBITS_Z){1'b0}},{acc_shr[NBITS_Z-1:0]}} :
                                                                     {{(NBITS_ACC-NBITS_Z){1'b0}},{acc_shr[NBITS_ACC-1],{NBITS_Z-1{~acc_shr[NBITS_ACC-1]}}}};

    assign acc_sat = (saturate_enable_i)? acc_sat_s : acc_shr;

    assign z0 = mult_xtnd_sel[NBITS_Z-1:0];
    assign z2 = acc_sat[NBITS_Z-1:0];

    initial z1 <= 0;

    always @(posedge clock_i or posedge s_reset)
        if (s_reset)
            z1 <= 0;
        else begin
            z1 <= (output_select_i == 3'b100) ? z0 : z2;
        end

    // Output mux
    assign z_o = (output_select_i == 3'h0) ?   z0 :
                 (output_select_i == 3'h1) ?   z2 :
                 (output_select_i == 3'h2) ?   z2 :
                 (output_select_i == 3'h3) ?   z2 :
                 (output_select_i == 3'h4) ?   z1 :
                 (output_select_i == 3'h5) ?   z1 :
                 (output_select_i == 3'h6) ?   z1 :
                           z1;  // if output_select_i == 3'h7
						   
	assign z_cout_o = z_o;
	assign a_cout_o = r_a;
	assign b_cout_o = r_b;

endmodule
