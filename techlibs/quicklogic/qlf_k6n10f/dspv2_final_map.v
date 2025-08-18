// Derived from dspv2_sim.v

module dspv2_32x18x64_cfg_ports (
	input  wire [31:0] a_i,
	input  wire [17:0] b_i,
	input  wire [17:0] c_i,
	output wire [49:0] z_o,

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
	parameter  ZCIN_REG  = 1'b0;
	parameter  FRAC_MODE = 1'b0;  // 32x18x64 DSP

	(* is_inferred *)
	QL_DSPV2 #(
		.MODE_BITS({FRAC_MODE,3'b000,ZCIN_REG,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,COEFF_0})
	) _TECHMAP_REPLACE_ (
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

		.z_cout(z_cout_o),
		.a_cout(a_cout_o),
		.b_cout(b_cout_o)
	);
	
endmodule

module dspv2_16x9x32_cfg_ports (
	input  wire [15:0] a_i,
	input  wire [8:0] b_i,
	input  wire [8:0] c_i,
	output wire [24:0] z_o,

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
	parameter  ZCIN_REG  = 1'b0;
	parameter  FRAC_MODE = 1'b1;  // 16x9x32 DSP

	(* is_inferred *)
	QL_DSPV2 #(
		.MODE_BITS({FRAC_MODE,3'b000,ZCIN_REG,M_REG,BC_REG,C_REG,B_REG,B_SEL,A_REG,A_SEL,PRE_ADD,SUBTRACT,SATURATE,SHIFT_REG,ZREG_SHIFT,ZC_SHIFT,ROUND,ACC_FIR,16'h0,COEFF_0})
	) _TECHMAP_REPLACE_ (
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

		.z_cout(z_cout_o),
		.a_cout(a_cout_o),
		.b_cout(b_cout_o)
	);
	
endmodule

