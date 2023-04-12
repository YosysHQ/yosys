module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  assign O = I0 ? INIT[1] : INIT[0];
endmodule

module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT4_HA(output O, Co, input I0, I1, I2, I3, Ci);
  parameter [15:0] INIT = 0;
  parameter I0MUX = 1'b1;

  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];

  wire I0_sel = I0MUX ? Ci : I0;
  assign O = I0_sel ? s1[1] : s1[0];

  assign Co = (Ci & I1) | (Ci & I2) | (I1 & I2);
endmodule

module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT6(output O, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
  wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT55_FCY (output O, Co, input I0, I1, I2, I3, I4, Ci);
  parameter [63:0] INIT = 0;

  wire comb1, comb2;

  LUT5 #(.INIT(INIT[31: 0])) l5_1 (.I0(I0), .I1(I1), .I2(I2), .I3(I3), .I4(I4), .O(comb1));
  LUT5 #(.INIT(INIT[63:32])) l5_2 (.I0(I0), .I1(I1), .I2(I2), .I3(I3), .I4(I4), .O(comb2));

  assign O = comb1 ^ Ci;
  assign Co = comb1 ? Ci : comb2;
endmodule


module LUTFF(input CLK, D, output reg O);
  initial O = 1'b0;
  always @ (posedge CLK) begin
    O <= D;
  end
endmodule

module FABULOUS_MUX2(input I0, I1, S0, output O);
  assign O = S0 ? I1 : I0;
endmodule

module FABULOUS_MUX4(input I0, I1, I2, I3, S0, S1, output O);
  wire A0 = S0 ? I1 : I0;
  wire A1 = S0 ? I3 : I2;
  assign O = S1 ? A1 : A0;
endmodule

module FABULOUS_MUX8(input I0, I1, I2, I3, I4, I5, I6, I7, S0, S1, S2, output O);
  wire A0 = S0 ? I1 : I0;
  wire A1 = S0 ? I3 : I2;
  wire A2 = S0 ? I5 : I4;
  wire A3 = S0 ? I7 : I6;
  wire B0 = S1 ? A1 : A0;
  wire B1 = S1 ? A3 : A2;
  assign O = S2 ? B1 : B0;
endmodule

module FABULOUS_LC #(
  parameter K = 4,
  parameter [2**K-1:0] INIT = 0,
  parameter DFF_ENABLE = 1'b0
) (
  input CLK,
  input [K-1:0] I,
  output O,
  output Q
);
  wire f_wire;
  
  //LUT #(.K(K), .INIT(INIT)) lut_i(.I(I), .Q(f_wire));
  generate
    if (K == 1) begin
      LUT1 #(.INIT(INIT)) lut1 (.O(f_wire), .I0(I[0]));
    end else
    if (K == 2) begin
      LUT2 #(.INIT(INIT)) lut2 (.O(f_wire), .I0(I[0]), .I1(I[1]));
    end else
    if (K == 3) begin
      LUT3 #(.INIT(INIT)) lut3 (.O(f_wire), .I0(I[0]), .I1(I[1]), .I2(I[2]));
    end else
    if (K == 4) begin
      LUT4 #(.INIT(INIT)) lut4 (.O(f_wire), .I0(I[0]), .I1(I[1]), .I2(I[2]), .I3(I[3]));
    end
  endgenerate
        
  LUTFF dff_i(.CLK(CLK), .D(f_wire), .Q(Q));

  assign O = f_wire;
endmodule

(* blackbox *)
module Global_Clock (output CLK);
`ifndef SYNTHESIS
  initial CLK = 0;
  always #10 CLK = ~CLK;
`endif
endmodule

(* blackbox, keep *)
module InPass4_frame_config (input CLK, output O0, O1, O2, O3);

endmodule


(* blackbox, keep *)
module OutPass4_frame_config (input CLK, I0, I1, I2, I3);

endmodule

(* keep *)
module IO_1_bidirectional_frame_config_pass (input CLK, T, I, output Q, O, (* iopad_external_pin *) inout PAD);
  assign PAD = T ? 1'bz : I;
  assign O = PAD;
  reg Q_q;
  always @(posedge CLK) Q_q <= O;
  assign Q = Q_q;
endmodule


module MULADD (A7, A6, A5, A4, A3, A2, A1, A0, B7, B6, B5, B4, B3, B2, B1, B0, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, C3, C2, C1, C0, Q19, Q18, Q17, Q16, Q15, Q14, Q13, Q12, Q11, Q10, Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q2, Q1, Q0, clr, CLK);
  parameter A_reg = 1'b0;
  parameter B_reg = 1'b0;
  parameter C_reg = 1'b0;
  parameter ACC = 1'b0;
  parameter signExtension = 1'b0;
  parameter ACCout = 1'b0;

  //parameter NoConfigBits = 6;// has to be adjusted manually (we don't use an arithmetic parser for the value)
  // IMPORTANT: this has to be in a dedicated line
  input A7;// operand A
  input A6;
  input A5;
  input A4;
  input A3;
  input A2;
  input A1;
  input A0;
  input B7;// operand B
  input B6;
  input B5;
  input B4;
  input B3;
  input B2;
  input B1;
  input B0;
  input C19;// operand C
  input C18;
  input C17;
  input C16;
  input C15;
  input C14;
  input C13;
  input C12;
  input C11;
  input C10;
  input C9;
  input C8;
  input C7;
  input C6;
  input C5;
  input C4;
  input C3;
  input C2;
  input C1;
  input C0;
  output Q19;// result
  output Q18;
  output Q17;
  output Q16;
  output Q15;
  output Q14;
  output Q13;
  output Q12;
  output Q11;
  output Q10;
  output Q9;
  output Q8;
  output Q7;
  output Q6;
  output Q5;
  output Q4;
  output Q3;
  output Q2;
  output Q1;
  output Q0;

  input clr;
  input CLK; // EXTERNAL // SHARED_PORT // ## the EXTERNAL keyword will send this sisgnal all the way to top and the //SHARED Allows multiple BELs using the same port (e.g. for exporting a clock to the top)
  // GLOBAL all primitive pins that are connected to the switch matrix have to go before the GLOBAL label


  wire [7:0] A;   // port A read data 
  wire [7:0] B;   // port B read data 
  wire [19:0] C;    // port B read data 
  reg [7:0] A_q;    // port A read data register
  reg [7:0] B_q;    // port B read data register
  reg [19:0] C_q;   // port B read data register
  wire [7:0] OPA;   // port A 
  wire [7:0] OPB;   // port B 
  wire [19:0] OPC;    // port B  
  reg [19:0] ACC_data ;    // accumulator register
  wire [19:0] sum;// port B read data register
  wire [19:0] sum_in;// port B read data register
  wire [15:0] product;
  wire [19:0] product_extended;

  assign A = {A7,A6,A5,A4,A3,A2,A1,A0};
  assign B = {B7,B6,B5,B4,B3,B2,B1,B0};
  assign C = {C19,C18,C17,C16,C15,C14,C13,C12,C11,C10,C9,C8,C7,C6,C5,C4,C3,C2,C1,C0};

  assign OPA = A_reg ? A_q : A;
  assign OPB = B_reg ? B_q : B;
  assign OPC = C_reg ? C_q : C;

  assign sum_in = ACC ? ACC_data : OPC;// we can

  assign product = OPA * OPB;

// The sign extension was not tested
  assign product_extended = signExtension ? {product[15],product[15],product[15],product[15],product} : {4'b0000,product};

  assign sum = product_extended + sum_in;

  assign Q19  = ACCout ? ACC_data[19] : sum[19];
  assign Q18  = ACCout ? ACC_data[18] : sum[18];
  assign Q17  = ACCout ? ACC_data[17] : sum[17];
  assign Q16  = ACCout ? ACC_data[16] : sum[16];
  assign Q15  = ACCout ? ACC_data[15] : sum[15];
  assign Q14  = ACCout ? ACC_data[14] : sum[14];
  assign Q13  = ACCout ? ACC_data[13] : sum[13];
  assign Q12  = ACCout ? ACC_data[12] : sum[12];
  assign Q11  = ACCout ? ACC_data[11] : sum[11];
  assign Q10  = ACCout ? ACC_data[10] : sum[10];
  assign Q9 = ACCout ? ACC_data[9] : sum[9];
  assign Q8 = ACCout ? ACC_data[8] : sum[8];
  assign Q7 = ACCout ? ACC_data[7] : sum[7];
  assign Q6 = ACCout ? ACC_data[6] : sum[6];
  assign Q5 = ACCout ? ACC_data[5] : sum[5];
  assign Q4 = ACCout ? ACC_data[4] : sum[4];
  assign Q3 = ACCout ? ACC_data[3] : sum[3];
  assign Q2 = ACCout ? ACC_data[2] : sum[2];
  assign Q1 = ACCout ? ACC_data[1] : sum[1];
  assign Q0 = ACCout ? ACC_data[0] : sum[0];

  always @ (posedge CLK)
  begin
    A_q <= A;
    B_q <= B;
    C_q <= C;
    if (clr == 1'b1) begin
      ACC_data <= 20'b00000000000000000000;
    end else begin
      ACC_data <= sum;
    end
  end

endmodule

module RegFile_32x4 (D0, D1, D2, D3, W_ADR0, W_ADR1, W_ADR2, W_ADR3, W_ADR4, W_en, AD0, AD1, AD2, AD3, A_ADR0, A_ADR1, A_ADR2, A_ADR3, A_ADR4, BD0, BD1, BD2, BD3, B_ADR0, B_ADR1, B_ADR2, B_ADR3, B_ADR4, CLK);
  //parameter NoConfigBits = 2;// has to be adjusted manually (we don't use an arithmetic parser for the value)
  parameter AD_reg = 1'b0;
  parameter BD_reg = 1'b0;
  // IMPORTANT: this has to be in a dedicated line
  input D0; // Register File write port
  input D1;
  input D2;
  input D3;
  input W_ADR0;
  input W_ADR1;
  input W_ADR2;
  input W_ADR3;
  input W_ADR4;
  input W_en;
  
  output AD0;// Register File read port A
  output AD1;
  output AD2;
  output AD3;
  input A_ADR0;
  input A_ADR1;
  input A_ADR2;
  input A_ADR3;
  input A_ADR4;

  output BD0;//Register File read port B
  output BD1;
  output BD2;
  output BD3;
  input B_ADR0;
  input B_ADR1;
  input B_ADR2;
  input B_ADR3;
  input B_ADR4;

  input CLK;// EXTERNAL // SHARED_PORT // ## the EXTERNAL keyword will send this sisgnal all the way to top and the //SHARED Allows multiple BELs using the same port (e.g. for exporting a clock to the top)
  
  // GLOBAL all primitive pins that are connected to the switch matrix have to go before the GLOBAL label
  

  //type memtype is array (31 downto 0) of std_logic_vector(3 downto 0); // 32 entries of 4 bit
  //signal mem : memtype := (others => (others => '0'));
  reg [3:0] mem [31:0];

  wire [4:0] W_ADR;// write address
  wire [4:0] A_ADR;// port A read address
  wire [4:0] B_ADR;// port B read address

  wire [3:0] D;   // write data
  wire [3:0] AD;    // port A read data
  wire [3:0] BD;    // port B read data

  reg [3:0] AD_q;   // port A read data register
  reg [3:0] BD_q;   // port B read data register
  
  integer i;

  assign W_ADR = {W_ADR4,W_ADR3,W_ADR2,W_ADR1,W_ADR0};
  assign A_ADR = {A_ADR4,A_ADR3,A_ADR2,A_ADR1,A_ADR0};
  assign B_ADR = {B_ADR4,B_ADR3,B_ADR2,B_ADR1,B_ADR0};

  assign D = {D3,D2,D1,D0};
  
  initial begin
    for (i=0; i<32; i=i+1) begin
      mem[i] = 4'b0000;
    end
  end

  always @ (posedge CLK) begin : P_write
    if (W_en == 1'b1) begin
      mem[W_ADR] <= D ;
    end
  end

  assign AD = mem[A_ADR];
  assign BD = mem[B_ADR];

  always @ (posedge CLK) begin
    AD_q <= AD;
    BD_q <= BD;
  end

  assign AD0 = AD_reg ? AD_q[0] : AD[0];
  assign AD1 = AD_reg ? AD_q[1] : AD[1];
  assign AD2 = AD_reg ? AD_q[2] : AD[2];
  assign AD3 = AD_reg ? AD_q[3] : AD[3];

  assign BD0 = BD_reg ? BD_q[0] : BD[0];
  assign BD1 = BD_reg ? BD_q[1] : BD[1];
  assign BD2 = BD_reg ? BD_q[2] : BD[2];
  assign BD3 = BD_reg ? BD_q[3] : BD[3];

endmodule

`ifdef EQUIV
`define COMPLEX_DFF
`endif

`ifdef COMPLEX_DFF
module LUTFF_E (
  output reg O,
  input CLK, E, D
);
  initial O = 1'b0;
  always @(posedge CLK)
    if (E)
      O <= D;
endmodule

module LUTFF_SR (
  output reg O,
  input CLK, R, D
);
  initial O = 1'b0;
  always @(posedge CLK)
    if (R)
      O <= 0;
    else
      O <= D;
endmodule

module LUTFF_SS (
  output reg O,
  input CLK, S, D
);
  initial O = 1'b0;
  always @(posedge CLK)
    if (S)
      O <= 1;
    else
      O <= D;
endmodule

module LUTFF_ESR (
  output reg O,
  input CLK, E, R, D
);
  initial O = 1'b0;
  always @(posedge CLK)
    if (E) begin
      if (R)
        O <= 0;
      else
        O <= D;
    end
endmodule

module LUTFF_ESS (
  output reg O,
  input CLK, E, S, D
);
  initial O = 1'b0;
  always @(posedge CLK)
    if (E) begin
      if (S)
        O <= 1;
      else
        O <= D;
    end
endmodule
`endif // COMPLEX_DFF
