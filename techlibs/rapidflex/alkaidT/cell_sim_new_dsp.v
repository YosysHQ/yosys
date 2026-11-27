module mad12x10x22 (clk_i, rst_ni, a_i, b_i, d_i, out_o, mode_i, rst_acc, accsel, cas_g, overflow);

input [0:47] a_i;
input [0:39] b_i;
input [0:59] d_i;
input [0:12] mode_i;
output [0:59] out_o;

input clk_i;
input rst_ni;
input rst_acc;
input accsel;
input cas_g;
output overflow;

  dsp #(
    .N_SIZE (12),
    .M_SIZE (10)
  ) u_dsp(
    .a_i    (a_i),
    .b_i    (b_i),
    .out_o  (out_o),

    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .d_i      (d_i),
    .mode_i   (mode_i),
    .rst_acc  (rst_acc),
    .accsel   (accsel),
    .cas_g    (cas_g),
    .overflow (overflow)
  );

endmodule

module mad24x20x44 (clk_i, rst_ni, a_i, b_i, d_i, out_o, mode_i, rst_acc, accsel, cas_g, overflow);

input [0:95] a_i;
input [0:79] b_i;
input [0:103] d_i;
input [0:12] mode_i;
output [0:103] out_o;

input clk_i;
input rst_ni;
input rst_acc;
input accsel;
input cas_g;
output overflow;

  dsp #(
    .N_SIZE (24),
    .M_SIZE (20)
  ) u_dsp(
    .a_i    (a_i),
    .b_i    (b_i),
    .out_o  (out_o),

    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .d_i      (d_i),
    .mode_i   (mode_i),
    .rst_acc  (rst_acc),
    .accsel   (accsel),
    .cas_g    (cas_g),
    .overflow (overflow)
  );

endmodule

//-----------------------------------------------------
// Design Name : Parameterized DSP block
// File Name   : dsp.v
// Function    : A N*M-bit DSP block which can operate in fracturable modes:
//               1. four [N/4]*[M/4]-bit multiplication with accumulation
//                 1.1 (combinational)
//                 1.2 (with input registers triggered by rising edge)
//                 1.3 (with output registers triggered by rising edge)
//                 1.4 (with input and output registers triggered by rising edge)
//                 1.5 (with input registers triggered by falling edge)
//                 1.6 (with output registers triggered by falling edge)
//                 1.7 (with input and output registers triggered by falling edge)
//               2. two [N/2]*[M/2]-bit multipliers
//                 2.1 (combinational)
//                 2.2 (with input registers triggered by rising edge)
//                 2.3 (with output registers triggered by rising edge)
//                 2.4 (with input and output registers triggered by rising edge)
//                 2.5 (with input registers triggered by falling edge)
//                 2.6 (with output registers triggered by falling edge)
//                 2.7 (with input and output registers triggered by falling edge)
//               3. Single N*M-bit multipliers
//                 3.1 (combinational)
//                 3.2 (with input registers triggered by rising edge)
//                 3.3 (with output registers triggered by rising edge)
//                 3.4 (with input and output registers triggered by rising edge)
//                 3.5 (with input registers triggered by falling edge)
//                 3.6 (with output registers triggered by falling edge)
//                 3.7 (with input and output registers triggered by falling edge)
//               4. Two [N/4]*[M/4]-bit multiply-accumulators
//                 4.1 (combinational)
//                 4.2 (with input registers triggered by rising edge)
//                 4.3 (with output registers triggered by rising edge)
//                 4.4 (with input and output registers triggered by rising edge)
//                 4.5 (with input registers triggered by falling edge)
//                 4.6 (with output registers triggered by falling edge)
//                 4.7 (with input and output registers triggered by falling edge)
//               5. One [N/4]*[M/4]-bit multiplier + One [N/4]*[M/4]-bit MAC
//                 5.1 (combinational)
//                 5.2 (with input registers triggered by rising edge)
//                 5.3 (with output registers triggered by rising edge)
//                 5.4 (with input and output registers triggered by rising edge)
//                 5.5 (with input registers triggered by falling edge)
//                 5.6 (with output registers triggered by falling edge)
//                 5.7 (with input and output registers triggered by falling edge)
//               6. One [N/4]*[M/4]-bit MAC + One [N/4]*[M/4]-bit multiply
//                 6.1 (combinational)
//                 6.2 (with input registers triggered by rising edge)
//                 6.3 (with output registers triggered by rising edge)
//                 6.4 (with input and output registers triggered by rising edge)
//                 6.5 (with input registers triggered by falling edge)
//                 6.6 (with output registers triggered by falling edge)
//                 6.7 (with input and output registers triggered by falling edge)
//               7. MSB parts [N/2+M/2] of four multipliers
//                 7.1 (combinational)
//                 7.2 (with input registers triggered by rising edge)
//                 7.3 (with output registers triggered by rising edge)
//                 7.4 (with input and output registers triggered by rising edge)
//                 7.5 (with input registers triggered by falling edge)
//                 7.6 (with output registers triggered by falling edge)
//                 7.7 (with input and output registers triggered by falling edge)
//               8. One [N/4]*[M/4]-bit multiply + MSB parts [N/2+M/2] of four multipliers
//                 8.1 (combinational)
//                 8.2 (with input registers triggered by rising edge)
//                 8.3 (with output registers triggered by rising edge)
//                 8.4 (with input and output registers triggered by rising edge)
//                 8.5 (with input registers triggered by falling edge)
//                 8.6 (with output registers triggered by falling edge)
//                 8.7 (with input and output registers triggered by falling edge)
//               9. One [N/4]*[M/4]-bit MAC + MSB parts [N/2+M/2] of four multipliers
//                 9.1 (combinational)
//                 9.2 (with input registers triggered by rising edge)
//                 9.3 (with output registers triggered by rising edge)
//                 9.4 (with input and output registers triggered by rising edge)
//                 9.5 (with input registers triggered by falling edge)
//                 9.6 (with output registers triggered by falling edge)
//                 9.7 (with input and output registers triggered by falling edge)
//               - In all the above modes, clock edges can be either positive or negative triggered
// Coder       : Xifan Tang
//-----------------------------------------------------
`default_nettype wire

module dsp (clk_i, rst_ni, a_i, b_i, d_i, out_o, mode_i, rst_acc, accsel, cas_g, overflow);
  // Parameters that can pass through
  parameter N_SIZE = 12;                            // Default parameter for N
  parameter M_SIZE = 10;                            // Default parameter for M
  // Local parameters
  localparam A_WIDTH = 4 * N_SIZE;                  // Default parameter for a
  localparam B_WIDTH = 4 * M_SIZE;                  // Default parameter for b
  localparam C_WIDTH = N_SIZE + M_SIZE;             // Default parameter for cin
  localparam OUT_WIDTH = A_WIDTH / 2 + B_WIDTH / 2; // Default parameter for data output
  
  parameter P_SIZE = OUT_WIDTH;									 // Default parameter for previous d
  
  // Ensure that all the mode bit constants unique!!!
  localparam MODE_BIT_CLK = 0;        // Mode bit that controls polarity of the clock signals
  localparam MODE_BIT_REGI_UPPER = 1; // Mode bit that controls the registering of upper part of the inputs
  localparam MODE_BIT_REGI_LOWER = 2; // Mode bit that controls the registering of lower part of the inputs
  localparam MODE_BIT_REGO_UPPER = 3; // Mode bit that controls the registering of upper part of the outputs
  localparam MODE_BIT_REGO_LOWER = 4; // Mode bit that controls the registering of lower part of the outputs
  localparam MODE_BIT_MAC_LSB = 5;    // LSB of the mode bits that control the core computing units
  localparam MODE_BIT_MAC_MSB = 8;    // MSB of the mode bits that contorl the core computing units
  localparam MODE_BIT_RST = 9;    // MSB of the mode bits that contorl the polarity of reset signals
  localparam MODE_BIT_SIGN = 10;    //Mode bit that controls valid of the sign bit
  // localparam MODE_BIT_CARRY = 11;    //Mode bit that controls valid of the carry bit
  localparam MODE_MUL_INPUT_REG = 11; // Mode bit that controls the registering of the inputs of the multipliers
  localparam MODE_MUL_OUTPUT_REG = 12; // Mode bit that controls the registering of the outputs of the multipliers

  localparam ADDER_REDUNDENT = 8; // Default parameter for adder redundancy
  localparam ADD_ACC_WIDTH = OUT_WIDTH/2 + ADDER_REDUNDENT; // Default accumulating parameter for adder width
  localparam ACC_OUT_WIDTH = OUT_WIDTH + 2*ADDER_REDUNDENT;

  // Ports
  input clk_i;
  input rst_ni;
  input [0:A_WIDTH-1] a_i;
  input [0:B_WIDTH-1] b_i;
  input [0:ACC_OUT_WIDTH-1] d_i;
  output [0:ACC_OUT_WIDTH-1] out_o;
  input [0:12] mode_i;
  output overflow;
  // input cin;
  // output cout;
  input rst_acc; //For accumulate resettable
  input accsel; // Accumulate or add new data
  input cas_g;  // Global cascade mode for top level dsp
  
  
  wire clk_core;
  wire clr;
  assign clk_core = mode_i[MODE_BIT_CLK] ? clk_i : ~clk_i;
  assign clr = mode_i[MODE_BIT_RST] ? ~rst_ni : rst_ni;

  // Control logic for registering inputs and outputs

  wire [0:A_WIDTH-1] in_a;
  wire [0:B_WIDTH-1] in_b;
  wire [0:ACC_OUT_WIDTH-1] in_d;
  wire [0:ACC_OUT_WIDTH-1] cas_out;

  reg [0:A_WIDTH-1] a_i_reg;
  reg [0:B_WIDTH-1] b_i_reg;
  reg [0:ACC_OUT_WIDTH-1] d_i_reg;
  reg [0:ACC_OUT_WIDTH-1] out_o_reg;

  always @(posedge clk_core or negedge clr) begin
    if (clr == 1'b0) begin
      a_i_reg <= 0;
      b_i_reg <= 0;
      d_i_reg <= 0;
      out_o_reg <= 0;
    end else begin
      a_i_reg <= a_i;
      b_i_reg <= b_i; 
      d_i_reg <= d_i;
      out_o_reg <= cas_out;
    end
  end

  assign in_a[0:A_WIDTH/2-1] = mode_i[MODE_BIT_REGI_LOWER] ? a_i_reg[0:A_WIDTH/2-1] : a_i[0:A_WIDTH/2-1];
  assign in_a[A_WIDTH/2:A_WIDTH-1] = mode_i[MODE_BIT_REGI_UPPER] ? a_i_reg[A_WIDTH/2:A_WIDTH-1] : a_i[A_WIDTH/2:A_WIDTH-1];
  assign in_b[0:B_WIDTH/2-1] = mode_i[MODE_BIT_REGI_LOWER] ? b_i_reg[0:B_WIDTH/2-1] : b_i[0:B_WIDTH/2-1];
  assign in_b[B_WIDTH/2:B_WIDTH-1] = mode_i[MODE_BIT_REGI_UPPER] ? b_i_reg[B_WIDTH/2:B_WIDTH-1] : b_i[B_WIDTH/2:B_WIDTH-1];
  assign in_d[0:ACC_OUT_WIDTH/2-1] = mode_i[MODE_BIT_REGI_LOWER] ? d_i_reg[0:ACC_OUT_WIDTH/2-1] : d_i[0:ACC_OUT_WIDTH/2-1];
  assign in_d[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1] = mode_i[MODE_BIT_REGI_UPPER] ? d_i_reg[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1] : d_i[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];
  assign out_o[0:ACC_OUT_WIDTH/2-1] = mode_i[MODE_BIT_REGO_LOWER] ? out_o_reg[0:ACC_OUT_WIDTH/2-1] : cas_out[0:ACC_OUT_WIDTH/2-1];
  assign out_o[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1] = mode_i[MODE_BIT_REGO_UPPER] ? out_o_reg[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1] : cas_out[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];

  // Control logic for registering inputs and outputs of the multipliers

  wire [0:A_WIDTH-1] mac_a;
  wire [0:B_WIDTH-1] mac_b;
  wire [0:ACC_OUT_WIDTH-1] mac_d;
  wire [0:ACC_OUT_WIDTH-1] mac_out;

  reg [0:A_WIDTH-1] in_a_reg;
  reg [0:B_WIDTH-1] in_b_reg;
  reg [0:ACC_OUT_WIDTH-1] in_d_reg;

  wire [0:ACC_OUT_WIDTH/2-1] mul_out_0;
  wire [0:ACC_OUT_WIDTH/2-1] mul_out_1;
  wire [0:ACC_OUT_WIDTH/2-1] mul_out_2;
  wire [0:ACC_OUT_WIDTH/2-1] mul_out_3;

  reg [0:ACC_OUT_WIDTH/2-1] mul_out_0_reg;
  reg [0:ACC_OUT_WIDTH/2-1] mul_out_1_reg;
  reg [0:ACC_OUT_WIDTH/2-1] mul_out_2_reg;
  reg [0:ACC_OUT_WIDTH/2-1] mul_out_3_reg;

  wire [0:ACC_OUT_WIDTH/2-1] q_o_0;
  wire [0:ACC_OUT_WIDTH/2-1] q_o_1;
  wire [0:ACC_OUT_WIDTH/2-1] q_o_2;
  wire [0:ACC_OUT_WIDTH/2-1] q_o_3;

  always @(posedge clk_core or negedge clr) begin
    if (clr == 1'b0) begin
      in_a_reg <= 0;
      in_b_reg <= 0;
      in_d_reg <= 0;
      mul_out_0_reg <= 0;
      mul_out_1_reg <= 0;
      mul_out_2_reg <= 0;
      mul_out_3_reg <= 0;
    end else begin
      in_a_reg <= in_a;
      in_b_reg <= in_b;
      in_d_reg <= in_d;
      mul_out_0_reg <= mul_out_0;
      mul_out_1_reg <= mul_out_1;
      mul_out_2_reg <= mul_out_2;
      mul_out_3_reg <= mul_out_3;
    end
  end

  assign mac_a = mode_i[MODE_MUL_INPUT_REG] ? in_a_reg : in_a;
  assign mac_b = mode_i[MODE_MUL_INPUT_REG] ? in_b_reg : in_b;
  assign mac_d = mode_i[MODE_MUL_INPUT_REG] ? in_d_reg : in_d;

  assign q_o_0 = mode_i[MODE_MUL_OUTPUT_REG] ? mul_out_0_reg : mul_out_0;
  assign q_o_1 = mode_i[MODE_MUL_OUTPUT_REG] ? mul_out_1_reg : mul_out_1;
  assign q_o_2 = mode_i[MODE_MUL_OUTPUT_REG] ? mul_out_2_reg : mul_out_2;
  assign q_o_3 = mode_i[MODE_MUL_OUTPUT_REG] ? mul_out_3_reg : mul_out_3;

  // Control logic around the core computing units
  always @(*) begin
    case (mode_i[MODE_BIT_MAC_LSB:MODE_BIT_MAC_MSB])
        4'b0000: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + q_o_0;
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1] + q_o_1;
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + q_o_2;
          mac_out = q_o_3;
        end
        4'b0001: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1] + mac_d[0:ACC_OUT_WIDTH/2-1];
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1] + mac_d[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + q_o_2;
          mac_out = {q_o_0, q_o_3};
        end
        4'b0010: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + q_o_0;
          mul_out_3 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1];
          mac_out = {q_o_1, q_o_2};
        end
        4'b0011: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1] + out_o_reg[0:ACC_OUT_WIDTH/2-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + out_o_reg[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];
          mac_out = {q_o_0, q_o_1};
        end
        4'b0100: begin
          mac_out = mac_a[0:A_WIDTH/2-1] * mac_b[0:B_WIDTH/2-1];
        end
        4'b0101: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1] + mac_d[0:ACC_OUT_WIDTH/2-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + mac_d[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];
          mac_out = {q_o_0, q_o_1};
        end
        4'b0110: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1];
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1];
          mac_out = {q_o_0[0:ACC_OUT_WIDTH/4-1], q_o_1[0:ACC_OUT_WIDTH/4-1], q_o_2[0:ACC_OUT_WIDTH/4-1], q_o_3[0:ACC_OUT_WIDTH/4-1]};
        end
        4'b1000: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1];
          mac_out = {q_o_0, q_o_1};
        end
        4'b1001: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1] + mac_d[0:ACC_OUT_WIDTH/2-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + q_o_0;
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1] + q_o_1;
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + q_o_2;
          mac_out = {q_o_2, q_o_3};
        end
        4'b1010: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + q_o_0;
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1] + q_o_1;
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + q_o_2;
          mac_out = {q_o_1, q_o_3};
        end
        4'b1011: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_1 = mac_a[A_WIDTH/4:A_WIDTH/2-1] * mac_b[B_WIDTH/4:B_WIDTH/2-1] + q_o_0;
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + q_o_2;
          mac_out = {q_o_1, q_o_3};
        end
        4'b1101: begin
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1] + mac_d[0:ACC_OUT_WIDTH/2-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1] + mac_d[ACC_OUT_WIDTH/2:ACC_OUT_WIDTH-1];
          mac_out = {q_o_2, q_o_3};
        end
        4'b1110: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1];
          mac_out = {q_o_0, q_o_2[0:ACC_OUT_WIDTH/4-1], q_o_3[0:ACC_OUT_WIDTH/4-1]};
        end
        default: begin
          mul_out_0 = mac_a[0:A_WIDTH/4-1] * mac_b[0:B_WIDTH/4-1];
          mul_out_2 = mac_a[A_WIDTH/2:A_WIDTH/4*3-1] * mac_b[B_WIDTH/2:B_WIDTH/4*3-1];
          mul_out_3 = mac_a[A_WIDTH/4*3:A_WIDTH-1] * mac_b[B_WIDTH/4*3:B_WIDTH-1];
          mac_out = {q_o_0, q_o_2[0:ACC_OUT_WIDTH/4-1], q_o_3[0:ACC_OUT_WIDTH/4-1]};
        end
    endcase
  end

  always @(*) begin
	  cas_out = cas_g ? mac_out + mac_d : mac_out;
  end

endmodule