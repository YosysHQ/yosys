//-------------------------------------------------
// DSP Primitives
//-------------------------------------------------

//-------------------------------------------------
// Multiply accumulators
module quad_mac12x10 (A0, B0, A1, B1, A2, B2, A3, B3, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
input  [0:A_WIDTH-1] A2;
input  [0:B_WIDTH-1] B2;
input  [0:A_WIDTH-1] A3;
input  [0:B_WIDTH-1] B3;
output  [0:Y_WIDTH-1] Y;

  assign Y = A0 * B0 + A1 * B1 + A2 * B2 + A3 * B3;

endmodule

//-------------------------------------------------
// Multiply accumulators with input registering
module quad_mac12x10_regi (CLK, RSTB, A0, B0, A1, B1, A2, B2, A3, B3, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
input  [0:A_WIDTH-1] A2;
input  [0:B_WIDTH-1] B2;
input  [0:A_WIDTH-1] A3;
input  [0:B_WIDTH-1] B3;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A0_reg;
reg  [0:B_WIDTH-1] B0_reg;
reg  [0:A_WIDTH-1] A1_reg;
reg  [0:B_WIDTH-1] B1_reg;
reg  [0:A_WIDTH-1] A2_reg;
reg  [0:B_WIDTH-1] B2_reg;
reg  [0:A_WIDTH-1] A3_reg;
reg  [0:B_WIDTH-1] B3_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A0_reg <= 0;
    B0_reg <= 0;
    A1_reg <= 0;
    B1_reg <= 0;
    A2_reg <= 0;
    B2_reg <= 0;
    A3_reg <= 0;
    B3_reg <= 0;
  end else begin
    A0_reg <= A0;
    B0_reg <= B0;
    A1_reg <= A1;
    B1_reg <= B1;
    A2_reg <= A2;
    B2_reg <= B2;
    A3_reg <= A3;
    B3_reg <= B3;
  end
end

assign Y = A0_reg * B0_reg + A1_reg * B1_reg + A2_reg * B2_reg + A3_reg * B3_reg;

endmodule

//-------------------------------------------------
// Multiply accumulators with output registering
module quad_mac12x10_rego (CLK, RSTB, A0, B0, A1, B1, A2, B2, A3, B3, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
input  [0:A_WIDTH-1] A2;
input  [0:B_WIDTH-1] B2;
input  [0:A_WIDTH-1] A3;
input  [0:B_WIDTH-1] B3;
output  [0:Y_WIDTH-1] Y;

reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    Y_reg <= 0;
  end else begin
    Y_reg <= A0 * B0 + A1 * B1 + A2 * B2 + A3 * B3;
  end
end

assign Y = Y_reg;

endmodule

//-------------------------------------------------
// Multiply accumulators with input and output registering
module quad_mac12x10_regio (CLK, RSTB, A0, B0, A1, B1, A2, B2, A3, B3, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
input  [0:A_WIDTH-1] A2;
input  [0:B_WIDTH-1] B2;
input  [0:A_WIDTH-1] A3;
input  [0:B_WIDTH-1] B3;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A0_reg;
reg  [0:B_WIDTH-1] B0_reg;
reg  [0:A_WIDTH-1] A1_reg;
reg  [0:B_WIDTH-1] B1_reg;
reg  [0:A_WIDTH-1] A2_reg;
reg  [0:B_WIDTH-1] B2_reg;
reg  [0:A_WIDTH-1] A3_reg;
reg  [0:B_WIDTH-1] B3_reg;
reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A0_reg <= 0;
    B0_reg <= 0;
    A1_reg <= 0;
    B1_reg <= 0;
    A2_reg <= 0;
    B2_reg <= 0;
    A3_reg <= 0;
    B3_reg <= 0;
    Y_reg <= 0;
  end else begin
    A0_reg <= A0;
    B0_reg <= B0;
    A1_reg <= A1;
    B1_reg <= B1;
    A2_reg <= A2;
    B2_reg <= B2;
    A3_reg <= A3;
    B3_reg <= B3;
    Y_reg <= A0_reg * B0_reg + A1_reg * B1_reg + A2_reg * B2_reg + A3_reg * B3_reg;
  end
end

assign Y = Y_reg;

endmodule


module quad_mac12x10_dual_output (A0, B0, A1, B1, A2, B2, A3, B3, Y0, Y1);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
input  [0:A_WIDTH-1] A2;
input  [0:B_WIDTH-1] B2;
input  [0:A_WIDTH-1] A3;
input  [0:B_WIDTH-1] B3;
output  [0:Y_WIDTH-1] Y0;
output  [0:Y_WIDTH-1] Y1;

  assign Y0 = A0 * B0 + A1 * B1 + A2 * B2 + A3 * B3;
  assign Y1 = A2 * B2 + A3 * B3;

endmodule

module mac12x10 (A0, B0, A1, B1, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
output  [0:Y_WIDTH-1] Y;

  assign Y = A0 * B0 + A1 * B1;

endmodule

module mac12x10_regi (CLK, RSTB, A0, B0, A1, B1, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A0_reg;
reg  [0:B_WIDTH-1] B0_reg;
reg  [0:A_WIDTH-1] A1_reg;
reg  [0:B_WIDTH-1] B1_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A0_reg <= 0;
    B0_reg <= 0;
    A1_reg <= 0;
    B1_reg <= 0;
  end else begin
    A0_reg <= A0;
    B0_reg <= B0;
    A1_reg <= A1;
    B1_reg <= B1;
  end
end

  assign Y = A0_reg * B0_reg + A1_reg * B1_reg;

endmodule

module mac12x10_rego (CLK, RSTB, A0, B0, A1, B1, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
output  [0:Y_WIDTH-1] Y;


reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    Y_reg <= 0;
  end else begin
    Y_reg <= A0 * B0 + A1 * B1;
  end
end

  assign Y = Y_reg;

endmodule

module mac12x10_regio (CLK, RSTB, A0, B0, A1, B1, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:A_WIDTH-1] A1;
input  [0:B_WIDTH-1] B1;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A0_reg;
reg  [0:B_WIDTH-1] B0_reg;
reg  [0:A_WIDTH-1] A1_reg;
reg  [0:B_WIDTH-1] B1_reg;
reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A0_reg <= 0;
    B0_reg <= 0;
    A1_reg <= 0;
    B1_reg <= 0;
    Y_reg <= 0;
  end else begin
    A0_reg <= A0;
    B0_reg <= B0;
    A1_reg <= A1;
    B1_reg <= B1;
    Y_reg = A0_reg * B0_reg + A1_reg * B1_reg;
  end
end

  assign Y = Y_reg;

endmodule


//-------------------------------------------------
// Multipliers
module mult12x10 (A, B, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

  assign Y = A * B;

endmodule

module mult12x10_regi (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A_reg;
reg  [0:B_WIDTH-1] B_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A_reg <= 0;
    B_reg <= 0;
  end else begin
    A_reg <= A;
    B_reg <= B;
  end
end

  assign Y = A_reg * B_reg;

endmodule

module mult12x10_rego (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    Y_reg <= 0;
  end else begin
    Y_reg <= A * B;
  end
end

  assign Y = Y_reg;

endmodule

module mult12x10_regio (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A_reg;
reg  [0:B_WIDTH-1] B_reg;
reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A_reg <= 0;
    B_reg <= 0;
    Y_reg <= 0;
  end else begin
    A_reg <= A;
    B_reg <= B;
    Y_reg <= A_reg * B_reg;
  end
end

  assign Y = Y_reg;

endmodule


module mult24x20 (A, B, Y);
// Parameters
parameter A_WIDTH = 24;
parameter B_WIDTH = 20;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

  assign Y = A * B;

endmodule

module mult24x20_regi (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 24;
parameter B_WIDTH = 20;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A_reg;
reg  [0:B_WIDTH-1] B_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A_reg <= 0;
    B_reg <= 0;
  end else begin
    A_reg <= A;
    B_reg <= B;
  end
end

  assign Y = A_reg * B_reg;

endmodule

module mult24x20_rego (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 24;
parameter B_WIDTH = 20;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    Y_reg <= 0;
  end else begin
    Y_reg <= A * B;
  end
end

  assign Y = Y_reg;

endmodule

module mult24x20_regio (CLK, RSTB, A, B, Y);
// Parameters
parameter A_WIDTH = 24;
parameter B_WIDTH = 20;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input CLK;
input RSTB;
input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH-1] Y;

reg  [0:A_WIDTH-1] A_reg;
reg  [0:B_WIDTH-1] B_reg;
reg  [0:Y_WIDTH-1] Y_reg;

always @(posedge CLK) begin
  if (RSTB == 1'b0) begin
    A_reg <= 0;
    B_reg <= 0;
    Y_reg <= 0;
  end else begin
    A_reg <= A;
    B_reg <= B;
    Y_reg <= A_reg * B_reg;
  end
end

  assign Y = Y_reg;

endmodule


// A half multiplier which only output the most significant 11 bit
module half_mult12x10 (A, B, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A;
input  [0:B_WIDTH-1] B;
output  [0:Y_WIDTH/2-1] Y;

wire [0:Y_WIDTH-1] mult_out;

  mult12x10 FULL_MULT (.A(A),
                       .B(B),
                       .Y(mult_out)
                      );
  assign Y = mult_out[0:Y_WIDTH/2-1];

endmodule

module mad12x10x22 (A0, B0, C0, Y);
// Parameters
parameter A_WIDTH = 12;
parameter B_WIDTH = 10;
parameter Y_WIDTH = A_WIDTH + B_WIDTH;

input  [0:A_WIDTH-1] A0;
input  [0:B_WIDTH-1] B0;
input  [0:Y_WIDTH-1] C0;
output  [0:Y_WIDTH-1] Y;

  assign Y = A0 * B0 + C0;

endmodule

