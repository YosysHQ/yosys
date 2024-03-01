module NX_LUT(input I1, I2, I3, I4, output O);

parameter lut_table = 16'h0000;

wire [7:0] s1 = I4 ? lut_table[15:8] : lut_table[7:0];
wire [3:0] s2 = I3 ? s1[7:4] : s1[3:0];
wire [1:0] s3 = I2 ? s2[3:2] : s2[1:0];
assign O = I1 ? s3[1] : s3[0];

endmodule
