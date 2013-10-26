module  \$_DFF_P_ (D, C, Q);

  input D, C;
  output Q;

  FDRE fpga_dff (
  	.D(D), .Q(Q), .C(C),
  	.CE(1'b1), .R(1'b0)
  );

endmodule

module \$lut (I, O);

  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] I;
  output O;

  generate
    if (WIDTH == 1) begin:lut1
      LUT1 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]));
    end else
    if (WIDTH == 2) begin:lut2
      LUT2 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]), .I1(I[1]));
    end else
    if (WIDTH == 3) begin:lut3
      LUT3 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]), .I1(I[1]), .I2(I[2]));
    end else
    if (WIDTH == 4) begin:lut4
      LUT4 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]), .I1(I[1]), .I2(I[2]),
        .I3(I[3]));
    end else
    if (WIDTH == 5) begin:lut5
      LUT5 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]), .I1(I[1]), .I2(I[2]),
        .I3(I[3]), .I4(I[4]));
    end else
    if (WIDTH == 6) begin:lut6
      LUT6 #(.INIT(LUT)) fpga_lut (.O(O),
        .I0(I[0]), .I1(I[1]), .I2(I[2]),
        .I3(I[3]), .I4(I[4]), .I5(I[5]));
    end else begin:error
      wire TECHMAP_FAIL;
    end
  endgenerate

endmodule
