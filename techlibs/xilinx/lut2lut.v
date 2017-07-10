module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  \$lut #(
    .WIDTH(1),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A(I0),
    .Y(O)
  );
endmodule

module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  \$lut #(
    .WIDTH(2),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A({I1, I0}),
    .Y(O)
  );
endmodule

module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  \$lut #(
    .WIDTH(3),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A({I2, I1, I0}),
    .Y(O)
  );
endmodule

module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  \$lut #(
    .WIDTH(4),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A({I3, I2, I1, I0}),
    .Y(O)
  );
endmodule

module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  \$lut #(
    .WIDTH(5),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A({I4, I3, I2, I1, I0}),
    .Y(O)
  );
endmodule

module LUT6(output O, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  \$lut #(
    .WIDTH(6),
    .LUT(INIT)
  ) _TECHMAP_REPLACE_ (
    .A({I5, I4, I3, I2, I1, I0}),
    .Y(O)
  );
endmodule
