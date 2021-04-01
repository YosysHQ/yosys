module \$lut (
  A, Y
);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(
        .EQN(""),
        .INIT(LUT)
      ) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0])
      );
    end else if (WIDTH == 2) begin
      LUT2 #(
        .EQN(""),
        .INIT(LUT)
      ) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1])
      );
    end else if (WIDTH == 3) begin
      LUT3 #(
        .EQN(""),
        .INIT(LUT)
      ) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2])
      );
    end else if (WIDTH == 4) begin
      LUT4 #(
        .EQN(""),
        .INIT(LUT)
      ) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3])
      );
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
