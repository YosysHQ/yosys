`ifndef NO_LUT
module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    generate
        if (WIDTH == 1) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(1'b0), .C(1'b0), .D(1'b0));
        end else
        if (WIDTH == 2) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(1'b0), .D(1'b0));
        end else
        if (WIDTH == 3) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(1'b0));
        end else
        if (WIDTH == 4) begin
            LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Z(Y),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
        `ifndef NO_PFUMUX
        end else
        if (WIDTH == 5) begin
            wire f0, f1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            PFUMX mux5(.ALUT(f1), .BLUT(f0), .SD(A[4]), .Z(Y));
        end else
        if (WIDTH == 6) begin
            wire f0, f1, f2, f3, g0, g1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .SD(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .SD(A[4]), .Z(g1));
            L6MUX21 mux6 (.D0(g0), .D1(g1), .SD(A[5]), .Z(Y));
        end else
        if (WIDTH == 7) begin
            wire f0, f1, f2, f3, f4, f5, f6, f7, g0, g1, g2, g3, h0, h1;
            LUT4 #(.INIT(LUT[15: 0])) lut0 (.Z(f0),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[31:16])) lut1 (.Z(f1),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[47:32])) lut2 (.Z(f2),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[63:48])) lut3 (.Z(f3),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[79:64])) lut4 (.Z(f4),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[95:80])) lut5 (.Z(f5),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            LUT4 #(.INIT(LUT[111: 96])) lut6 (.Z(f6),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
            LUT4 #(.INIT(LUT[127:112])) lut7 (.Z(f7),
                .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));

            PFUMX mux50(.ALUT(f1), .BLUT(f0), .SD(A[4]), .Z(g0));
            PFUMX mux51(.ALUT(f3), .BLUT(f2), .SD(A[4]), .Z(g1));
            PFUMX mux52(.ALUT(f5), .BLUT(f4), .SD(A[4]), .Z(g2));
            PFUMX mux53(.ALUT(f7), .BLUT(f6), .SD(A[4]), .Z(g3));
            L6MUX21 mux60 (.D0(g0), .D1(g1), .SD(A[5]), .Z(h0));
            L6MUX21 mux61 (.D0(g2), .D1(g3), .SD(A[5]), .Z(h1));
            L6MUX21 mux7  (.D0(h0), .D1(h1), .SD(A[6]), .Z(Y));
        `endif
        end else begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule
`endif
