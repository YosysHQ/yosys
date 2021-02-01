(* techmap_celltype = "$alu" *)
module _80_quicklogic_alu (A, B, CI, BI, X, Y, CO);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH  = 1;
    parameter B_WIDTH  = 1;
    parameter Y_WIDTH  = 1;

    parameter _TECHMAP_CONSTMSK_CI_ = 0;
    parameter _TECHMAP_CONSTVAL_CI_ = 0;

    (* force_downto *)
    input [A_WIDTH-1:0] A;
    (* force_downto *)
    input [B_WIDTH-1:0] B;
    (* force_downto *)
    output [Y_WIDTH-1:0] X, Y;

    input CI, BI;
    (* force_downto *)
    output [Y_WIDTH-1:0] CO;

    wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

    (* force_downto *)
    wire [Y_WIDTH-1:0] A_buf, B_buf;
    \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
    \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

    (* force_downto *)
    wire [Y_WIDTH-1:0] AA = A_buf;
    (* force_downto *)
    wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
    (* force_downto *)
    wire [Y_WIDTH-1:0] C;

    assign CO = C[Y_WIDTH-1];

    genvar i;
    generate for (i = 0; i < Y_WIDTH; i = i + 1) begin: slice

        wire ci;
        wire co;

        wire [0:1] lut2_out_1;
        wire [0:1] lut2_out_2;
        wire [0:1] lut2_out_3;

        // First in chain
        generate if (i == 0) begin

            // CI connected to a constant
            if (_TECHMAP_CONSTMSK_CI_ == 1) begin

                localparam INIT = (_TECHMAP_CONSTVAL_CI_ == 0) ?
                    16'b0110_0000_0000_0001 :
                    16'b1001_0000_0000_0111;

                // LUT4 configured as 1-bit adder with CI=const
                frac_lut4 #(
                    .LUT(INIT)
                ) lut_inst_1 (
                    .in({AA[i], BB[i], 1'b0, 1'b0}),
                    .lut2_out(lut2_out_1),
                    .lut4_out(Y[i])
                );
                carry_follower carry_inst_1(
                    .a(lut2_out_1[1]),
                    .b(),
                    .cin(lut2_out_1[0]),
                    .cout(ci)
                );

            // CI connected to a non-const driver
            end else begin

                // LUT4 configured as passthrough to drive CI of the next stage
                frac_lut4 #(
                    .LUT(16'b1100_0000_0000_0011)
                ) lut_inst_2 (
                    .in({1'b0, CI, 1'b0, 1'b0}),
                    .lut2_out(lut2_out_1),
                    .lut4_out()
                );
                carry_follower carry_inst_2(
                    .a(lut2_out_1[1]),
                    .b(),
                    .cin(lut2_out_1[0]),
                    .cout(ci)
                );
            end

        // Not first in chain
        end else begin
            assign ci = C[i-1];

        end endgenerate

        // ....................................................

        // Single 1-bit adder, mid-chain adder or non-const CI
        // adder
        generate if ((i == 0 && _TECHMAP_CONSTMSK_CI_ == 0) || (i > 0)) begin
            
            // LUT4 configured as full 1-bit adder
            frac_lut4 #(
                .LUT(16'b0110_1001_0110_0001)
            ) lut_inst_3 (
                .in({AA[i], BB[i], ci, 1'b0}),
                .lut2_out(lut2_out_2),
                .lut4_out(Y[i])
            );
            carry_follower carry_inst_3(
                .a(lut2_out_2[1]),
                .b(ci),
                .cin(lut2_out_2[0]),
                .cout(co)
            );
                         
        end else begin
            assign co = ci;

        end endgenerate

        // ....................................................

        // Last in chain
        generate if (i == Y_WIDTH-1) begin

            // LUT4 configured for passing its CI input to output. This should
            // get pruned if the actual CO port is not connected anywhere.
            frac_lut4 #(
                .LUT(16'b0000_1111_0000_1111)
            ) lut_inst_4 (
                .in({1'b0, co, 1'b0, 1'b0}),
                .lut2_out(lut2_out_3),
                .lut4_out(C[i])
            );
            carry_follower carry_inst_4(
                .a(lut2_out_3[1]),
                .b(co),
                .cin(lut2_out_3[0]),
                .cout()
            );
        // Not last in chain
        end else begin
            assign C[i] = co;

        end endgenerate

    end: slice	  
    endgenerate

    /* End implementation */
    assign X = AA ^ BB;
endmodule
