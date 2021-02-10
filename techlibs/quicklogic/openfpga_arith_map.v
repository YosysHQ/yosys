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

        // First in chain
        generate if (i == 0) begin

            // CI connected to a constant
            if (_TECHMAP_CONSTMSK_CI_ == 1) begin

                localparam INIT = (_TECHMAP_CONSTVAL_CI_ == 0) ?
                    16'b0110_0000_0000_0001 :
                    16'b1001_0000_0000_0111;

                // LUT4 configured as 1-bit adder with CI=const
                adder_lut4 #(
                    .LUT(INIT),
                    .IN2_IS_CIN(1'b0)
                ) lut_ci_adder (
                    .in({AA[i], BB[i], 1'b0, 1'b0}), 
                    .cin(), 
                    .lut4_out(Y[i]), 
                    .cout(ci)
                );

            // CI connected to a non-const driver
            end else begin

                // LUT4 configured as passthrough to drive CI of the next stage
                adder_lut4 #(
                    .LUT(16'b1100_0000_0000_0011),
                    .IN2_IS_CIN(1'b0)
                ) lut_ci (
                    .in({1'b0,CI,1'b0,1'b0}), 
                    .cin(), 
                    .lut4_out(), 
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
            adder_lut4 #(
                    .LUT(16'b0110_1001_0110_0001),
                    .IN2_IS_CIN(1'b1)
                ) lut_adder (
                    .in({AA[i], BB[i], 1'b0, 1'b0}),
                    .cin(ci), 
                    .lut4_out(Y[i]), 
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
            adder_lut4 #(
                    .LUT(16'b0000_1111_0000_1111),
                    .IN2_IS_CIN(1'b1)
                ) lut_co (
                    .in({1'b0, co, 1'b0, 1'b0}),
                    .cin(co),
                    .lut4_out(C[i]),
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
