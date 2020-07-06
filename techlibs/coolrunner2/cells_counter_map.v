module \$__COUNT_ (CE, CLK, OUT, POUT, RST, UP);

    input wire CE;
    input wire CLK;
    output wire OUT;
    (* force_downto *)
    output wire[WIDTH-1:0] POUT;
    input wire RST;
    input wire UP;

    parameter COUNT_TO = 1;
    parameter RESET_MODE = "RISING";
    parameter RESET_TO_MAX = 0;
    parameter HAS_POUT = 0;
    parameter HAS_CE = 0;
    parameter WIDTH = 8;
    parameter DIRECTION = "DOWN";

    if (DIRECTION == "UP") begin
        if (WIDTH < 2) begin
            initial begin
                $display("ERROR: \$__COUNT_ must be at least 2 bits wide (bug in extract_counter pass?).");
                $finish;
            end
        end

        // FIXME: Max width?

        assign OUT = POUT == COUNT_TO;

        if (HAS_CE) begin
            genvar i;
            for (i = 0; i < WIDTH; i++) begin: countbits
                // each bit = (cur & !reset) ^ (all prev & !reset)
                wire xor_to_mc_bitn;
                FDCP #(
                    .INIT(0)
                ) bitn_ff (
                    .C(CLK),
                    .CLR(0),
                    .D(xor_to_mc_bitn),
                    .PRE(0),
                    .Q(POUT[i])
                );
                wire orterm_to_xor_bitn;
                wire pterm0_to_or_bitn;
                wire pterm1_to_or_bitn;
                MACROCELL_XOR #(
                    .INVERT_OUT(0)
                ) bitn_xor (
                    .IN_ORTERM(orterm_to_xor_bitn),
                    .IN_PTC(pterm1_to_or_bitn),
                    .OUT(xor_to_mc_bitn)
                );
                ORTERM #(
                    .WIDTH(1)
                ) bitn_or (
                    .IN(pterm0_to_or_bitn),
                    .OUT(orterm_to_xor_bitn)
                );
                ANDTERM #(
                    .COMP_INP(1),
                    .TRUE_INP(1)
                ) bitn_pterm0 (
                    .IN(POUT[i]),
                    .IN_B(OUT),
                    .OUT(pterm0_to_or_bitn)
                );
                ANDTERM #(
                    .COMP_INP(1),
                    .TRUE_INP(i + 1)
                ) bitn_pterm1 (
                    .IN({POUT[i-1:0], CE}),
                    .IN_B(OUT),
                    .OUT(pterm1_to_or_bitn)
                );
            end
        end else begin
            // Bit0 is special; toggle unless reset
            // cur  reset           out
            // 0    0               1
            // 0    1               0
            // 1    0               0
            // 1    1               0
            wire xor_to_mc_bit0;
            FDCP #(
                .INIT(0)
            ) bit0_ff (
                .C(CLK),
                .CLR(0),
                .D(xor_to_mc_bit0),
                .PRE(0),
                .Q(POUT[0])
            );
            wire pterm_to_xor_bit0;
            MACROCELL_XOR #(
                .INVERT_OUT(0)
            ) bit0_xor (
                .IN_PTC(pterm_to_xor_bit0),
                .OUT(xor_to_mc_bit0)
            );
            ANDTERM #(
                .COMP_INP(2),
                .TRUE_INP(0)
            ) bit0_pterm (
                .IN(),
                .IN_B({POUT[0], OUT}),
                .OUT(pterm_to_xor_bit0)
            );

            genvar i;
            for (i = 1; i < WIDTH; i++) begin: countbits
                // each bit = (cur & !reset) ^ (all prev & !reset)
                wire xor_to_mc_bitn;
                FDCP #(
                    .INIT(0)
                ) bitn_ff (
                    .C(CLK),
                    .CLR(0),
                    .D(xor_to_mc_bitn),
                    .PRE(0),
                    .Q(POUT[i])
                );
                wire orterm_to_xor_bitn;
                wire pterm0_to_or_bitn;
                wire pterm1_to_or_bitn;
                MACROCELL_XOR #(
                    .INVERT_OUT(0)
                ) bitn_xor (
                    .IN_ORTERM(orterm_to_xor_bitn),
                    .IN_PTC(pterm1_to_or_bitn),
                    .OUT(xor_to_mc_bitn)
                );
                ORTERM #(
                    .WIDTH(1)
                ) bitn_or (
                    .IN(pterm0_to_or_bitn),
                    .OUT(orterm_to_xor_bitn)
                );
                ANDTERM #(
                    .COMP_INP(1),
                    .TRUE_INP(1)
                ) bitn_pterm0 (
                    .IN(POUT[i]),
                    .IN_B(OUT),
                    .OUT(pterm0_to_or_bitn)
                );
                ANDTERM #(
                    .COMP_INP(1),
                    .TRUE_INP(i)
                ) bitn_pterm1 (
                    .IN(POUT[i-1:0]),
                    .IN_B(OUT),
                    .OUT(pterm1_to_or_bitn)
                );
            end
        end
    end

    // FIXME: down counters

endmodule
