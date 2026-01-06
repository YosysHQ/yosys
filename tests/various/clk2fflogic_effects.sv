module top;

(* gclk *)
reg gclk;

reg clk = 0;
always @(posedge gclk)
    clk <= !clk;

reg [5:0] counter = 0;

reg eff_0_trg = '0;
reg eff_0_en = '0;

reg eff_1_trgA = '0;
reg eff_1_trgB = '0;
reg eff_1_en = '0;

reg eff_2_trgA = '0;
reg eff_2_trgB = '0;
reg eff_2_en = '0;

reg eff_3_trg = '0;
reg eff_3_en = '0;
reg eff_3_a = '0;

`ifdef FAST
always @(posedge gclk) begin
`else
always @(posedge clk) begin
`endif
    counter <= counter + 1;

    eff_0_trg = 32'b00000000000000110011001100101010 >> counter;
    eff_0_en <= 32'b00000000000001100000110110110110 >> counter;

    eff_1_trgA = 32'b00000000000000000011110000011110 >> counter;
    eff_1_trgB = 32'b00000000000000001111000001111000 >> counter;
    eff_1_en  <= 32'b00000000000000001010101010101010 >> counter;

    eff_2_trgA = counter[0];
    eff_2_trgB = !counter[0];
    eff_2_en  <= 32'b00000000000000000000001111111100 >> counter;

    eff_3_trg  = 32'b10101010101010101010101010101010 >> counter;
    eff_3_en  <= 32'b11101110010001001110111001000100 >> counter;
    eff_3_a   <= 32'b11111010111110100101000001010000 >> counter;
end

always @(posedge eff_0_trg)
    if (eff_0_en)
        $display("%02d: eff0 +", counter);

always @(negedge eff_0_trg)
    if (eff_0_en)
        $display("%02d: eff0 -", counter);

always @(posedge eff_0_trg, negedge eff_0_trg)
    if (eff_0_en)
        $display("%02d: eff0 *", counter);

always @(posedge eff_1_trgA, posedge eff_1_trgB)
    if (eff_1_en)
        $display("%02d: eff1 ++", counter);

always @(posedge eff_1_trgA, negedge eff_1_trgB)
    if (eff_1_en)
        $display("%02d: eff1 +-", counter);

always @(negedge eff_1_trgA, posedge eff_1_trgB)
    if (eff_1_en)
        $display("%02d: eff1 -+", counter);

always @(negedge eff_1_trgA, negedge eff_1_trgB)
    if (eff_1_en)
        $display("%02d: eff1 --", counter);

always @(posedge eff_2_trgA, posedge eff_2_trgB)
    if (eff_2_en)
        $display("repeated");

always @(posedge eff_3_trg)
    if (eff_3_en) begin
        $display("%02d: eff3 vvv", counter);
`ifdef NO_ASSERT
        if (!eff_3_a)
            $display("Failed assertion eff3 at");
`else
        eff3: assert(eff_3_a);
`endif
    end

`ifdef __ICARUS__
initial gclk = 0;
always @(gclk) gclk <= #5 !gclk;
always @(posedge gclk)
    if (counter == 32)
        $finish(0);
`endif

endmodule
