module top (
    input  wire        clk,
    input  wire        rst,
    input  wire [7:0]  a,
    input  wire [7:0]  b,
    input  wire [3:0]  c,
    input  wire        en,
    output wire [7:0]  out1,
    output wire [7:0]  out2
);

    // Shared intermediate signal
    wire [7:0] ab_sum;
    assign ab_sum = a + b;

    // Logic cone for out1
    wire [7:0] cone1_1, cone1_2;
    assign cone1_1 = ab_sum ^ {4{c[1:0]}};
    assign cone1_2 = (a & b) | {4{c[3:2]}};

    reg  [7:0] reg1, reg2; // only reg1 feeds into out1, but both share a source location
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            reg1 <= 8'h00;
            reg2 <= 8'hFF;
        end else if (en) begin
            reg1 <= cone1_1 + cone1_2;
            reg2 <= cone1_2 - cone1_1;
        end
    end

    wire [7:0] cone1_3;
    assign cone1_3 = reg1 & ~a[0];

    // Logic cone for out2
    wire [7:0] cone2_1, cone2_2;
    assign cone2_1 = (ab_sum << 1) | (a >> 2);
    assign cone2_2 = (b ^ {4{c[2:0]}}) & 8'hAA;

    reg  [7:0] reg3;
    always @(posedge clk or posedge rst) begin
        if (rst)
            reg3 <= 8'h0F;
        else
            reg3 <= cone2_1 ^ cone2_2 ^ reg1[7:0];
    end

    wire [7:0] cone2_3;
    assign cone2_3 = reg3 | (reg2 ^ 8'h55);

    // Outputs
    assign out1 = cone1_3 | (reg1 ^ 8'hA5);
    assign out2 = cone2_3 & (reg3 | 8'h5A);

    always @(posedge clk) begin
        assert (out1 == 8'h42);
    end

endmodule
