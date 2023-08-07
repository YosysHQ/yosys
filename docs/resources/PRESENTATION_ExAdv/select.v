module test(clk, s, a, y);
    input clk, s;
    input [15:0] a;
    output [15:0] y;
    reg [15:0] b, c;

    always @(posedge clk) begin
        b <= a;
        c <= b;
    end

    wire [15:0] state_a = (a ^ b) + c;
    wire [15:0] state_b = (a ^ b) - c;
    assign y = !s ? state_a : state_b;
endmodule
