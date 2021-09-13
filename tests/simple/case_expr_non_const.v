// Note: case_expr_{,non_}const.v should be modified in tandem to ensure both
// the constant and non-constant case evaluation logic is covered
module top(
	// expected to output all 1s
    output reg a, b, c, d, e, f, g, h
);
    reg x_1b0 = 1'b0;
    reg x_1b1 = 1'b1;
    reg signed x_1sb0 = 1'sb0;
    reg signed x_1sb1 = 1'sb1;
    reg [1:0] x_2b0 = 2'b0;
    reg [1:0] x_2b11 = 2'b11;
    reg signed [1:0] x_2sb01 = 2'sb01;
    reg signed [1:0] x_2sb11 = 2'sb11;
    reg [2:0] x_3b0 = 3'b0;

    initial begin
        case (x_2b0)
            x_1b0:   a = 1;
            default: a = 0;
        endcase
        case (x_2sb11)
            x_2sb01: b = 0;
            x_1sb1:  b = 1;
        endcase
        case (x_2sb11)
            x_1sb0:  c = 0;
            x_1sb1:  c = 1;
        endcase
        case (x_2sb11)
            x_1b0:   d = 0;
            x_1sb1:  d = 0;
            default: d = 1;
        endcase
        case (x_2b11)
            x_1sb0:  e = 0;
            x_1sb1:  e = 0;
            default: e = 1;
        endcase
        case (x_1sb1)
            x_1sb0:  f = 0;
            x_2sb11: f = 1;
            default: f = 0;
        endcase
        case (x_1sb1)
            x_1sb0:  g = 0;
            x_3b0:   g = 0;
            x_2sb11: g = 0;
            default: g = 1;
        endcase
        case (x_1sb1)
            x_1sb0:  h = 0;
            x_1b1:   h = 1;
            x_3b0:   h = 0;
            x_2sb11: h = 0;
            default: h = 0;
        endcase
    end
endmodule
