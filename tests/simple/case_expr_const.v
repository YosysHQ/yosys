// Note: case_expr_{,non_}const.v should be modified in tandem to ensure both
// the constant and non-constant case evaluation logic is covered
module top(
	// expected to output all 1s
    output reg a, b, c, d, e, f, g, h
);
    initial begin
        case (2'b0)
            1'b0:    a = 1;
            default: a = 0;
        endcase
        case (2'sb11)
            2'sb01:  b = 0;
            1'sb1:   b = 1;
        endcase
        case (2'sb11)
            1'sb0:   c = 0;
            1'sb1:   c = 1;
        endcase
        case (2'sb11)
            1'b0:    d = 0;
            1'sb1:   d = 0;
            default: d = 1;
        endcase
        case (2'b11)
            1'sb0:   e = 0;
            1'sb1:   e = 0;
            default: e = 1;
        endcase
        case (1'sb1)
            1'sb0:   f = 0;
            2'sb11:  f = 1;
            default: f = 0;
        endcase
        case (1'sb1)
            1'sb0:   g = 0;
            3'b0:    g = 0;
            2'sb11:  g = 0;
            default: g = 1;
        endcase
        case (1'sb1)
            1'sb0:   h = 0;
            1'b1:    h = 1;
            3'b0:    h = 0;
            2'sb11:  h = 0;
            default: h = 0;
        endcase
    end
endmodule
