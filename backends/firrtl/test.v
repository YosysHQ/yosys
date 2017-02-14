module test(
	input clk, wen,
	input [7:0] uns,
	input signed [7:0] a, b,
	input signed [23:0] c,
	input signed [2:0] sel,
	output [15:0] s, d, y, z, u, q, p, mul, div, mod, mux, And, Or, Xor, eq, neq, gt, lt, geq, leq, eqx, shr, sshr, shl, sshl, Land, Lor, Lnot, Not, Neg, pos, Andr, Orr, Xorr, Xnorr, Reduce_bool,
        output [7:0] PMux
);
        //initial begin
          //$display("shr = %b", shr);
        //end
	assign s = a+{b[6:2], 2'b1};
	assign d = a-b;
	assign y = x;
	assign z[7:0] = s+d;
	assign z[15:8] = s-d;
        assign p = a & b | x;
        assign mul = a * b;
        assign div = a / b;
        assign mod = a % b;
        assign mux = x[0] ? a : b;
        assign And = a & b;
        assign Or = a | b;
        assign Xor = a ^ b;
        assign Not = ~a;
        assign Neg = -a;
        assign eq = a == b;
        assign neq = a != b;
        assign gt = a > b;
        assign lt = a < b;
        assign geq = a >= b;
        assign leq = a <= b;
        assign eqx = a === b;
        assign shr = a >> b; //0111111111000000
        assign sshr = a >>> b;
        assign shl = a << b;
        assign sshl = a <<< b;
        assign Land = a && b;
        assign Lor = a || b;
        assign Lnot = !a;
        assign pos = $signed(uns);
        assign Andr = &a;
        assign Orr = |a;
        assign Xorr = ^a;
        assign Xnorr = ~^a;
        always @*
          if(!a) begin
             Reduce_bool = a;
          end else begin
             Reduce_bool = b;
          end
        //always @(sel or c or a)
        //  begin
        //    case (sel)
        //      3'b000: PMux = a;
        //      3'b001: PMux = c[7:0];
        //      3'b010: PMux = c[15:8];
        //      3'b100: PMux = c[23:16];
        //    endcase
        //  end

endmodule
