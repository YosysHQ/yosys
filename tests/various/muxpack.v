module mux_if_unbal_4_1 #(parameter N=4, parameter W=1) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @*
    if (s == 0) o <= i[0*W+:W];
    else if (s == 1) o <= i[1*W+:W];
    else if (s == 2) o <= i[2*W+:W];
    else if (s == 3) o <= i[3*W+:W];
    else o <= {W{1'bx}};
endmodule

module mux_if_unbal_5_3 #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {W{1'bx}};
    if (s == 0) o <= i[0*W+:W];
    if (s == 1) o <= i[1*W+:W];
    if (s == 2) o <= i[2*W+:W];
    if (s == 3) o <= i[3*W+:W];
    if (s == 4) o <= i[4*W+:W];
end
endmodule

module mux_if_unbal_5_3_invert #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @*
    if (s != 0) 
	   	if (s != 1) 
			if (s != 2)
				if (s != 3)
					if (s != 4) o <= i[4*W+:W];
					else o <= i[0*W+:W];
				else o <= i[3*W+:W];
			else o <= i[2*W+:W];
		else o <= i[1*W+:W];
    else o <= {W{1'bx}};
endmodule

module mux_if_unbal_5_3_width_mismatch #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {W{1'bx}};
    if (s == 0) o <= i[0*W+:W];
    if (s == 1) o <= i[1*W+:W];
    if (s == 2) o[W-2:0] <= i[2*W+:W-1];
    if (s == 3) o <= i[3*W+:W];
    if (s == 4) o <= i[4*W+:W];
end
endmodule

module mux_if_unbal_4_1_missing #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    if (s == 0) o <= i[0*W+:W];
//    else if (s == 1) o <= i[1*W+:W];
//    else if (s == 2) o <= i[2*W+:W];
    else if (s == 3) o <= i[3*W+:W];
    else o <= {W{1'bx}};
end
endmodule

module mux_if_unbal_5_3_order #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {W{1'bx}};
    if (s == 3) o <= i[3*W+:W];
    if (s == 2) o <= i[2*W+:W];
    if (s == 1) o <= i[1*W+:W];
    if (s == 4) o <= i[4*W+:W];
    if (s == 0) o <= i[0*W+:W];
end
endmodule

module mux_if_unbal_4_1_nonexcl #(parameter N=4, parameter W=1) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @*
    if (s == 0) o <= i[0*W+:W];
    else if (s == 1) o <= i[1*W+:W];
    else if (s == 2) o <= i[2*W+:W];
    else if (s == 3) o <= i[3*W+:W];
	else if (s == 0) o <= {W{1'b0}};
    else o <= {W{1'bx}};
endmodule

module mux_if_unbal_5_3_nonexcl #(parameter N=5, parameter W=3) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {W{1'bx}};
    if (s == 0) o <= i[0*W+:W];
    if (s == 1) o <= i[1*W+:W];
    if (s == 2) o <= i[2*W+:W];
    if (s == 3) o <= i[3*W+:W];
    if (s == 4) o <= i[4*W+:W];
	if (s == 0) o <= i[2*W+:W];
end
endmodule

module mux_case_unbal_8_7#(parameter N=8, parameter W=7) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @* begin
    o <= {W{1'bx}};
    case (s)
    0: o <= i[0*W+:W];
    default:
        case (s)
        1: o <= i[1*W+:W];
        2: o <= i[2*W+:W];
        default:
            case (s)
            3: o <= i[3*W+:W];
            4: o <= i[4*W+:W];
            5: o <= i[5*W+:W];
            default:
                case (s)
                    6: o <= i[6*W+:W];
                    default: o <= i[7*W+:W];
                endcase
            endcase
        endcase
    endcase
end
endmodule

module mux_if_bal_8_2 #(parameter N=8, parameter W=2) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @*
    if (s[0] == 1'b0)
     if (s[1] == 1'b0)
      if (s[2] == 1'b0)
       o <= i[0*W+:W];
      else
       o <= i[1*W+:W];
     else
      if (s[2] == 1'b0)
       o <= i[2*W+:W];
      else
       o <= i[3*W+:W];
    else
     if (s[1] == 1'b0)
      if (s[2] == 1'b0)
       o <= i[4*W+:W];
      else
       o <= i[5*W+:W];
     else
      if (s[2] == 1'b0)
       o <= i[6*W+:W];
      else
       o <= i[7*W+:W];
endmodule

module mux_if_bal_5_1 #(parameter N=5, parameter W=1) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
always @*
    if (s[0] == 1'b0)
     if (s[1] == 1'b0)
      if (s[2] == 1'b0)
       o <= i[0*W+:W];
      else
       o <= i[1*W+:W];
     else
      if (s[2] == 1'b0)
       o <= i[2*W+:W];
      else
       o <= i[3*W+:W];
    else
     o <= i[4*W+:W];
endmodule

module cliffordwolf_nonexclusive_select (
        input wire x, y, z,
        input wire a, b, c, d,
        output reg o
);
        always @* begin
                o = a;
                if (x) o = b;
                if (y) o = c;
                if (z) o = d;
        end
endmodule

module cliffordwolf_freduce (
        input wire [1:0] s,
        input wire a, b, c, d,
        output reg [3:0] o
);
        always @* begin
                o = {4{a}};
                if (s == 0) o = {3{b}};
                if (s == 1) o = {2{c}};
                if (s == 2) o = d;
        end
endmodule

module case_nonexclusive_select (
        input wire [1:0] x, y,
        input wire a, b, c, d, e,
        output reg o
);
        always @* begin
            case (x)
                0: o = b;
                2: o = b;
                1: o = c;
                default: begin
                    o = a;
                    if (y == 0) o = d;
                    if (y == 1) o = e;
                end
        endcase
        end
endmodule

module case_nonoverlap (
        input wire [2:0] x,
        input wire a, b, c, d, e,
        output reg o
);
        always @* begin
            case (x)
                0, 2: o = b; // Creates $reduce_or
                1: o = c;
                default:
                    case (x)
                        3: o = d; 4: o = d; // Creates $reduce_or
                        5: o = e;
                        default: o = 1'b0;
                    endcase
        endcase
        end
endmodule

module case_overlap (
        input wire [2:0] x,
        input wire a, b, c, d, e,
        output reg o
);
        always @* begin
            case (x)
                0, 2: o = b; // Creates $reduce_or
                1: o = c;
                default:
                    case (x)
                        0: o = 1'b1; // OVERLAP!
                        3, 4: o = d; // Creates $reduce_or
                        5: o = e;
                        default: o = 1'b0;
                    endcase
        endcase
        end
endmodule

module case_overlap2 (
        input wire [2:0] x,
        input wire a, b, c, d, e,
        output reg o
);
        always @* begin
            case (x)
                0: o = b; 2: o = b; // Creates $reduce_or
                1: o = c;
                default:
                    case (x)
                        0: o = d; 2: o = d; // Creates $reduce_or
                        3: o = d; 4: o = d; // Creates $reduce_or
                        5: o = e;
                        default: o = 1'b0;
                    endcase
        endcase
        end
endmodule
