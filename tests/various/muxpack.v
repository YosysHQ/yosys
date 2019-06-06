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

module mux_if_unbal_5_3_nonexcl #(parameter N=4, parameter W=1) (input [N*W-1:0] i, input [$clog2(N)-1:0] s, output reg [W-1:0] o);
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
