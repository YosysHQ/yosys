module uut_param_attr (I, O);

(* PARAMETER_ATTRIBUTE = "attribute_content" *)
parameter WIDTH = 1;

input  wire [WIDTH-1:0] I;
output wire [WIDTH-1:0] O;

assign O = I;

endmodule
