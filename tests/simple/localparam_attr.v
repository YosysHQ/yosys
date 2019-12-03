module uut_localparam_attr (I, O);

(* LOCALPARAM_ATTRIBUTE = "attribute_content" *)
localparam WIDTH = 1;

input  wire [WIDTH-1:0] I;
output wire [WIDTH-1:0] O;

assign O = I;

endmodule
