#!/bin/bash

trap 'echo "ERROR in sv_implicit_ports.sh" >&2; exit 1' ERR

# Simple case
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
	assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	wire [7:0] b = 8'd42;
	add add_i(.*);
endmodule
EOT

# Generate block
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	generate
	if (1) begin:ablock
		wire [7:0] b = 8'd42;
		add add_i(.*);
	end
	endgenerate
endmodule
EOT

# Missing wire
((../../yosys -f "verilog -sv" -qp "hierarchy -top top" - || true) <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
	assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	add add_i(.*);
endmodule
EOT
) 2>&1 | grep -F "ERROR: No matching wire for implicit port connection \`b' of cell top.add_i (add)." > /dev/null

# Incorrectly sized wire
((../../yosys -f "verilog -sv" -qp "hierarchy -top top" - || true) <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
	assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	wire [6:0] b = 6'd42;
	add add_i(.*);
endmodule
EOT
) 2>&1 | grep -F "ERROR: Width mismatch between wire (7 bits) and port (8 bits) for implicit port connection \`b' of cell top.add_i (add)." > /dev/null

# Defaults
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add(input [7:0] a = 8'd00, input [7:0] b = 8'd01, output [7:0] q);
assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	add add_i(.*);
endmodule
EOT

# Parameterised module
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add #(parameter N=3) (input [N-1:0] a = 8'd00, input [N-1:0] b = 8'd01, output [N-1:0] q);
assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	add #(.N(8)) add_i(.*);
endmodule
EOT

# Parameterised blackbox module
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:add" - <<EOT
(* blackbox *)
module add #(parameter N=3) (input [N-1:0] a, b, output [N-1:0] q);
endmodule

module top(input [7:0] a, b, output [7:0] q);
	add #(.N(8)) add_i(.*);
endmodule
EOT

# Parameterised blackbox module - incorrect width
((../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:add" - || true) <<EOT
(* blackbox *)
module add #(parameter N=3) (input [N-1:0] a, b, output [N-1:0] q);
endmodule

module top(input [7:0] a, b, output [7:0] q);
	add #(.N(6)) add_i(.*);
endmodule
EOT
) 2>&1 | grep -F "ERROR: Width mismatch between wire (8 bits) and port (6 bits) for implicit port connection \`q' of cell top.add_i (add)." > /dev/null

# Mixed implicit and explicit 1
../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
	assign q = a + b;
endmodule

module top(input [7:0] a, output [7:0] q);
	add add_i(.b(8'd42), .*);
endmodule
EOT

# Mixed implicit and explicit 2
(../../yosys -f "verilog -sv" -qp "prep -flatten -top top; select -assert-count 1 t:\$add" - <<EOT
module add(input [7:0] a, input [7:0] b, output [7:0] q);
	assign q = a + b;
endmodule

module top(input [7:0] a, input [9:0] b, output [7:0] q);
	add add_i(.b, .*);
endmodule
EOT
) 2>&1 | grep -F "Warning: Resizing cell port top.add_i.b from 10 bits to 8 bits." > /dev/null
