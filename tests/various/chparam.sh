#!/bin/bash

trap 'echo "ERROR in chparam.sh" >&2; exit 1' ERR

cat > chparam1.sv << "EOT"
module top #(
        parameter [31:0] X = 0
) (
        input [31:0] din,
        output [31:0] dout
);
        assign dout = X-din;
endmodule

module top_props #(
        parameter [31:0] X = 0
) (
        input [31:0] dout
);
        always @* assert (dout != X);
endmodule

bind top top_props #(.X(123456789)) props (.*);
EOT

cat > chparam2.sv << "EOT"
module top #(
	parameter [31:0] X = 0
) (
	input [31:0] din,
	output [31:0] dout
);
	assign dout = X-din;
	always @* assert (dout != 123456789);
endmodule
EOT

if ../../yosys -q -p 'verific -sv chparam1.sv'; then
	../../yosys -q -p 'verific -sv chparam1.sv; hierarchy -chparam X 123123123 -top top; prep -flatten' \
			-p 'sat -verify -prove-asserts -show-ports -set din[0] 1' \
			-p 'sat -falsify -prove-asserts -show-ports -set din[0] 0'

	../../yosys -q -p 'verific -sv chparam2.sv; hierarchy -chparam X 123123123 -top top; prep -flatten' \
			-p 'sat -verify -prove-asserts -show-ports -set din[0] 1' \
			-p 'sat -falsify -prove-asserts -show-ports -set din[0] 0'
fi
../../yosys -q -p 'read_verilog -sv chparam2.sv; hierarchy -chparam X 123123123 -top top; prep -flatten' \
		-p 'sat -verify -prove-asserts -show-ports -set din[0] 1' \
		-p 'sat -falsify -prove-asserts -show-ports -set din[0] 0'

rm chparam1.sv
rm chparam2.sv
