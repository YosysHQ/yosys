#!/bin/bash
set -ex

for iter in {1..100}
do
	SZA=$(( 3 + $RANDOM % 13 ))
	SZB=$(( 3 + $RANDOM % 13 ))
	SZO=$(( 3 + $RANDOM % 29 ))

	C0=clk$(( $RANDOM & 1))
	C1=clk$(( $RANDOM & 1))
	C2=clk$(( $RANDOM & 1))
	C3=clk$(( $RANDOM & 1))

	E0=$( test $(( $RANDOM & 1 )) -eq 0 && echo posedge || echo negedge )
	E1=$( test $(( $RANDOM & 1 )) -eq 0 && echo posedge || echo negedge )
	E2=$( test $(( $RANDOM & 1 )) -eq 0 && echo posedge || echo negedge )
	E3=$( test $(( $RANDOM & 1 )) -eq 0 && echo posedge || echo negedge )

	SP=$( test $(( $RANDOM & 1 )) -eq 0 && echo S || echo P )

	RC=$( test $(( $RANDOM & 1 )) -eq 0 && echo "reset" || echo "!reset" )
	RV="32'h$( echo $RANDOM | md5sum | cut -c1-8 )"

	cat > test_dsp_map_top.v << EOT
module top (
	input clk0, clk1, reset,
	input  [$SZA:0] A,
	input  [$SZB:0] B,
	output [$SZO:0] O
);
	reg [15:0] AA, BB;
	reg [31:0] P, S;

	always @($E0 $C0) AA <= A;
	always @($E1 $C1) BB <= B;
	always @($E2 $C2) P <= AA * BB;
	always @($E3 $C3) S <= $RC ? $RV : S + P;
	assign O = $SP;
endmodule
EOT

	cat > test_dsp_map_tb.v << EOT
\`timescale 1ns / 1ps
module testbench;
	reg clk1, clk0, reset;
	reg [$SZA:0] A;
	reg [$SZB:0] B;

	wire [$SZO:0] O_top, O_syn;

	top top_inst (.clk0(clk0), .clk1(clk1), .reset(reset), .A(A), .B(B), .O(O_top));
	syn syn_inst (.clk0(clk0), .clk1(clk1), .reset(reset), .A(A), .B(B), .O(O_syn));

	initial begin
		// \$dumpfile("test_dsp_map.vcd");
		// \$dumpvars(0, testbench);

		#2;
		clk0 = 0;
		clk1 = 0;
		reset = 1;
		reset = $RC;
		A = 0;
		B = 0;

		repeat (3) begin
			#2; clk0 = ~clk0;
			#2; clk0 = ~clk0;
			#2; clk1 = ~clk1;
			#2; clk1 = ~clk1;
		end

		repeat (100) begin
			#2;
			A = \$urandom;
			B = \$urandom;
			reset = \$urandom & \$urandom & \$urandom & \$urandom;
			if (\$urandom & 1) begin
				#2; clk0 = ~clk0;
				#2; clk0 = ~clk0;
			end else begin
				#2; clk1 = ~clk1;
				#2; clk1 = ~clk1;
			end
			#2;
			if (O_top !== O_syn) begin
				\$display("ERROR: O_top=%b O_syn=%b", O_top, O_syn);
				\$stop;
			end
			// \$display("OK O_top=O_syn=%b", O_top);
		end

		\$display("Test passed.");
		\$finish;
	end
endmodule
EOT

	../../../yosys -p 'read_verilog test_dsp_map_top.v; synth_ice40 -dsp; rename top syn; write_verilog test_dsp_map_syn.v'
	iverilog -o test_dsp_map -s testbench test_dsp_map_tb.v test_dsp_map_top.v test_dsp_map_syn.v ../cells_sim.v
	vvp -N test_dsp_map
done

: ""
: "####  All tests passed.  ####"
: ""
