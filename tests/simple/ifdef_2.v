module top(o1, o2, o3);

output wire o1;

`define COND_1
`define COND_2
`define COND_3

`ifdef COND_1
	output wire o2;
`elsif COND_2
	input wire dne1;
`elsif COND_3
	input wire dne2;
`else
	input wire dne3;
`endif

output wire o3;

endmodule
