`ifdef GUARD_5
module top;
	wire x;
endmodule

`elsif GUARD_4
`define GUARD_5
`include "include_self.v"

`elsif GUARD_3
`define GUARD_4
`include "include_self.v"

`elsif GUARD_2
`define GUARD_3
`include "include_self.v"

`elsif GUARD_1
`define GUARD_2
`include "include_self.v"

`elsif GUARD_0
`define GUARD_1
`include "include_self.v"

`else
`define GUARD_0
`include "include_self.v"

`endif
