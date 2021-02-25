module top(o1, o2, o3, o4);

`define FAIL input wire not_a_port;

`ifdef COND_1
	`FAIL
`elsif COND_2
	`FAIL
`elsif COND_3
	`FAIL
`elsif COND_4
	`FAIL
`else

	`define COND_4
	output wire o4;

	`ifdef COND_1
		`FAIL
	`elsif COND_2
		`FAIL
	`elsif COND_3
		`FAIL
	`elsif COND_4

		`define COND_3
		output wire o3;

		`ifdef COND_1
			`FAIL
		`elsif COND_2
			`FAIL
		`elsif COND_3

			`define COND_2
			output wire o2;

			`ifdef COND_1
				`FAIL
			`elsif COND_2

				`define COND_1
				output wire o1;

				`ifdef COND_1

					`ifdef COND_1
					`elsif COND_2
						`FAIL
					`elsif COND_3
						`FAIL
					`elsif COND_4
						`FAIL
					`else
						`FAIL
					`endif

				`elsif COND_2
					`FAIL
				`elsif COND_3
					`FAIL
				`elsif COND_4
					`FAIL
				`else
					`FAIL
				`endif

			`elsif COND_3
				`FAIL
			`elsif COND_4
				`FAIL
			`else
				`FAIL
			`endif

		`elsif COND_4
			`FAIL
		`else
			`FAIL
		`endif

	`else
		`FAIL
	`endif

`endif

endmodule
