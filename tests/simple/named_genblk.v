`default_nettype none
module top;
	generate
		if (1) begin
			wire t;
			begin : foo
				wire x;
			end
			wire u;
		end
		begin : bar
			wire x;
			wire y;
			begin : baz
				wire x;
				wire z;
			end
		end
	endgenerate
	assign genblk1.t = 1;
	assign genblk1.foo.x = 1;
	assign genblk1.u = 1;
	assign bar.x = 1;
	assign bar.y = 1;
	assign bar.baz.x = 1;
	assign bar.baz.z = 1;
endmodule
