`timescale 1ns/1ns 
module tb_dlatchsr();
	reg d = 0;
	reg set = 0;
	reg clr = 0;
	wire q;

	dlatchsr uut(.d(d),.set(set),.clr(clr),.q(q));

	initial
	begin
		$dumpfile("tb_dlatchsr");
		$dumpvars(0,tb_dlatchsr);
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		clr = 1;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		clr = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		set = 1;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		set = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		d = 1;
		#10
		d = 0;
		#10
		$finish;
	end
endmodule
