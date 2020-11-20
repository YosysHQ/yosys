module top;
	parameter STR = "something interesting";
	initial begin
		$display("A: %s", STR);
		$display("B: %0s", STR);
	end
endmodule
