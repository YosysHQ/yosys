module DFF(input D, CLK, nRSTZ, nSETZ, output reg Q);
	always @(posedge CLK, negedge nRSTZ, negedge nSETZ) begin
		if (!nRSTZ)
			Q <= 1'b0;
		else if (!nSETZ)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule

module LUT2(input IN0, IN1, output OUT);
	parameter [3:0] INIT = 0;
	assign OUT = INIT[{IN1, IN0}];
endmodule

module LUT3(input IN0, IN1, IN2, output OUT);
	parameter [7:0] INIT = 0;
	assign OUT = INIT[{IN2, IN1, IN0}];
endmodule

module LUT4(input IN0, IN1, IN2, IN3, output OUT);
	parameter [15:0] INIT = 0;
	assign OUT = INIT[{IN3, IN2, IN1, IN0}];
endmodule
