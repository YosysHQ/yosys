module gold (input clock, ctrl, din, output reg dout);
	always @(posedge clock) begin
		if (1'b1) begin
			if (1'b0) begin end else begin
				dout <= 0;
			end
			if (ctrl)
				dout <= din;
		end
	end
endmodule

module gate (input clock, ctrl, din, output reg dout);
	always @(posedge clock) begin
		if (1'b1) begin
			if (1'b0) begin end else begin
				dout <= 0;
			end
		end
		if (ctrl)
			dout <= din;
	end
endmodule
