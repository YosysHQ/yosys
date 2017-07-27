module top (input logic clk, input logic selA, selB, QA, QB, output logic Q);
	always @(posedge clk) begin
		if (selA) Q <= QA;
		if (selB) Q <= QB;
	end

	check_selA: assert property ( @(posedge clk) selA |=> Q == $past(QA) );
	check_selB: assert property ( @(posedge clk) selB |=> Q == $past(QB) );
`ifndef FAIL
	assume_not_11: assume property ( @(posedge clk) !(selA & selB) );
`endif
endmodule
