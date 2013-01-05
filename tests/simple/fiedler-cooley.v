// borrowed with some modifications from
// http://www.ee.ed.ac.uk/~gerard/Teach/Verilog/manual/Example/lrgeEx2/cooley.html
module up3down5(clock, data_in, up, down, carry_out, borrow_out, count_out, parity_out);

input [8:0] data_in;
input clock, up, down;

output reg [8:0] count_out;
output reg carry_out, borrow_out, parity_out;

reg [9:0] cnt_up, cnt_dn;
reg [8:0] count_nxt;

always @(posedge clock)
begin
	cnt_dn = count_out - 3'b 101;
	cnt_up = count_out + 2'b 11;

	case ({up,down})
		2'b 00 : count_nxt = data_in;
		2'b 01 : count_nxt = cnt_dn;
		2'b 10 : count_nxt = cnt_up;
		2'b 11 : count_nxt = count_out;
		default : count_nxt = 9'bX;
	endcase

	parity_out  <= ^count_nxt;
	carry_out   <= up & cnt_up[9];
	borrow_out  <= down & cnt_dn[9];
	count_out   <= count_nxt;
end

endmodule
