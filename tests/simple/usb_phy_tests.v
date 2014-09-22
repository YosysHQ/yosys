
// from usb_rx_phy
module usb_phy_test01(clk, rst, rx_en, fs_ce);

input		clk, rst;
input		rx_en;
output reg	fs_ce;
reg	[1:0]	dpll_next_state;
reg	[1:0]	dpll_state;

always @(posedge clk)
	dpll_state <= rst ? 0 : dpll_next_state;

always @*
   begin
	fs_ce = 1'b0;
	case(dpll_state)
	   2'h0:
		if(rx_en)	dpll_next_state = 2'h0;
		else		dpll_next_state = 2'h1;
	   2'h1:begin
		fs_ce = 1'b1;
		if(rx_en)	dpll_next_state = 2'h3;
		else		dpll_next_state = 2'h2;
		end
	   2'h2:
		if(rx_en)	dpll_next_state = 2'h0;
		else		dpll_next_state = 2'h3;
	   2'h3:
		if(rx_en)	dpll_next_state = 2'h0;
		else		dpll_next_state = 2'h0;
	endcase
   end

endmodule

