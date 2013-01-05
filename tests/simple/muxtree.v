
// test case generated from IWLS 2005 usb_phy core
// (triggered a bug in opt_muxtree pass)

module usb_tx_phy(clk, rst, DataOut_i, TxValid_i, hold_reg);

input		clk;
input		rst;
input		DataOut_i;
input		TxValid_i;
output reg	hold_reg;

reg		state, next_state;
reg		ld_sop_d;
reg		ld_data_d;

always @(posedge clk)
	if(ld_sop_d)
		hold_reg <= 0;
	else
		hold_reg <= DataOut_i;

always @(posedge clk)
	if(!rst)	state <= 0;
	else		state <= next_state;

always @(state or TxValid_i)
   begin
	next_state = state;

	ld_sop_d = 1'b0;
	ld_data_d = 1'b0;

	case(state)	// synopsys full_case parallel_case
	   0:
			if(TxValid_i)
			   begin
				ld_sop_d = 1'b1;
				next_state = 1;
			   end
	   1:
			if(TxValid_i)
			   begin
				ld_data_d = 1'b1;
				next_state = 0;
			   end
	endcase
   end

endmodule
