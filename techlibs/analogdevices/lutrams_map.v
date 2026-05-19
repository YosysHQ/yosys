module $__ANALOGDEVICES_LUTRAM_ (...);

parameter INIT = 0;
parameter OPTION_SIZE = 32;
parameter OPTION_MODE = "SP";
parameter ABITS = 5;
parameter WIDTH = 1;

output PORT_RW_RD_DATA;
input PORT_RW_WR_DATA;
input [ABITS-1:0] PORT_RW_ADDR;
input PORT_RW_WR_EN;
input PORT_RW_CLK;

output PORT_R_RD_DATA;
input [ABITS-1:0] PORT_R_ADDR;

generate
	if (OPTION_MODE=="SP")
	case(OPTION_SIZE)
	32:
		RAMS32X1
		#(
			.INIT(INIT)
		)
		_TECHMAP_REPLACE_
		(
			.O(PORT_RW_RD_DATA),
			.A0(PORT_RW_ADDR[0]),
			.A1(PORT_RW_ADDR[1]),
			.A2(PORT_RW_ADDR[2]),
			.A3(PORT_RW_ADDR[3]),
			.A4(PORT_RW_ADDR[4]),
			.D(PORT_RW_WR_DATA),
			.WCLK(PORT_RW_CLK),
			.WE(PORT_RW_WR_EN)
		);
	64:
		RAMS64X1
		#(
			.INIT(INIT)
		)
		_TECHMAP_REPLACE_
		(
			.O(PORT_RW_RD_DATA),
			.A0(PORT_RW_ADDR[0]),
			.A1(PORT_RW_ADDR[1]),
			.A2(PORT_RW_ADDR[2]),
			.A3(PORT_RW_ADDR[3]),
			.A4(PORT_RW_ADDR[4]),
			.A5(PORT_RW_ADDR[5]),
			.D(PORT_RW_WR_DATA),
			.WCLK(PORT_RW_CLK),
			.WE(PORT_RW_WR_EN)
		);
	default:
		$error("invalid SIZE/MODE combination");
	endcase
	else if (OPTION_MODE=="DP")
	case (OPTION_SIZE)
	32:
		RAMD32X1
		#(
			.INIT(INIT)
		)
		_TECHMAP_REPLACE_
		(
			.DPO(PORT_R_RD_DATA),
			.SPO(PORT_RW_RD_DATA),
			.A0(PORT_RW_ADDR[0]),
			.A1(PORT_RW_ADDR[1]),
			.A2(PORT_RW_ADDR[2]),
			.A3(PORT_RW_ADDR[3]),
			.A4(PORT_RW_ADDR[4]),
			.D(PORT_RW_WR_DATA),
			.DPRA0(PORT_R_ADDR[0]),
			.DPRA1(PORT_R_ADDR[1]),
			.DPRA2(PORT_R_ADDR[2]),
			.DPRA3(PORT_R_ADDR[3]),
			.DPRA4(PORT_R_ADDR[4]),
			.WCLK(PORT_RW_CLK),
			.WE(PORT_RW_WR_EN)
		);
	64:
		RAMD64X1
		#(
			.INIT(INIT)
		)
		_TECHMAP_REPLACE_
		(
			.DPO(PORT_R_RD_DATA),
			.SPO(PORT_RW_RD_DATA),
			.A0(PORT_RW_ADDR[0]),
			.A1(PORT_RW_ADDR[1]),
			.A2(PORT_RW_ADDR[2]),
			.A3(PORT_RW_ADDR[3]),
			.A4(PORT_RW_ADDR[4]),
			.A5(PORT_RW_ADDR[5]),
			.D(PORT_RW_WR_DATA),
			.DPRA0(PORT_R_ADDR[0]),
			.DPRA1(PORT_R_ADDR[1]),
			.DPRA2(PORT_R_ADDR[2]),
			.DPRA3(PORT_R_ADDR[3]),
			.DPRA4(PORT_R_ADDR[4]),
			.DPRA5(PORT_R_ADDR[5]),
			.WCLK(PORT_RW_CLK),
			.WE(PORT_RW_WR_EN)
		);
	default:
		$error("invalid SIZE/MODE combination");
	endcase
	else
		wire _TECHMAP_FAIL_ = 1;
endgenerate

endmodule


module $__ANALOGDEVICES_LUTRAM_DP_ (...);

parameter INIT = 0;
parameter OPTION_SIZE = 32;
parameter ABITS = 5;
parameter WIDTH = 1;

output PORT_RW_RD_DATA;
input PORT_RW_WR_DATA;
input [ABITS-1:0] PORT_RW_ADDR;
input PORT_RW_WR_EN;
input PORT_RW_CLK;

output PORT_R_RD_DATA;
input [ABITS-1:0] PORT_R_ADDR;

generate

endgenerate

endmodule
