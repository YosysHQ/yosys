
module \$mem (RD_CLK, RD_EN, RD_ADDR, RD_DATA, WR_CLK, WR_EN, WR_ADDR, WR_DATA);
	parameter MEMID = "";
	parameter SIZE = 256;
	parameter OFFSET = 0;
	parameter ABITS = 8;
	parameter WIDTH = 8;
	parameter signed INIT = 1'bx;

	parameter RD_PORTS = 1;
	parameter RD_CLK_ENABLE = 1'b1;
	parameter RD_CLK_POLARITY = 1'b1;
	parameter RD_TRANSPARENT = 1'b1;

	parameter WR_PORTS = 1;
	parameter WR_CLK_ENABLE = 1'b1;
	parameter WR_CLK_POLARITY = 1'b1;

	input [RD_PORTS-1:0] RD_CLK;
	input [RD_PORTS-1:0] RD_EN;
	input [RD_PORTS*ABITS-1:0] RD_ADDR;
	output reg [RD_PORTS*WIDTH-1:0] RD_DATA;

	input [WR_PORTS-1:0] WR_CLK;
	input [WR_PORTS*WIDTH-1:0] WR_EN;
	input [WR_PORTS*ABITS-1:0] WR_ADDR;
	input [WR_PORTS*WIDTH-1:0] WR_DATA;

	wire [1023:0] _TECHMAP_DO_ = "proc; clean";

	parameter _TECHMAP_CONNMAP_RD_CLK_ = 0;
	parameter _TECHMAP_CONNMAP_WR_CLK_ = 0;

	parameter _TECHMAP_CONSTVAL_RD_EN_ = 0;

	parameter _TECHMAP_BITS_CONNMAP_ = 0;
	parameter _TECHMAP_CONNMAP_WR_EN_ = 0;

	reg _TECHMAP_FAIL_;
	integer k;
	initial begin
		_TECHMAP_FAIL_ <= 0;

		// no initialized memories
		if (INIT !== 1'bx)
			_TECHMAP_FAIL_ <= 1;

		// only map cells with only one read and one write port
		if (RD_PORTS > 1 || WR_PORTS > 1)
			_TECHMAP_FAIL_ <= 1;

		// read enable must be constant high
		if (_TECHMAP_CONSTVAL_RD_EN_[0] !== 1'b1)
			_TECHMAP_FAIL_ <= 1;

		// we expect positive read clock and non-transparent reads
		if (RD_TRANSPARENT || !RD_CLK_ENABLE || !RD_CLK_POLARITY)
			_TECHMAP_FAIL_ <= 1;

		// we expect positive write clock
		if (!WR_CLK_ENABLE || !WR_CLK_POLARITY)
			_TECHMAP_FAIL_ <= 1;

		// only one global write enable bit is supported
		for (k = 1; k < WR_PORTS*WIDTH; k = k+1)
			if (_TECHMAP_CONNMAP_WR_EN_[0 +: _TECHMAP_BITS_CONNMAP_] !=
					_TECHMAP_CONNMAP_WR_EN_[k*_TECHMAP_BITS_CONNMAP_ +: _TECHMAP_BITS_CONNMAP_])
				_TECHMAP_FAIL_ <= 1;

		// read and write must be in same clock domain
		if (_TECHMAP_CONNMAP_RD_CLK_ != _TECHMAP_CONNMAP_WR_CLK_)
			_TECHMAP_FAIL_ <= 1;

		// we don't do small memories or memories with offsets
		if (OFFSET != 0 || ABITS < 4 || SIZE < 16)
			_TECHMAP_FAIL_ <= 1;
	end

	genvar i;
	generate
	  for (i = 0; i < WIDTH; i=i+1) begin:slice
		\$__mem_4x1_generator #(
			.ABITS(ABITS),
			.SIZE(SIZE)
		) bit_slice (
			.CLK(RD_CLK),
			.RD_ADDR(RD_ADDR),
			.RD_DATA(RD_DATA[i]),
			.WR_ADDR(WR_ADDR),
			.WR_DATA(WR_DATA[i]),
			.WR_EN(WR_EN[0])
		);
	  end
	endgenerate
endmodule

module \$__mem_4x1_generator (CLK, RD_ADDR, RD_DATA, WR_ADDR, WR_DATA, WR_EN);
	parameter ABITS = 4;
	parameter SIZE = 16;

	input CLK, WR_DATA, WR_EN;
	input [ABITS-1:0] RD_ADDR, WR_ADDR;
	output RD_DATA;

	wire [1023:0] _TECHMAP_DO_ = "proc; clean";

	generate
	  if (ABITS > 4) begin
	  	wire high_rd_data, low_rd_data;
	  	if (SIZE > 2**(ABITS-1)) begin
			\$__mem_4x1_generator #(
				.ABITS(ABITS-1),
				.SIZE(SIZE - 2**(ABITS-1))
			) part_high (
				.CLK(CLK),
				.RD_ADDR(RD_ADDR[ABITS-2:0]),
				.RD_DATA(high_rd_data),
				.WR_ADDR(WR_ADDR[ABITS-2:0]),
				.WR_DATA(WR_DATA),
				.WR_EN(WR_EN && WR_ADDR[ABITS-1])
			);
		end else begin
			assign high_rd_data = 1'bx;
		end
		\$__mem_4x1_generator #(
			.ABITS(ABITS-1),
			.SIZE(SIZE > 2**(ABITS-1) ? 2**(ABITS-1) : SIZE)
		) part_low (
			.CLK(CLK),
			.RD_ADDR(RD_ADDR[ABITS-2:0]),
			.RD_DATA(low_rd_data),
			.WR_ADDR(WR_ADDR[ABITS-2:0]),
			.WR_DATA(WR_DATA),
			.WR_EN(WR_EN && !WR_ADDR[ABITS-1])
		);
		reg delayed_abit;
		always @(posedge CLK)
			delayed_abit <= RD_ADDR[ABITS-1];
		assign RD_DATA = delayed_abit ? high_rd_data : low_rd_data;
	  end else begin
	  	MEM4X1 _TECHMAP_REPLACE_ (
			.CLK(CLK),
			.RD_ADDR(RD_ADDR),
			.RD_DATA(RD_DATA),
			.WR_ADDR(WR_ADDR),
			.WR_DATA(WR_DATA),
			.WR_EN(WR_EN)
		);
	  end
	endgenerate
endmodule

