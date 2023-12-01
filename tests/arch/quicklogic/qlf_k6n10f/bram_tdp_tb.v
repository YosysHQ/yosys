module TB(input clk);

localparam ADDR_WIDTH = 10;
localparam DATA_WIDTH = 36;
localparam VECTORLEN = 16;

reg rce_a_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] ra_a_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] rq_a_expected [VECTORLEN-1:0];

reg wce_a_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] wa_a_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] wd_a_testvector [VECTORLEN-1:0];

reg rce_b_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] ra_b_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] rq_b_expected [VECTORLEN-1:0];

reg wce_b_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] wa_b_testvector [VECTORLEN-1:0];
reg [ADDR_WIDTH-1:0] wd_b_testvector [VECTORLEN-1:0];

reg [$clog2(VECTORLEN)-1:0] i = 0;

integer j;
initial begin
	for (j = 0; j < VECTORLEN; j = j + 1) begin
		rce_a_testvector[j] = 1'b0;
		ra_a_testvector[j] = 10'h0;
		wce_a_testvector[j] = 1'b0;
		wa_a_testvector[j] = 10'h0;
		rce_b_testvector[j] = 1'b0;
		ra_b_testvector[j] = 10'h0;
		wce_b_testvector[j] = 1'b0;
		wa_b_testvector[j] = 10'h0;

	end

	wce_a_testvector[0] = 1'b1;
	wa_a_testvector[0] = 10'hA;
	wd_a_testvector[0] = 36'hDEADBEEF;

	rce_b_testvector[2] = 1'b1;
	ra_b_testvector[2] = 10'hA;
	rq_b_expected[3] = 36'hDEADBEEF;
	
end


wire rce_a = rce_a_testvector[i];
wire [ADDR_WIDTH-1:0] ra_a = ra_a_testvector[i];
wire [DATA_WIDTH-1:0] rq_a;

wire wce_a = wce_a_testvector[i];
wire [ADDR_WIDTH-1:0] wa_a = wa_a_testvector[i];
wire [DATA_WIDTH-1:0] wd_a = wd_a_testvector[i];

wire rce_b = rce_b_testvector[i];
wire [ADDR_WIDTH-1:0] ra_b = ra_b_testvector[i];
wire [DATA_WIDTH-1:0] rq_b;

wire wce_b = wce_b_testvector[i];
wire [ADDR_WIDTH-1:0] wa_b = wa_b_testvector[i];
wire [DATA_WIDTH-1:0] wd_b = wd_b_testvector[i];

BRAM_TDP #(
	.AWIDTH(ADDR_WIDTH),
	.DWIDTH(DATA_WIDTH)
) uut (
	.clk_a(clk),
	.rce_a(rce_a),
	.ra_a(ra_a),
	.rq_a(rq_a),
	.wce_a(wce_a),
	.wa_a(wa_a),
	.wd_a(wd_a),

	.clk_b(clk),
	.rce_b(rce_b),
	.ra_b(ra_b),
	.rq_b(rq_b),
	.wce_b(wce_b),
	.wa_b(wa_b),
	.wd_b(wd_b)
);


always @(posedge clk) begin
	if (i < VECTORLEN-1) begin
		if (i > 0) begin
			if($past(rce_a)) 
				assert(rq_a == rq_a_expected[i]);
			if($past(rce_b))
				assert(rq_b == rq_b_expected[i]);
		end
		i <= i + 1;
	end
end
endmodule