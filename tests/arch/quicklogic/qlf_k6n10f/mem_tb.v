module TB(input clk);

parameter ADDRESS_WIDTH = 10;
parameter ADDRESS_WIDTH_A = ADDRESS_WIDTH;
parameter ADDRESS_WIDTH_B = ADDRESS_WIDTH;
parameter DATA_WIDTH = 36;
parameter DATA_WIDTH_A = DATA_WIDTH;
parameter DATA_WIDTH_B = DATA_WIDTH;
parameter VECTORLEN = 16;
parameter SHIFT_VAL = 0;

// intentionally keep expected values at full width precision to allow testing
// of truncation
localparam MAX_WIDTH = 36;

reg rce_a_testvector [VECTORLEN-1:0];
reg [ADDRESS_WIDTH_A-1:0] ra_a_testvector [VECTORLEN-1:0];
reg [MAX_WIDTH-1:0] rq_a_expected [VECTORLEN-1:0];

reg wce_a_testvector [VECTORLEN-1:0];
reg [ADDRESS_WIDTH_A-1:0] wa_a_testvector [VECTORLEN-1:0];
reg [DATA_WIDTH_A-1:0] wd_a_testvector [VECTORLEN-1:0];

reg rce_b_testvector [VECTORLEN-1:0];
reg [ADDRESS_WIDTH_B-1:0] ra_b_testvector [VECTORLEN-1:0];
reg [MAX_WIDTH-1:0] rq_b_expected [VECTORLEN-1:0];

reg wce_b_testvector [VECTORLEN-1:0];
reg [ADDRESS_WIDTH_B-1:0] wa_b_testvector [VECTORLEN-1:0];
reg [DATA_WIDTH_B-1:0] wd_b_testvector [VECTORLEN-1:0];

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

	`MEM_TEST_VECTOR
	
end


wire rce_a = rce_a_testvector[i];
wire [ADDRESS_WIDTH_A-1:0] ra_a = ra_a_testvector[i];
wire [MAX_WIDTH-1:0] rq_a_e = rq_a_expected[i];
wire [DATA_WIDTH_A-1:0] rq_a;

wire wce_a = wce_a_testvector[i];
wire [ADDRESS_WIDTH_A-1:0] wa_a = wa_a_testvector[i];
wire [DATA_WIDTH_A-1:0] wd_a = wd_a_testvector[i];

wire rce_b = rce_b_testvector[i];
wire [ADDRESS_WIDTH_B-1:0] ra_b = ra_b_testvector[i];
wire [MAX_WIDTH-1:0] rq_b_e = rq_b_expected[i];
wire [DATA_WIDTH_B-1:0] rq_b;

wire wce_b = wce_b_testvector[i];
wire [ADDRESS_WIDTH_B-1:0] wa_b = wa_b_testvector[i];
wire [DATA_WIDTH_B-1:0] wd_b = wd_b_testvector[i];

`UUT_SUBMODULE

always @(posedge clk) begin
	if (i < VECTORLEN-1) begin
		if (i > 0) begin
			if($past(rce_a)) 
				assert(rq_a == rq_a_e);
			if($past(rce_b))
				assert(rq_b == rq_b_e);
		end
		i <= i + 1;
	end
end
endmodule
