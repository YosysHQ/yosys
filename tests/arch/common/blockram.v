`default_nettype none
module sync_ram_sp #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
   (input  wire                      write_enable, clk,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in,
    output wire  [DATA_WIDTH-1:0]    data_out);

  localparam WORD  = (DATA_WIDTH-1);
  localparam DEPTH = (2**ADDRESS_WIDTH-1);

  reg [WORD:0] data_out_r;
  reg [WORD:0] memory [0:DEPTH];

  always @(posedge clk) begin
    if (write_enable)
      memory[address_in] <= data_in;
    data_out_r <= memory[address_in];
  end

  assign data_out = data_out_r;

endmodule // sync_ram_sp


module sync_ram_sdp #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
   (input  wire                      clk, write_enable,
    input  wire  [DATA_WIDTH-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-1:0] address_in_r, address_in_w,
    output wire  [DATA_WIDTH-1:0]    data_out);

  localparam WORD  = (DATA_WIDTH-1);
  localparam DEPTH = (2**ADDRESS_WIDTH-1);

  reg [WORD:0] data_out_r;
  reg [WORD:0] memory [0:DEPTH];

  always @(posedge clk) begin
    if (write_enable)
      memory[address_in_w] <= data_in;
    data_out_r <= memory[address_in_r];
  end

  assign data_out = data_out_r;

endmodule // sync_ram_sdp


module sync_ram_sdp_wwr #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10, SHIFT_VAL=1) // wd=16, wa=9
(
		input  wire                          clk_w, clk_r, write_enable,
    		input  wire  [WORD-1:0]              data_in,
    		input  wire  [ADDRESS_WIDTH_W-1:0]   address_in_w,
    		input  wire  [ADDRESS_WIDTH-1:0]     address_in_r,
    		output wire  [DATA_WIDTH-1:0]        data_out
);

	localparam ADDRESS_WIDTH_W = ADDRESS_WIDTH-SHIFT_VAL;
	localparam BYTE = DATA_WIDTH;
	localparam WORD  = DATA_WIDTH<<SHIFT_VAL;
	localparam DEPTH = 2**ADDRESS_WIDTH_W;
	localparam SUB_DEPTH = 2**SHIFT_VAL;

	reg [BYTE-1:0] data_out_r;
	reg [BYTE-1:0] memory [0:DEPTH-1];

	integer i;
	always @(posedge clk_w) begin
		for (i=0; i<SUB_DEPTH; i=i+1)
			if (write_enable)
				memory[{address_in_w, i}] <= data_in[i*BYTE+:BYTE];
	end

	always @(posedge clk_r) begin
		data_out_r <= memory[address_in_r];
	end

	assign data_out = data_out_r;

endmodule // sync_ram_sdp_wwr


module sync_ram_sdp_wrr #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10, SHIFT_VAL=1) // rd=16, ra=9
(
		input  wire                         clk_w, clk_r, write_enable,
		input  wire  [DATA_WIDTH-1:0]       data_in,
		input  wire  [ADDRESS_WIDTH-1:0]    address_in_w,
		input  wire  [ADDRESS_WIDTH_R-1:0]  address_in_r,
		output wire  [WORD-1:0]             data_out
);
	localparam ADDRESS_WIDTH_R = ADDRESS_WIDTH-SHIFT_VAL;
	localparam BYTE = DATA_WIDTH;
	localparam WORD  = BYTE<<SHIFT_VAL;
	localparam DEPTH = 2**ADDRESS_WIDTH;
	localparam SUB_DEPTH = 2**SHIFT_VAL;

	reg [WORD-1:0] data_out_r;
	reg [BYTE-1:0] memory [0:DEPTH-1];

	always @(posedge clk_w) begin
		if (write_enable)
			memory[address_in_w] <= data_in;
	end

	integer i;
	always @(posedge clk_r) begin
		for (i=0; i<SUB_DEPTH; i=i+1)
			data_out_r[i*BYTE+:BYTE] <= memory[{address_in_r, i}];
	end

	assign data_out = data_out_r;

endmodule // sync_ram_sdp_wrr


module double_sync_ram_sdp #(parameter DATA_WIDTH_A=8, ADDRESS_WIDTH_A=10, DATA_WIDTH_B=8, ADDRESS_WIDTH_B=10)
(
    input  wire                        write_enable_a, clk_a,
    input  wire  [DATA_WIDTH_A-1:0]    data_in_a,
    input  wire  [ADDRESS_WIDTH_A-1:0] address_in_r_a, address_in_w_a,
    output wire  [DATA_WIDTH_A-1:0]    data_out_a,

    input  wire                        write_enable_b, clk_b,
    input  wire  [DATA_WIDTH_B-1:0]    data_in_b,
    input  wire  [ADDRESS_WIDTH_B-1:0] address_in_r_b, address_in_w_b,
    output wire  [DATA_WIDTH_B-1:0]    data_out_b
);

    sync_ram_sdp #(
        .DATA_WIDTH(DATA_WIDTH_A),
        .ADDRESS_WIDTH(ADDRESS_WIDTH_A)
    ) a_ram (
    .write_enable(write_enable_a),
    .clk(clk_a),
    .data_in(data_in_a),
    .address_in_r(address_in_r_a),
    .address_in_w(address_in_w_a),
    .data_out(data_out_a)
    );

    sync_ram_sdp #(
        .DATA_WIDTH(DATA_WIDTH_B),
        .ADDRESS_WIDTH(ADDRESS_WIDTH_B)
    ) b_ram (
    .write_enable(write_enable_b),
    .clk(clk_b),
    .data_in(data_in_b),
    .address_in_r(address_in_r_b),
    .address_in_w(address_in_w_b),
    .data_out(data_out_b)
    );

endmodule // double_sync_ram_sdp


module sync_ram_tdp #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
   (input  wire                      clk_a, clk_b, 
    input  wire                      write_enable_a, write_enable_b,
    input  wire                      read_enable_a, read_enable_b,
    input  wire  [DATA_WIDTH-1:0]    write_data_a, write_data_b,
    input  wire  [ADDRESS_WIDTH-1:0] addr_a, addr_b,
    output reg   [DATA_WIDTH-1:0]    read_data_a, read_data_b);

  localparam WORD  = (DATA_WIDTH-1);
  localparam DEPTH = (2**ADDRESS_WIDTH-1);

  reg [WORD:0] mem [0:DEPTH];

  always @(posedge clk_a) begin
    if (write_enable_a)
      mem[addr_a] <= write_data_a;
    else
      read_data_a <= mem[addr_a];
  end

  always @(posedge clk_b) begin
    if (write_enable_b)
      mem[addr_b] <= write_data_b;
    else
      read_data_b <= mem[addr_b];
  end

endmodule // sync_ram_tdp

module double_sync_ram_tdp #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
(
    input  wire                         clk_a_0,
    input  wire                         write_enable_a_0, read_enable_a_0,
    input  wire  [DATA_WIDTH-1:0]       write_data_a_0,
    input  wire  [ADDRESS_WIDTH-1:0]    addr_a_0,
    output wire  [DATA_WIDTH-1:0]       read_data_a_0,

    input  wire                         clk_a_1,
    input  wire                         write_enable_a_1, read_enable_a_1,
    input  wire  [DATA_WIDTH-1:0]       write_data_a_1,
    input  wire  [ADDRESS_WIDTH-1:0]    addr_a_1,
    output wire  [DATA_WIDTH-1:0]       read_data_a_1,

    input  wire                         clk_b_0,
    input  wire                         write_enable_b_0, read_enable_b_0,
    input  wire  [DATA_WIDTH-1:0]       write_data_b_0,
    input  wire  [ADDRESS_WIDTH-1:0]    addr_b_0,
    output wire  [DATA_WIDTH-1:0]       read_data_b_0,

    input  wire                         clk_b_1,
    input  wire                         write_enable_b_1, read_enable_b_1,
    input  wire  [DATA_WIDTH-1:0]       write_data_b_1,
    input  wire  [ADDRESS_WIDTH-1:0]    addr_b_1,
    output wire  [DATA_WIDTH-1:0]       read_data_b_1
);

    sync_ram_tdp #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDRESS_WIDTH(ADDRESS_WIDTH)
    ) ram_0 (
        .clk_a(clk_a_0),
        .clk_b(clk_b_0),
        .write_enable_a(write_enable_a_0),
        .write_enable_b(write_enable_b_0),
        .read_enable_a(read_enable_a_0),
        .read_enable_b(read_enable_b_0),
        .write_data_a(write_data_a_0),
        .write_data_b(write_data_b_0),
        .addr_a(addr_a_0),
        .addr_b(addr_b_0),
        .read_data_a(read_data_a_0),
        .read_data_b(read_data_b_0)
    );

    sync_ram_tdp #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDRESS_WIDTH(ADDRESS_WIDTH)
    ) ram_1 (
        .clk_a(clk_a_1),
        .clk_b(clk_b_1),
        .write_enable_a(write_enable_a_1),
        .write_enable_b(write_enable_b_1),
        .read_enable_a(read_enable_a_1),
        .read_enable_b(read_enable_b_1),
        .write_data_a(write_data_a_1),
        .write_data_b(write_data_b_1),
        .addr_a(addr_a_1),
        .addr_b(addr_b_1),
        .read_data_a(read_data_a_1),
        .read_data_b(read_data_b_1)
    );

endmodule // double_sync_ram_tdp

