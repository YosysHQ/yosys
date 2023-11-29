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


module sync_ram_sdp_wwr #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10) // wd=16, wa=9
   (input  wire                          clk, write_enable,
    input  wire  [(DATA_WIDTH*2)-1:0]    data_in,
    input  wire  [ADDRESS_WIDTH-2:0]     address_in_w,
    input  wire  [ADDRESS_WIDTH-1:0]     address_in_r,
    output wire  [DATA_WIDTH-1:0]        data_out);

  localparam WORD  = ((DATA_WIDTH*2)-1);
  localparam DEPTH = (2**(ADDRESS_WIDTH-1)-1);

  reg [WORD:0] data_out_r;
  reg [WORD:0] memory [0:DEPTH];

  always @(posedge clk) begin
    if (write_enable) begin
      memory[address_in_w] <= data_in;
    end
    data_out_r <= memory[address_in_r>>1];
  end

  assign data_out = address_in_r[0] ? data_out_r[WORD:DATA_WIDTH] : data_out_r[DATA_WIDTH-1:0];

endmodule // sync_ram_sdp_wwr


module sync_ram_sdp_wrr #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10) // rd=16, ra=9
   (input  wire                         clk, write_enable,
    input  wire  [DATA_WIDTH-1:0]       data_in,
    input  wire  [ADDRESS_WIDTH-1:0]    address_in_w,
    input  wire  [ADDRESS_WIDTH-2:0]    address_in_r,
    output wire  [(DATA_WIDTH*1)-1:0]   data_out);

  localparam WORD  = (DATA_WIDTH-1);
  localparam DEPTH = (2**ADDRESS_WIDTH-1);

  reg [WORD:0] data_out_r0;
  reg [WORD:0] data_out_r1;
  reg [WORD:0] memory [0:DEPTH];

  always @(posedge clk) begin
    if (write_enable)
      memory[address_in_w] <= data_in;
    data_out_r0 <= memory[address_in_r<<1+0];
    data_out_r1 <= memory[address_in_r<<1+1];
  end

  assign data_out = {data_out_r0, data_out_r1};

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

