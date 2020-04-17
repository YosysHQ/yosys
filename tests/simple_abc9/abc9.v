module abc9_test001(input a, output o);
assign o = a;
endmodule

module abc9_test002(input [1:0] a, output o);
assign o = a[1];
endmodule

module abc9_test003(input [1:0] a, output [1:0] o);
assign o = a;
endmodule

module abc9_test004(input [1:0] a, output o);
assign o = ^a;
endmodule

module abc9_test005(input [1:0] a, output o, output p);
assign o = ^a;
assign p = ~o;
endmodule

module abc9_test006(input [1:0] a, output [2:0] o);
assign o[0] = ^a;
assign o[1] = ~o[0];
assign o[2] = o[1];
endmodule

module abc9_test007(input a, output o);
wire b, c;
assign c = ~a;
assign b = c;
abc9_test007_sub s(b, o);
endmodule

module abc9_test007_sub(input a, output b);
assign b = a;
endmodule

module abc9_test008(input a, output o);
wire b, c;
assign b = ~a;
assign c = b;
abc9_test008_sub s(b, o);
endmodule

module abc9_test008_sub(input a, output b);
assign b = ~a;
endmodule

module abc9_test009(inout io, input oe);
reg latch;
always @(io or oe)
    if (!oe)
        latch <= io;
assign io = oe ? ~latch : 1'bz;
endmodule

module abc9_test010(inout [7:0] io, input oe);
reg [7:0] latch;
always @(io or oe)
    if (!oe)
        latch <= io;
assign io = oe ? ~latch : 8'bz;
endmodule

module abc9_test011(inout io, input oe);
reg latch;
always @(io or oe)
    if (!oe)
        latch <= io;
//assign io = oe ? ~latch : 8'bz;
endmodule

module abc9_test012(inout io, input oe);
reg latch;
//always @(io or oe)
//    if (!oe)
//        latch <= io;
assign io = oe ? ~latch : 8'bz;
endmodule

module abc9_test013(inout [3:0] io, input oe);
reg [3:0] latch;
always @(io or oe)
    if (!oe)
        latch[3:0] <= io[3:0];
    else
        latch[7:4] <= io;
assign io[3:0] = oe ? ~latch[3:0] : 4'bz;
assign io[7:4] = !oe ? {latch[4], latch[7:3]} : 4'bz;
endmodule

module abc9_test014(inout [7:0] io, input oe);
abc9_test012_sub sub(io, oe);
endmodule

module abc9_test012_sub(inout [7:0] io, input oe);
reg [7:0] latch;
always @(io or oe)
    if (!oe)
        latch[3:0] <= io;
    else
        latch[7:4] <= io;
assign io[3:0] = oe ? ~latch[3:0] : 4'bz;
assign io[7:4] = !oe ? {latch[4], latch[7:3]} : 4'bz;
endmodule

module abc9_test015(input a, output b, input c);
assign b = ~a;
(* keep *) wire d;
assign d = ~c;
endmodule

module abc9_test016(input a, output b);
assign b = ~a;
(* keep *) reg c;
always @* c <= ~a;
endmodule

module abc9_test017(input a, output b);
assign b = ~a;
(* keep *) reg c;
always @* c = b;
endmodule

module abc9_test018(input a, output b, output c);
assign b = ~a;
(* keep *) wire [1:0] d;
assign c = &d;
endmodule

module abc9_test019(input a, output b);
assign b = ~a;
(* keep *) reg [1:0] c;
reg d;
always @* d <= &c;
endmodule

module abc9_test020(input a, output b);
assign b = ~a;
(* keep *) reg [1:0] c;
(* keep *) reg d;
always @* d <= &c;
endmodule

// Citation: https://github.com/alexforencich/verilog-ethernet
module abc9_test021(clk, rst, s_eth_hdr_valid, s_eth_hdr_ready, s_eth_dest_mac, s_eth_src_mac, s_eth_type, s_eth_payload_axis_tdata, s_eth_payload_axis_tkeep, s_eth_payload_axis_tvalid, s_eth_payload_axis_tready, s_eth_payload_axis_tlast, s_eth_payload_axis_tid, s_eth_payload_axis_tdest, s_eth_payload_axis_tuser, m_eth_hdr_valid, m_eth_hdr_ready, m_eth_dest_mac, m_eth_src_mac, m_eth_type, m_eth_payload_axis_tdata, m_eth_payload_axis_tkeep, m_eth_payload_axis_tvalid, m_eth_payload_axis_tready, m_eth_payload_axis_tlast, m_eth_payload_axis_tid, m_eth_payload_axis_tdest, m_eth_payload_axis_tuser);
  input clk;
  output [47:0] m_eth_dest_mac;
  input m_eth_hdr_ready;
  output m_eth_hdr_valid;
  output [7:0] m_eth_payload_axis_tdata;
  output [7:0] m_eth_payload_axis_tdest;
  output [7:0] m_eth_payload_axis_tid;
  output m_eth_payload_axis_tkeep;
  output m_eth_payload_axis_tlast;
  input m_eth_payload_axis_tready;
  output m_eth_payload_axis_tuser;
  output m_eth_payload_axis_tvalid;
  output [47:0] m_eth_src_mac;
  output [15:0] m_eth_type;
  input rst;
  input [191:0] s_eth_dest_mac;
  output [3:0] s_eth_hdr_ready;
  input [3:0] s_eth_hdr_valid;
  input [31:0] s_eth_payload_axis_tdata;
  input [31:0] s_eth_payload_axis_tdest;
  input [31:0] s_eth_payload_axis_tid;
  input [3:0] s_eth_payload_axis_tkeep;
  input [3:0] s_eth_payload_axis_tlast;
  output [3:0] s_eth_payload_axis_tready;
  input [3:0] s_eth_payload_axis_tuser;
  input [3:0] s_eth_payload_axis_tvalid;
  input [191:0] s_eth_src_mac;
  input [63:0] s_eth_type;
  (* keep *)
  wire [0:0] grant, request;
  wire a;
  not u0 (
    a,
    grant[0]
  );
  and u1  (
    request[0],
    s_eth_hdr_valid[0],
    a
  );
  (* keep *)
  MUXF8 u2  (
    .I0(1'bx),
    .I1(1'bx),
    .O(o),
    .S(1'bx)
  );
  arbiter  arb_inst (
    .acknowledge(acknowledge),
    .clk(clk),
    .grant(grant),
    .grant_encoded(grant_encoded),
    .grant_valid(grant_valid),
    .request(request),
    .rst(rst)
  );
endmodule

module arbiter (clk, rst, request, acknowledge, grant, grant_valid, grant_encoded);
  input [3:0] acknowledge;
  input clk;
  output [3:0] grant;
  output [1:0] grant_encoded;
  output grant_valid;
  input [3:0] request;
  input rst;
endmodule

(* abc9_box, blackbox *)
module MUXF8(input I0, I1, S, output O);
specify
    (I0 => O) = 0;
    (I1 => O) = 0;
    (S => O) = 0;
endspecify
endmodule

// Citation: https://github.com/alexforencich/verilog-ethernet
module abc9_test022
(
    input  wire        clk,
    input  wire        i,
    output wire [7:0]  m_eth_payload_axis_tkeep
);
    reg [7:0]  m_eth_payload_axis_tkeep_reg = 8'd0;
    assign m_eth_payload_axis_tkeep = m_eth_payload_axis_tkeep_reg;
    always @(posedge clk)
        m_eth_payload_axis_tkeep_reg <= i ? 8'hff : 8'h0f;
endmodule

// Citation: https://github.com/riscv/riscv-bitmanip
module abc9_test023 #(
	parameter integer N = 2,
	parameter integer M = 2
) (
	input [7:0] din,
	output [M-1:0] dout
);
	wire [2*M-1:0] mask = {M{1'b1}};
	assign dout = (mask << din[N-1:0]) >> M;
endmodule

module abc9_test024(input [3:0] i, output [3:0] o);
abc9_test024_sub a(i[1:0], o[1:0]);
endmodule

module abc9_test024_sub(input [1:0] i, output [1:0] o);
assign o = i;
endmodule

module abc9_test025(input [3:0] i, output [3:0] o);
abc9_test024_sub a(i[2:1], o[2:1]);
endmodule

module abc9_test026(output [3:0] o, p);
assign o = { 1'b1, 1'bx };
assign p = { 1'b1, 1'bx, 1'b0 };
endmodule

module abc9_test030(input [3:0] d, input en, output reg [3:0] q);
always @*
  if (en)
    q <= d;
endmodule

module abc9_test031(input clk1, clk2, d, output reg q1, q2);
always @(posedge clk1) q1 <= d;
always @(negedge clk2) q2 <= q1;
endmodule

module abc9_test032(input clk, d, r, output reg q);
always @(posedge clk or posedge r)
    if (r) q <= 1'b0;
    else q <= d;
endmodule

module abc9_test033(input clk, d, r, output reg q);
always @(negedge clk or posedge r)
    if (r) q <= 1'b1;
    else q <= d;
endmodule

module abc9_test034(input clk, d, output reg q1, q2);
always @(posedge clk) q1 <= d;
always @(posedge clk) q2 <= q1;
endmodule

module abc9_test035(input clk, d, output reg [1:0] q);
always @(posedge clk) q[0] <= d;
always @(negedge clk) q[1] <= q[0];
endmodule

module abc9_test036(input A, B, S, output [1:0] O);
  (* keep *)
  MUXF8 m  (
    .I0(I0),
    .I1(I1),
    .O(O[0]),
    .S(S)
  );
  MUXF8 m2  (
    .I0(I0),
    .I1(I1),
    .O(O[1]),
    .S(S)
  );
endmodule
