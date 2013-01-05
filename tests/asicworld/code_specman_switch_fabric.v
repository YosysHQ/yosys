module switch_fabric(
  clk, reset, data_in0, data_in1, data_in2,
  data_in3, data_in4, data_in5, data_in_valid0,
  data_in_valid1, data_in_valid2, data_in_valid3,
  data_in_valid4, data_in_valid5, data_out0,
  data_out1, data_out2, data_out3, data_out4,
  data_out5, data_out_ack0, data_out_ack1,
  data_out_ack2, data_out_ack3, data_out_ack4,
  data_out_ack5
);

input           clk, reset;
input  [7:0]    data_in0, data_in1, data_in2, data_in3;
input  [7:0]    data_in4, data_in5;
input           data_in_valid0, data_in_valid1, data_in_valid2;
input  [7:0]    data_in_valid3, data_in_valid4, data_in_valid5;
output [7:0]    data_out0, data_out1, data_out2, data_out3;
output [7:0]    data_out4, data_out5;
output          data_out_ack0, data_out_ack1, data_out_ack2;
output [7:0]    data_out_ack3, data_out_ack4, data_out_ack5;

(* gentb_clock *)
wire clk;

switch port_0 ( .clk(clk), .reset(reset), .data_in(data_in0), 
  .data_in_valid(data_in_valid0), .data_out(data_out0), 
  .data_out_ack(data_out_ack0));

switch port_1 ( .clk(clk), .reset(reset), .data_in(data_in1), 
  .data_in_valid(data_in_valid1), .data_out(data_out1), 
  .data_out_ack(data_out_ack1));

switch port_2 ( .clk(clk), .reset(reset), .data_in(data_in2), 
  .data_in_valid(data_in_valid2), .data_out(data_out2), .
  data_out_ack(data_out_ack2));

switch port_3 ( .clk(clk), .reset(reset), .data_in(data_in3), 
  .data_in_valid(data_in_valid3), .data_out(data_out3), 
  .data_out_ack(data_out_ack3));

switch port_4 ( .clk(clk), .reset(reset), .data_in(data_in4), 
  .data_in_valid(data_in_valid4), .data_out(data_out4), 
  .data_out_ack(data_out_ack4));

switch port_5 ( .clk(clk), .reset(reset), .data_in(data_in5), 
  .data_in_valid(data_in_valid5), .data_out(data_out5), 
  .data_out_ack(data_out_ack5));

endmodule

module switch (
  clk,
  reset,
  data_in,
  data_in_valid,
  data_out,
  data_out_ack
);

input   clk;
input   reset;
input [7:0]  data_in;
input   data_in_valid;
output [7:0]  data_out;
output  data_out_ack;

reg [7:0]  data_out;
reg   data_out_ack;

always @ (posedge clk)
if (reset) begin
   data_out <= 0;
   data_out_ack <= 0;
end else if (data_in_valid) begin
   data_out <= data_in;
   data_out_ack <= 1;
end else begin
   data_out <= 0;
   data_out_ack <= 0;
end

endmodule
