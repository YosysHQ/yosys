module test001(input [2:0] idx, input [31:0] data, output [3:0] slice_up, slice_down);
wire [5:0] offset = idx << 2;
assign slice_up = data[offset +: 4];
assign slice_down = data[offset + 3 -: 4];
endmodule
