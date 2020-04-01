module dynslice (
    input clk ,
    input [9:0] ctrl ,
    input [15:0] din ,
    input [3:0] sel ,
    output reg [127:0] dout
);
always @(posedge clk)
begin
    dout[ctrl*sel+:16] <= din ;
end
endmodule
