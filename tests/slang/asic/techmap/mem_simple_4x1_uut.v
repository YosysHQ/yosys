module uut (clk, rst, out, counter);

input clk, rst;
output reg [7:0] out;
output reg [4:0] counter;

reg [7:0] memory [0:19];

always @(posedge clk) begin
	counter <= rst || counter == 19 ? 0 : counter+1;
	memory[counter] <= counter;
	out <= memory[counter];
end

endmodule
