// Dual-Port RAM with Asynchronous Read (Distributed RAM)
// File: rams_dist.v

module rams_dist (clk, we, a, dpra, di, spo, dpo);

input clk;
input we;
input [5:0] a;
input [5:0] dpra;
input [15:0] di;
output [15:0] spo;
output [15:0] dpo;
reg [15:0] ram [63:0];

always @(posedge clk) 
begin 
 if (we)
   ram[a] <= di;
end

assign spo = ram[a];
assign dpo = ram[dpra];

endmodule
