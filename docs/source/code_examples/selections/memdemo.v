module memdemo(clk, d, y);

input clk;
input [3:0] d;
output reg [3:0] y;

integer i;
reg [1:0] s1, s2;
reg [3:0] mem [0:3];

always @(posedge clk) begin
    for (i = 0; i < 4; i = i+1)
        mem[i] <= mem[(i+1) % 4] + mem[(i+2) % 4];
    { s2, s1 } = d ? { s1, s2 } ^ d : 4'b0;
    mem[s1] <= d;
    y <= mem[s2];
end

endmodule
