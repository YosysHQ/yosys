// Block RAM with Optional Output Registers
// File: rams_pipeline

module rams_pipeline (clk1, clk2, we, en1, en2, addr1, addr2, di, res1, res2);
input clk1;
input clk2;
input we, en1, en2;
input [9:0] addr1;
input [9:0] addr2;
input [15:0] di;
output [15:0] res1;
output [15:0] res2;
reg [15:0] res1;
reg [15:0] res2;
reg [15:0] RAM [1023:0];
reg [15:0] do1;
reg [15:0] do2;

always @(posedge clk1)
begin
    if (we == 1'b1)
        RAM[addr1] <= di;
    do1 <= RAM[addr1];
end

always @(posedge clk2)
begin
    do2 <= RAM[addr2];
end

always @(posedge clk1)
begin
    if (en1 == 1'b1)
        res1 <= do1;
end

always @(posedge clk2)
begin
    if (en2 == 1'b1)
        res2 <= do2;
end 
endmodule
