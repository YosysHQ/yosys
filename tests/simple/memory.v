
module test00(clk, setA, setB, y);

input clk, setA, setB;
output y;
reg mem [1:0];

always @(posedge clk) begin
	if (setA) mem[0] <= 0;  // this is line 9
	if (setB) mem[0] <= 1;  // this is line 10
end

assign y = mem[0];

endmodule

// ----------------------------------------------------------

module test01(clk, wr_en, wr_addr, wr_value, rd_addr, rd_value);

input clk, wr_en;
input [3:0] wr_addr, rd_addr;
input [7:0] wr_value;
output reg [7:0] rd_value;

reg [7:0] data [15:0];

always @(posedge clk)
	if (wr_en)
		data[wr_addr] <= wr_value;

always @(posedge clk)
	rd_value <= data[rd_addr];

endmodule

// ----------------------------------------------------------

module test02(clk, setA, setB, addr, bit, y1, y2, y3, y4);

input clk, setA, setB;
input [1:0] addr;
input [2:0] bit;
output reg y1, y2;
output y3, y4;

reg [7:0] mem1 [3:0];

(* mem2reg *)
reg [7:0] mem2 [3:0];

always @(posedge clk) begin
	if (setA) begin
		mem1[0] <= 10;
		mem1[1] <= 20;
		mem1[2] <= 30;
		mem2[0] <= 17;
		mem2[1] <= 27;
		mem2[2] <= 37;
	end
	if (setB) begin
		mem1[0] <=  1;
		mem1[1] <=  2;
		mem1[2] <=  3;
		mem2[0] <= 71;
		mem2[1] <= 72;
		mem2[2] <= 73;
	end
	y1 <= mem1[addr][bit];
	y2 <= mem2[addr][bit];
end

assign y3 = mem1[addr][bit];
assign y4 = mem2[addr][bit];

endmodule

