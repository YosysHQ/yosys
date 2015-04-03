
module memtest00(clk, setA, setB, y);

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

module memtest01(clk, wr_en, wr_addr, wr_value, rd_addr, rd_value);

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

module memtest02(clk, setA, setB, addr, bit, y1, y2, y3, y4);

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

// ----------------------------------------------------------

module memtest03(clk, wr_addr, wr_data, wr_enable, rd_addr, rd_data);

input clk, wr_enable;
input [3:0] wr_addr, wr_data, rd_addr;
output reg [3:0] rd_data;

reg [3:0] memory [0:15];

always @(posedge clk) begin
	if (wr_enable)
		memory[wr_addr] <= wr_data;
	rd_data <= memory[rd_addr];
end

endmodule

// ----------------------------------------------------------

module memtest04(clk, wr_addr, wr_data, wr_enable, rd_addr, rd_data);

input clk, wr_enable;
input [3:0] wr_addr, wr_data, rd_addr;
output [3:0] rd_data;

reg rd_addr_buf;
reg [3:0] memory [0:15];

always @(posedge clk) begin
	if (wr_enable)
		memory[wr_addr] <= wr_data;
	rd_addr_buf <= rd_addr;
end

assign rd_data = memory[rd_addr_buf];

endmodule

// ----------------------------------------------------------

module memtest05(clk, addr, wdata, rdata, wen);

input clk;
input [1:0] addr;
input [7:0] wdata;
output reg [7:0] rdata;
input [3:0] wen;

reg [7:0] mem [0:3];

integer i;
always @(posedge clk) begin
	for (i = 0; i < 4; i = i+1)
		if (wen[i]) mem[addr][i*2 +: 2] <= wdata[i*2 +: 2];
	rdata <= mem[addr];
end

endmodule

// ----------------------------------------------------------

module memtest06_sync(input clk, input rst, input [2:0] idx, input [7:0] din, output [7:0] dout);
    (* gentb_constant=0 *) wire rst;
    reg [7:0] test [0:7];
    integer i;
    always @(posedge clk) begin
        if (rst) begin
            for (i=0; i<8; i=i+1)
                test[i] <= 0;
        end else begin
            test[0][2] <= din[1];
            test[0][5] <= test[0][2];
            test[idx][3] <= din[idx];
            test[idx][6] <= test[idx][2];
            test[idx][idx] <= !test[idx][idx];
        end
    end
    assign dout = test[idx];
endmodule

module memtest06_async(input clk, input rst, input [2:0] idx, input [7:0] din, output [7:0] dout);
    (* gentb_constant=0 *) wire rst;
    reg [7:0] test [0:7];
    integer i;
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            for (i=0; i<8; i=i+1)
                test[i] <= 0;
        end else begin
            test[0][2] <= din[1];
            test[0][5] <= test[0][2];
            test[idx][3] <= din[idx];
            test[idx][6] <= test[idx][2];
            test[idx][idx] <= !test[idx][idx];
        end
    end
    assign dout = test[idx];
endmodule

// ----------------------------------------------------------

module memtest07(clk, addr, woffset, wdata, rdata);

input clk;
input [1:0] addr;
input [3:0] wdata;
input [1:0] woffset;
output reg [7:0] rdata;

reg [7:0] mem [0:3];

integer i;
always @(posedge clk) begin
	mem[addr][woffset +: 4] <= wdata;
	rdata <= mem[addr];
end

endmodule

// ----------------------------------------------------------

module memtest08(input clk, input [3:0] a, b, c, output reg [3:0] y);
	reg [3:0] mem [0:15] [0:15];
	always @(posedge clk) begin
		y <= mem[a][b];
		mem[a][b] <= c;
	end
endmodule

// ----------------------------------------------------------

module memtest09 (
    input clk,
    input [3:0] a_addr, a_din, b_addr, b_din,
    input a_wen, b_wen,
    output reg [3:0] a_dout, b_dout
);
    reg [3:0] memory [10:35];

    always @(posedge clk) begin
        if (a_wen)
            memory[10 + a_addr] <= a_din;
        a_dout <= memory[10 + a_addr];
    end

    always @(posedge clk) begin
        if (b_wen && (10 + a_addr != 20 + b_addr || !a_wen))
            memory[20 + b_addr] <= b_din;
        b_dout <= memory[20 + b_addr];
    end
endmodule

