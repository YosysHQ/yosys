module sub_rom (input clk, input [3:0] addr, output reg [7:0] data);
    reg [7:0] mem [0:15];

    always @(posedge clk)
        data <= mem[addr];
endmodule

module top (input clk, input [3:0] addr, output [7:0] data, input [3:0] f_addr, input [7:0] f_data);
    sub_rom u_sub_rom (clk, addr, data);

    always @(posedge clk) 
        assume(u_sub_rom.mem[f_addr] == f_data);
endmodule
