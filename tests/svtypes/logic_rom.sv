module top(input [3:0] addr, output [7:0] data);
    logic [7:0] mem[0:15];
    assign data = mem[addr];
    integer i;
    initial for(i = 0; i < 16; i = i + 1) mem[i] = i;
endmodule
