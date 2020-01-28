/*
Example from: https://www.latticesemi.com/-/media/LatticeSemi/Documents/UserManuals/EI/iCEcube201701UserGuide.ashx?document_id=52071 [p. 74].
*/
module top(data, addr);
output [3:0] data; // Note: this prompts a Yosys warning, but
                   //       vendor doc does not contain 'reg'
input [4:0] addr;
always @(addr) begin
case (addr)
0 : data = 'h4;
1 : data = 'h9;
2 : data = 'h1;
15 : data = 'h8;
16 : data = 'h1;
17 : data = 'h0;
default : data = 'h0;
endcase
end
endmodule
