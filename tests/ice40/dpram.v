/*
Example from: https://www.latticesemi.com/-/media/LatticeSemi/Documents/UserManuals/EI/iCEcube201701UserGuide.ashx?document_id=52071 [p. 72].
*/
module top (din, write_en, waddr, wclk, raddr, rclk, dout);
parameter addr_width = 8;
parameter data_width = 8;
input [addr_width-1:0] waddr, raddr;
input [data_width-1:0] din;
input write_en, wclk, rclk;
output [data_width-1:0] dout;
reg [data_width-1:0] dout;
reg [data_width-1:0] mem [(1<<addr_width)-1:0]
/* synthesis syn_ramstyle = "no_rw_check" */ ;
always @(posedge wclk) // Write memory.
begin
if (write_en)
mem[waddr] <= din; // Using write address bus.
end
always @(posedge rclk) // Read memory.
begin
dout <= mem[raddr]; // Using read address bus.
end
endmodule
