module gate (
    input clk, wen,
    input [2:0] addr,
    input [3:0] wdata,
    output [3:0] rdata
);

reg [3:0] m [7:0];
initial
    $readmemh("gold.m.mem", m);

always @(posedge clk) begin
    if (wen)
        m[addr] <= wdata;
    else
        rdata <= m[addr];
end

endmodule