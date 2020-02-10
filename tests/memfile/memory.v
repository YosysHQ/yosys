// A memory initialized with an external file

module memory (
    input             clk_i,
    input             we_i,
    input       [5:0] addr_i,
    input      [31:0] data_i,
    output reg [31:0] data_o
);

parameter MEMFILE = "";

reg [31:0] mem [0:63];

initial $readmemb(MEMFILE,mem);

always @(posedge clk_i) begin
    if (we_i)
        mem[addr_i] <= data_i;
    data_o <= mem[addr_i];
end

endmodule
