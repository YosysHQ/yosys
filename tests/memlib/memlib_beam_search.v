// Test case for beam search optimization in memory_libmap
// This memory with 32 parallel read ports would cause exponential
// blowup (O(4^32) = 10^19 configurations) without beam search pruning

module memlib_beam_search (
    input wire clk,
    input wire we,
    input wire [9:0] wr_addr,
    input wire [7:0] wr_data,
    input wire [9:0] base_addr,
    output reg [255:0] parallel_out  // 32 x 8 = 256 bits
);

    reg [7:0] mem [0:1023];
    integer i;

    always @(posedge clk) begin
        if (we)
            mem[wr_addr] <= wr_data;

        // 32 parallel reads - triggers beam search
        for (i = 0; i < 32; i = i + 1) begin
            parallel_out[i*8 +: 8] <= mem[base_addr + i];
        end
    end

endmodule
