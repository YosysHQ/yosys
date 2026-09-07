module lutram_init(input clk, we, input [4:0] waddr, raddr,
                   input [7:0] data, output [7:0] q);
    (* ramstyle = "mlab" *) reg [7:0] mem [0:31];
    integer i;
    initial begin
`ifdef INIT_FROM_FILE
        $readmemh("lutram_init.hex", mem);
`else
        for (i = 0; i < 32; i = i + 1)
            mem[i] = ((i * 73) ^ (i >> 1) ^ 8'ha6) & 8'hff;
`endif
    end
    always @(posedge clk)
        if (we) mem[waddr] <= data;
    assign q = mem[raddr];
endmodule
