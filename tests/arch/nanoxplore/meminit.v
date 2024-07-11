module top(clk);
parameter DEPTH_LOG2 = 10;
parameter WIDTH = 36;
parameter PRIME = 237481091;
localparam DEPTH = 2**DEPTH_LOG2;

input wire clk;

(* syn_ramstyle = "distributed" *)
reg [WIDTH-1:0] mem [DEPTH-1:0];

integer i;
initial begin
    for (i = 0; i < DEPTH; i = i + 1) begin
        // Make up data by multiplying a large prime with the address,
        // then cropping and retaining the lower bits
        mem[i] = PRIME * (i*2+1);
    end
end

reg [DEPTH_LOG2-1:0] counter = 0;
reg done = 1'b0;

reg did_read = 1'b0;
reg [DEPTH_LOG2-1:0] read_addr;
reg [WIDTH-1:0] read_val;

always @(posedge clk) begin
    if (!done) begin
        did_read <= 1'b1;
        read_addr <= counter;
        read_val <= mem[counter];
    end else begin
        did_read <= 1'b0; 
    end

    if (!done)
        counter = counter + 1;
    if (counter == 0)
        done = 1;
end

wire [WIDTH-1:0] expect_val = PRIME * (read_addr*2+1);
always @(posedge clk) begin
    if (did_read) begin
        $display("addr %x expected %x actual %x", read_addr, expect_val, read_val);
        assert(read_val == expect_val);
    end
end
endmodule
