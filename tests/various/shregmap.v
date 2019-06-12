module shregmap_test(input i, clk, output [1:0] q);
reg head = 1'b0;
reg [3:0] shift1 = 4'b0000;
reg [3:0] shift2 = 4'b0000;

always @(posedge clk) begin
    head <= i;
    shift1 <= {shift1[2:0], head};
    shift2 <= {shift2[2:0], head};
end

assign q = {shift2[3], shift1[3]};
endmodule

module $__SHREG_DFF_P_(input C, D, output Q);
parameter DEPTH = 1;
parameter [DEPTH-1:0] INIT = {DEPTH{1'b0}};
reg [DEPTH-1:0] r = INIT;
always @(posedge C) 
    r <= { r[DEPTH-2:0], D };
assign Q = r[DEPTH-1];
endmodule
