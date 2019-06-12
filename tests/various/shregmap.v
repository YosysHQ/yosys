module shregmap_static_test(input i, clk, output [1:0] q);
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

module shregmap_variable_test(input i, clk, input [1:0] l1, l2, output [1:0] q);
reg head = 1'b0;
reg [3:0] shift1 = 4'b0000;
reg [3:0] shift2 = 4'b0000;

always @(posedge clk) begin
    head <= i;
    shift1 <= {shift1[2:0], head};
    shift2 <= {shift2[2:0], head};
end

assign q = {shift2[l2], shift1[l1]};
endmodule

module $__XILINX_SHREG_(input C, D, input [1:0] L, output Q);
parameter CLKPOL = 1;
parameter ENPOL = 1;
parameter DEPTH = 1;
parameter [DEPTH-1:0] INIT = {DEPTH{1'b0}};
reg [DEPTH-1:0] r = INIT;
wire clk = C ^ CLKPOL;
always @(posedge C)
    r <= { r[DEPTH-2:0], D };
assign Q = r[L];
endmodule
