module top #(parameter WIDTH=10, CONST_DATA=0, SAME_CLOCK=0, ABITS=(WIDTH<=10 ? 10 : 9)) (
 input ac,bc,ae,be,aw,bw,
 input [ABITS-1:0] aa,ba,
 input [WIDTH-1:0] ad,bd,
 output reg [WIDTH-1:0] aq,bq);
 (* ram_style="m10k_tdp" *) reg [WIDTH-1:0] mem[0:(1<<ABITS)-1];
`ifdef FORMAL
 // Exclude hardware-undefined cross-port collisions; both clocks, enables,
 // data and noncolliding addresses remain unconstrained.
 always @* assume (!(ae && be && (aw || bw) && aa == ba));
`endif
 wire clock_b = SAME_CLOCK ? ac : bc;
 wire [WIDTH-1:0] data_a = CONST_DATA ? ((ad & 'h3ff) ^ 'h93a00) : ad;
 wire [WIDTH-1:0] data_b = CONST_DATA ? ((bd & 'h3ff) ^ 'h2bc00) : bd;
 integer i;
 initial for(i=0;i<(1<<ABITS);i=i+1) mem[i]=(i*73)^(i>>1)^'ha6;
 always @(posedge ac) if(ae) begin
  if(aw) begin mem[aa]<=data_a; aq<=data_a; end
  else aq<=mem[aa];
 end
 always @(posedge clock_b) if(be) begin
  if(bw) begin mem[ba]<=data_b; bq<=data_b; end
  else bq<=mem[ba];
 end
endmodule
