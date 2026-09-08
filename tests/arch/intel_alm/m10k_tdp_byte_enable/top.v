module top #(parameter WIDTH=20, CONST_MASK=0, SAME_CLOCK=0) (
 input ac,bc,ae,be,aw,bw,
 input [1:0] am,bm,
 input [8:0] aa,ba,
 input [WIDTH-1:0] ad,bd,
 output reg [WIDTH-1:0] aq,bq);
 localparam BYTE=WIDTH/2;
 (* ram_style="m10k_tdp_byte" *) reg [WIDTH-1:0] mem[0:511];
 wire [1:0] mask_a=CONST_MASK ? {1'b0,am[0]} : am;
 wire [1:0] mask_b=CONST_MASK ? {bm[1],1'b1} : bm;
 wire clock_b=SAME_CLOCK ? ac : bc;
`ifdef FORMAL
 // Exclude unsupported cross-port collisions throughout the timing window.
 always @* assume (!(ae && be && (aw || bw) && aa == ba));
`endif
 integer i;
 initial for(i=0;i<512;i=i+1) mem[i]=(i*73)^(i>>1)^'ha6;
 // Reads explicitly exclude writes; outputs hold during writes.
 // memory_libmap supplies any output-hold emulation required by the primitive.
 always @(posedge ac) if(ae && !aw) aq<=mem[aa];
 always @(posedge clock_b) if(be && !bw) bq<=mem[ba];
 genvar lane;
 generate for(lane=0;lane<2;lane=lane+1) begin
  always @(posedge ac) if(ae && aw && mask_a[lane]) mem[aa][lane*BYTE+:BYTE]<=ad[lane*BYTE+:BYTE];
  always @(posedge clock_b) if(be && bw && mask_b[lane]) mem[ba][lane*BYTE+:BYTE]<=bd[lane*BYTE+:BYTE];
 end endgenerate
endmodule
