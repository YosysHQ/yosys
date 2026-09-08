module top #(parameter UNIT=10,WLANES=4,RLANES=1)(
 input wc,rc,we,re,input [10-$clog2(WLANES)-1:0] wa,
 input [10-$clog2(RLANES)-1:0] ra,input [UNIT*WLANES-1:0] d,
 output reg [UNIT*RLANES-1:0] q);
 (* ram_style="m10k_mixed" *) reg [UNIT-1:0] mem[0:1023];
 integer i,w,r;
 initial for(i=0;i<1024;i=i+1) mem[i]=(i*73)^(i>>1)^'ha6;
 genvar lane;
 generate for(lane=0;lane<WLANES;lane=lane+1) begin: write_lane
  if(WLANES==1) begin
   always @(posedge wc) if(we) mem[wa]<=d;
  end else begin
   localparam [$clog2(WLANES)-1:0] INDEX=lane;
   always @(posedge wc) if(we) mem[{wa,INDEX}]<=d[lane*UNIT+:UNIT];
  end
 end
 for(lane=0;lane<RLANES;lane=lane+1) begin: read_lane
  if(RLANES==1) begin
   always @(posedge rc) if(re) q<=mem[ra];
  end else begin
   localparam [$clog2(RLANES)-1:0] INDEX=lane;
   always @(posedge rc) if(re) q[lane*UNIT+:UNIT]<=mem[{ra,INDEX}];
  end
 end endgenerate
endmodule
