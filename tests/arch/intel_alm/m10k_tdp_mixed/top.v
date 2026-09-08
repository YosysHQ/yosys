module top #(parameter UNIT=10, ALANES=2, BLANES=1, SAME_CLOCK=0)(
 input ac,bc,ae,be,aw,bw,
 input [10-$clog2(ALANES)-1:0] aa,
 input [10-$clog2(BLANES)-1:0] ba,
 input [UNIT*ALANES-1:0] ad,
 input [UNIT*BLANES-1:0] bd,
 output reg [UNIT*ALANES-1:0] aq,
 output reg [UNIT*BLANES-1:0] bq);
 (* ram_style="m10k_tdp_mixed" *) reg [UNIT-1:0] mem[0:1023];
 wire clock_b=SAME_CLOCK ? ac : bc;
`ifdef FORMAL
 // Unequal ports overlap when the narrow chunk is either lane of the wide word.
 always @* assume (!(ae && be && (aw || bw) &&
                    (ALANES==BLANES ? aa==ba : (aa*ALANES)/2 == (ba*BLANES)/2)));
`endif
 integer i;
 initial for(i=0;i<1024;i=i+1) mem[i]=(i*73)^(i>>1)^'ha6;
 genvar lane;
 generate for(lane=0;lane<ALANES;lane=lane+1) begin: a_lane
  if(ALANES==1) begin
   always @(posedge ac) if(ae) begin
    if(aw) begin mem[aa]<=ad;aq<=ad;end else aq<=mem[aa];
   end
  end else begin
   localparam [$clog2(ALANES)-1:0] INDEX=lane;
   always @(posedge ac) if(ae) begin
    if(aw) begin mem[{aa,INDEX}]<=ad[lane*UNIT+:UNIT];aq[lane*UNIT+:UNIT]<=ad[lane*UNIT+:UNIT];end
    else aq[lane*UNIT+:UNIT]<=mem[{aa,INDEX}];
   end
  end
 end
 for(lane=0;lane<BLANES;lane=lane+1) begin: b_lane
  if(BLANES==1) begin
   always @(posedge clock_b) if(be) begin
    if(bw) begin mem[ba]<=bd;bq<=bd;end else bq<=mem[ba];
   end
  end else begin
   localparam [$clog2(BLANES)-1:0] INDEX=lane;
   always @(posedge clock_b) if(be) begin
    if(bw) begin mem[{ba,INDEX}]<=bd[lane*UNIT+:UNIT];bq[lane*UNIT+:UNIT]<=bd[lane*UNIT+:UNIT];end
    else bq[lane*UNIT+:UNIT]<=mem[{ba,INDEX}];
   end
  end
 end endgenerate
endmodule
