// Direct primitive contract: check NEW_DATA on enabled write lanes,
// complete subsequent reads and clock-enable hold against separate byte banks.
module primitive_check (
 input ac,bc,ae,be,aw,bw,
 input [1:0] am,bm,aa,ba,
 input [19:0] ad,bd,
 output mismatch);
 wire [19:0] aq,bq;
 MISTRAL_M10K_TDP #(.CFG_ABITS(9), .CFG_DBITS(20), .CFG_BYTE_ENABLE(1)) dut (
  .CLK1(ac), .CLK2(bc), .A1EN(ae), .B1EN(be), .A1WE(aw), .B1WE(bw),
  .A1BE(am), .B1BE(bm), .A1ADDR({7'b0,aa}), .B1ADDR({7'b0,ba}),
  .A1DATA(ad), .B1DATA(bd), .A1Q(aq), .B1Q(bq));
 reg [9:0] low_bank[0:3], high_bank[0:3];
 reg [19:0] expected_a,expected_b;
 reg [1:0] visible_a=0,visible_b=0;
 integer i;
 initial for(i=0;i<4;i=i+1) begin low_bank[i]=0;high_bank[i]=0;end
 always @* assume (!(ae && be && (aw || bw) && aa == ba));
 always @(posedge ac) if(ae) begin
  visible_a<=aw ? am : 2'b11;
  expected_a<=aw ? ad : {high_bank[aa],low_bank[aa]};
  if(aw && am[0]) low_bank[aa]<=ad[9:0];
  if(aw && am[1]) high_bank[aa]<=ad[19:10];
 end
 always @(posedge bc) if(be) begin
  visible_b<=bw ? bm : 2'b11;
  expected_b<=bw ? bd : {high_bank[ba],low_bank[ba]};
  if(bw && bm[0]) low_bank[ba]<=bd[9:0];
  if(bw && bm[1]) high_bank[ba]<=bd[19:10];
 end
 assign mismatch=|((aq^expected_a)&{{10{visible_a[1]}},{10{visible_a[0]}}}) |
                 |((bq^expected_b)&{{10{visible_b[1]}},{10{visible_b[0]}}});
endmodule
