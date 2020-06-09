`default_nettype none
module latch_002
  (dword, sel, st, vect);
   output reg [63:0] dword;
   input wire [7:0]  vect;
   input wire [7:0]  sel;
   input wire        st;
   
   always @(*) begin
      if (st)
	dword[8*sel +:8] <= vect[7:0];
   end
endmodule // latch_002
