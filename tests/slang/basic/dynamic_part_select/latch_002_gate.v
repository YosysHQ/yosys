`default_nettype none
module latch_002_gate(dword, vect, sel, st);
   output reg [63:0] dword;
   input wire [7:0]  vect;
   input wire [7:0]  sel;
   input wire 	     st;
   reg [63:0] 	     mask;
   reg [63:0] 	     data;
   always @*
     case (|(st))
       1'b 1:
         begin
            mask  = (8'b 11111111)<<((((8)*(sel)))+(0));
            data  = ((8'b 11111111)&(vect[7:0]))<<((((8)*(sel)))+(0));
            dword <= ((dword)&(~(mask)))|(data);
         end
     endcase
endmodule
