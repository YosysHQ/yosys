// Latch with Positive Gate and Asynchronous Reset
// File: latches.v
module latches (
                input G,
                input D,
                input CLR,
                output reg Q
               );
always @ *
begin
 if(CLR)
  Q = 0;
 else if(G)
  Q = D;
end

endmodule               
