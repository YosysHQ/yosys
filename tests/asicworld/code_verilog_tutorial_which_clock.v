module which_clock (x,y,q,d);
input x,y,d;
output q;
reg q;

always @ (posedge x or posedge y)
   if (x) 
     q <= 1'b0;
   else
     q <= d;

endmodule
