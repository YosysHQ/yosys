//-----------------------------------------------------
// Design Name : mux21_switch
// File Name   : mux21_switch.v
// Function    : 2:1 Mux using Switch Primitives
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module mux21_switch (out, ctrl, in1, in2);
   
   output out;                    
   input  ctrl, in1, in2;         
   wire          w;            

   supply1 power;             
   supply0 ground;      
   
   pmos N1 (w, power, ctrl);     
   nmos N2 (w, ground, ctrl);   
   
   cmos C1 (out, in1, w, ctrl);   
   cmos C2 (out, in2, ctrl, w);
   
endmodule
