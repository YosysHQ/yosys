//sfir_shifter.v
(* dont_touch = "yes" *)
module sfir_shifter #(parameter dsize = 16, nbtap = 4)
                     (input clk,input [dsize-1:0] datain, output [dsize-1:0] dataout);

   (* srl_style = "srl_register" *) reg [dsize-1:0] tmp [0:2*nbtap-1];
   integer i;

   always @(posedge clk)
     begin
        tmp[0] <= datain;
        for (i=0; i<=2*nbtap-2; i=i+1)
          tmp[i+1] <= tmp[i];
     end

   assign dataout = tmp[2*nbtap-1];

endmodule
// sfir_shifter
