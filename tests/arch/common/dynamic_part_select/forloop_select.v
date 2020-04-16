module forloop_select #(parameter WIDTH=256, SELW=4)
   (input                  clk ,
    input [9:0] 	   ctrl ,
    input [15:0] 	   din ,
    input 		   en,
    output reg [WIDTH-1:0] dout);
   
   reg [SELW-1:0] 	   sel;
   localparam SLICE = WIDTH/(SELW**2);
   
   always @(posedge clk)
     begin
        if (en) begin
           for (sel = 0; sel < 4'hf; sel=sel+1'b1)
             dout[(ctrl*sel)+:SLICE] <= din;
        end
     end
endmodule

