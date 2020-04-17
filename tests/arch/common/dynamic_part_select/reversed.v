module reversed #(parameter WIDTH=256, SELW=2)
   (input                  clk ,
    input [9:0] 	   ctrl ,
    input [15:0] 	   din ,
    input [SELW-1:0] 	   sel ,
    output reg [WIDTH-1:0] dout);
   
   localparam SLICE = WIDTH/(SELW**2);
   always @(posedge clk) begin
      dout[(WIDTH-ctrl*sel)-:SLICE] <= din;
   end
endmodule

