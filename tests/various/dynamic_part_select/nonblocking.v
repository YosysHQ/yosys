module nonblocking #(parameter WIDTH=32, SELW=1, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input                  clk,
    input [CTRLW-1:0] 	   ctrl,
    input [DINW-1:0] 	   din,
    input [SELW-1:0] 	   sel,
    output reg [WIDTH-1:0] dout);
   
   localparam SLICE = WIDTH/(SELW**2);
   always @(posedge clk) begin
      dout <= dout + 1;
      dout[ctrl*sel+:SLICE] <= din ;
   end
   
endmodule
