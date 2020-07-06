module reset_test  #(parameter WIDTH=32, SELW=1, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input                  clk,
    input [CTRLW-1:0] 	   ctrl,
    input [DINW-1:0] 	   din,
    input [SELW-1:0] 	   sel,
    output reg [WIDTH-1:0] dout);
   
   reg [SELW:0] 		   i;
   wire [SELW-1:0] 	   rval = {reset, {SELW-1{1'b0}}};
   localparam SLICE = WIDTH/(SELW**2);
   // Doing exotic reset. masking 2 LSB bits to 0, 6 MSB bits to 1 for
   // whatever reason.
   always @(posedge clk) begin
      if (reset) begin: reset_mask
         for (i = 0; i < {SELW{1'b1}}; i=i+1) begin
            dout[i*rval+:SLICE] <= 32'hDEAD;
         end
      end
      //else begin
      dout[ctrl*sel+:SLICE] <= din;
      //end
   end
endmodule
