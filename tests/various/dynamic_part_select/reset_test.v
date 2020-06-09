`default_nettype none
module reset_test  #(parameter WIDTH=32, SELW=1, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input wire             clk,
    input wire             reset,
    input wire [CTRLW-1:0] ctrl,
    input wire [DINW-1:0]  din,
    input wire [SELW-1:0]  sel,
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
      dout[ctrl*sel+:SLICE] <= din;
   end
endmodule
