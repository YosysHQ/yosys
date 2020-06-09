`default_nettype none
module reversed #(parameter WIDTH=32, SELW=4, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input wire             clk,
    input wire [CTRLW-1:0] ctrl,
    input wire [DINW-1:0]  din,
    input wire [SELW-1:0]  sel,
    output reg [WIDTH-1:0] dout);
   
   localparam SLICE = WIDTH/(SELW**2);
   always @(posedge clk) begin
      dout[(WIDTH-ctrl*sel)-:SLICE] <= din;
   end
endmodule

