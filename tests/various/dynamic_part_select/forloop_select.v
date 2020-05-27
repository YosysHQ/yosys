`default_nettype none
module forloop_select #(parameter WIDTH=16, SELW=4, CTRLW=$clog2(WIDTH), DINW=2**SELW)
   (input wire             clk,
    input wire [CTRLW-1:0] ctrl,
    input wire [DINW-1:0]  din,
    input wire             en,
    output reg [WIDTH-1:0] dout);

   reg [SELW:0]            sel;
   localparam SLICE = WIDTH/(SELW**2);

   always @(posedge clk)
     begin
        if (en) begin
           for (sel = 0; sel <= 4'hf; sel=sel+1'b1)
             dout[(ctrl*sel)+:SLICE] <= din;
        end
     end
endmodule
