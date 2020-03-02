module simpledff
  (input wire clk, rstn,
   input wire [15:0]   din,
   output logic [15:0] dout);


   always_ff @(posedge clk) begin
      if (~rstn) dout <= 0;
      else       dout <= din;
   end
endmodule // simpledff
