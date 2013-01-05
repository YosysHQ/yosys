module explicit();
reg clk,d,rst,pre;
wire q;

// Here q_bar is not connected
// We can connect ports in any order
dff u0 (  
.q  	(q),
.d 	(d),
.clk 	(clk),
.q_bar 	(),
.rst 	(rst),
.pre 	(pre)
);

endmodule

// D fli-flop
module dff (q, q_bar, clk, d, rst, pre);
input clk, d, rst, pre;
output q, q_bar;
reg q;

assign q_bar = ~q;

always @ (posedge clk)
if (rst == 1'b1) begin
  q <= 0;
end else if (pre == 1'b1) begin
  q <= 1;
end else begin
  q <= d;
end

endmodule
