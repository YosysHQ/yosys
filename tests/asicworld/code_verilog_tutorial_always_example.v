module always_example();
reg clk,reset,enable,q_in,data;

always @ (posedge clk)
if (reset)  begin
   data <= 0;
end else if (enable) begin   
   data <= q_in;
end

endmodule
