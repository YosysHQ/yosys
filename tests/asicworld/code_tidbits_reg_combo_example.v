module reg_combo_example( a, b, y);
input a, b;
output y;

reg   y;
wire a, b;

always @ ( a or b)
begin	
  y = a & b;
end

endmodule
