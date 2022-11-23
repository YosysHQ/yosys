module sumprod(a, b, c, sum, prod);

  input [7:0] a, b, c;
  output [7:0] sum, prod;

  {* sumstuff *}
  assign sum = a + b + c;
  {* *}

  assign prod = a * b * c;

endmodule
