module addbit (
a      , // first input
b      , // Second input
ci     , // Carry input
sum    , // sum output
co       // carry output
);
//Input declaration
input a;
input b;
input ci;
//Ouput declaration
output sum;
output co;
//Port Data types
wire  a;
wire  b;
wire  ci;
wire  sum;
wire  co;
//Code starts here
assign {co,sum} = a + b + ci;

endmodule // End of Module addbit
