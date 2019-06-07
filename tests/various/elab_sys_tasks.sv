module test;
localparam X=1;
genvar i;
generate
if (X == 1)
  $info("X is 1");
if (X == 1)
  $warning("X is 1");
else
  $error("X is not 1");
case (X)
  1: $info("X is 1 in a case statement");
endcase
//case (X-1)
//  1: $warn("X is 2");
//  default: $warn("X might be anything in a case statement");
//endcase
for (i = 0; i < 3; i = i + 1)
begin
  case(i)
    0: $info;
    1: $warning;
    default: $info("default case statemnent");
  endcase
end

$info("This is a standalone $info(). Next $info has no parameters");
$info;
endgenerate
endmodule
