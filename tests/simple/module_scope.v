`default_nettype none

module Example(o1, o2);
   parameter [31:0] v1 = 10;
   parameter [31:0] v2 = 20;
   output [31:0] o1, o2;
   assign Example.o1 = Example.v1;
   assign Example.o2 = Example.v2;
endmodule

module ExampleLong(o1, o2);
   parameter [31:0] ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum1 = 10;
   parameter [31:0] ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum2 = 20;
   output [31:0] o1, o2;
   assign ExampleLong.o1 = ExampleLong.ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum1;
   assign ExampleLong.o2 = ExampleLong.ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum2;
endmodule

module top(
   output [31:0] a1, a2, b1, b2, c1, c2,
   output [31:0] d1, d2, e1, e2, f1, f2
);
   Example a(a1, a2);
   Example #(1) b(b1, b2);
   Example #(1, 2) c(c1, c2);
   ExampleLong d(d1, d2);
   ExampleLong #(1) e(e1, e2);
   ExampleLong #(1, 2) f(f1, f2);
endmodule
