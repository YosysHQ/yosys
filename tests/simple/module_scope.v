`default_nettype none

module module_scope_Example(o1, o2);
   parameter [31:0] v1 = 10;
   parameter [31:0] v2 = 20;
   output wire [31:0] o1, o2;
   assign module_scope_Example.o1 = module_scope_Example.v1;
   assign module_scope_Example.o2 = module_scope_Example.v2;
endmodule

module module_scope_ExampleLong(o1, o2);
   parameter [31:0] ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum1 = 10;
   parameter [31:0] ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum2 = 20;
   output wire [31:0] o1, o2;
   assign module_scope_ExampleLong.o1 = module_scope_ExampleLong.ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum1;
   assign module_scope_ExampleLong.o2 = module_scope_ExampleLong.ThisIsAnExtremelyLongParameterNameToTriggerTheSHA1Checksum2;
endmodule

module module_scope_top(
   output wire [31:0] a1, a2, b1, b2, c1, c2,
   output wire [31:0] d1, d2, e1, e2, f1, f2
);
   module_scope_Example a(a1, a2);
   module_scope_Example #(1) b(b1, b2);
   module_scope_Example #(1, 2) c(c1, c2);
   module_scope_ExampleLong d(d1, d2);
   module_scope_ExampleLong #(1) e(e1, e2);
   module_scope_ExampleLong #(1, 2) f(f1, f2);
endmodule
