#!/usr/bin/env bash
# Simple test of hierarchy -auto-top.

set -e

echo -n "  TOP first - "
../../yosys -s - <<- EOY | grep "Automatically selected TOP as design top module"
  read_verilog << EOV
    module TOP(a, y);
      input a;
      output [31:0] y;

      aoi12 p [31:0] (a, y);
    endmodule

    module aoi12(a, y);
      input a;
      output y;
      assign y = ~a;
    endmodule
  EOV
  hierarchy -auto-top
EOY

echo -n "  TOP last - "
../../yosys -s - <<- EOY | grep "Automatically selected TOP as design top module"
  read_verilog << EOV
    module aoi12(a, y);
      input a;
      output y;
      assign y = ~a;
    endmodule

    module TOP(a, y);
      input a;
      output [31:0] y;

      aoi12 foo (a, y);
    endmodule
  EOV
  hierarchy -auto-top
EOY

echo -n "  no explicit top - "
../../yosys -s - <<- EOY | grep "Automatically selected noTop as design top module."
  read_verilog << EOV
    module aoi12(a, y);
      input a;
      output y;
      assign y = ~a;
    endmodule

    module noTop(a, y);
      input a;
      output [31:0] y;
      assign y = a;
    endmodule
  EOV
  hierarchy -auto-top
EOY
