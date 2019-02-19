#!/usr/bin/env bash
# Simple test of hierarchy -auto-top.

set -e

../../yosys -q -s - <<- EOY 2>&1 | grep "Automatically selected TOP as design top module"
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

../../yosys -q -s - <<- EOY 2>&1 | grep "Automatically selected TOP as design top module"
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

../../yosys -q -s - <<- EOY 2>&1 | grep "Automatically selected noTop as design top module."
  read_verilog << EOV
    module aoi12(a, y);
      input a;
      output y;
      assign y = ~a;
    endmodule

    module noTop(a, y);
      input a;
      output [31:0] y;
    endmodule
  EOV
  hierarchy -auto-top
EOY
