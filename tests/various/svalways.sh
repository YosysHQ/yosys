#!/bin/bash

trap 'echo "ERROR in svalways.sh" >&2; exit 1' ERR

# Good case
../../yosys -f "verilog -sv" -qp proc - <<EOT
module top(input clk, en, d, output reg p, q, r);

always_ff @(posedge clk)
	p <= d;

always_comb
	q = ~d;

always_latch
	if (en) r = d;

endmodule
EOT

# Incorrect always_comb syntax
((../../yosys -f "verilog -sv" -qp proc -|| true) <<EOT
module top(input d, output reg q);

always_comb @(d)
	q = ~d;

endmodule
EOT
) 2>&1 | grep -F "<stdin>:3: ERROR: syntax error, unexpected '@'" > /dev/null

# Incorrect use of always_comb
((../../yosys -f "verilog -sv" -qp proc -|| true) <<EOT
module top(input en, d, output reg q);

always_comb
	if (en) q = d;

endmodule
EOT
) 2>&1 | grep -F "ERROR: Latch inferred for signal \`\\top.\\q' from always_comb process" > /dev/null

# Incorrect use of always_latch
((../../yosys -f "verilog -sv" -qp proc -|| true) <<EOT
module top(input en, d, output reg q);

always_latch
	q = !d;

endmodule
EOT
) 2>&1 | grep -F "ERROR: No latch inferred for signal \`\\top.\\q' from always_latch process" > /dev/null

# Incorrect use of always_ff
((../../yosys -f "verilog -sv" -qp proc -|| true) <<EOT
module top(input en, d, output reg q);

always_ff @(*)
	q = !d;

endmodule
EOT
) 2>&1 | grep -F "ERROR: Found non edge/level sensitive event in always_ff process" > /dev/null
