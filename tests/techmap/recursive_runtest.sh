set -e

../../yosys -p 'read_verilog recursive.v; hierarchy -top top; techmap -map recursive_map.v -max_iter 1; select -assert-count 2 t:sub; select -assert-count 2 t:bar'
