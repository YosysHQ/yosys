set -ev

../../yosys -p 'hierarchy -top top; techmap -map recursive_map.v -max_iter 1; select -assert-count 2 t:sub; select -assert-count 2 t:bar' recursive.v
