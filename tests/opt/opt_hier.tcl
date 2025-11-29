yosys -import

# per each opt_hier_*.v source file, confirm flattening and hieropt+flattening
# are combinationally equivalent
foreach fn [glob opt_hier_*.v] {
	log -header "Test $fn"
	log -push
	design -reset

	read_verilog $fn
	hierarchy -auto-top
	prep -top top
	design -save start
	flatten
	design -save gold
	design -load start
	opt -hier
	# check any instances marked `should_get_optimized_out` were
	# indeed optimized out
	select -assert-none a:should_get_optimized_out
	dump
	flatten
	design -save gate

	design -reset
	design -copy-from gold -as gold A:top
	design -copy-from gate -as gate A:top
	yosys rename -hide
	equiv_make gold gate equiv
	equiv_induct equiv
	equiv_status -assert equiv

	log -pop
}
