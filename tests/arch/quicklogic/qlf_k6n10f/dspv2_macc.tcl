yosys -import

proc testcase {top} {
	log -header "Testcase $top"
	log -push

	design -load ast
	prep -top $top
	design -save gold

	design -load ast
	hierarchy -top $top
	synth_quicklogic -family qlf_k6n10f -dspv2 -run :coarse
	opt_clean
	select -assert-none t:\$mul
	stat
	dump $top
	select -assert-count 1 t:QL_DSPV2_MULTACC
	read_verilog +/quicklogic/qlf_k6n10f/dspv2_sim.v
	prep -flatten -top $top
	design -save gate

	design -clear
	design -copy-from gate -as gate A:top
	design -copy-from gold -as gold A:top
	async2sync
	equiv_make gold gate equiv
	opt -fast equiv
	equiv_induct equiv
	equiv_status -assert equiv

	log -pop
}

read_verilog dspv2_macc.v
design -save ast

testcase "macc_simple"
testcase "macc_simple_clr"
testcase "macc_simple_arst"
testcase "macc_simple_ena"
testcase "macc_simple_arst_clr_ena"
testcase "macc_simple_preacc_clr"
testcase "macc_simple_signed"
testcase "macc_simple_signed_subtract"
