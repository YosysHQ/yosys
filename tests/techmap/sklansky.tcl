yosys -import

read_verilog +/choices/sklansky.v
read_verilog -icells lcu_refined.v
design -save init

for {set i 1} {$i <= 16} {incr i} {
    design -load init
    chparam -set WIDTH $i
    yosys proc
    opt_clean
    equiv_make lcu _80_lcu_sklansky equiv
    equiv_simple equiv
    equiv_status -assert equiv
}
