# gw_sh run.tcl
exec yosys -p "synth_gowin -top demo -vout demo_syn.v" demo.v
add_file -cst demo.cst
add_file -sdc demo.sdc
add_file -vm demo_syn.v
add_file -cfg device.cfg
set_option -device GW1NR-9-QFN88-6
set_option -pn GW1NR-LV9QN88C6/I5
run_pnr -opt pnr.cfg
