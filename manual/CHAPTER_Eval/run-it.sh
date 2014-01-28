#!/bin/bash

openmsp430_mods="
omsp_alu
omsp_clock_module
omsp_dbg
omsp_dbg_uart
omsp_execution_unit
omsp_frontend
omsp_mem_backbone
omsp_multiplier
omsp_register_file
omsp_sfr
omsp_sync_cell
omsp_sync_reset
omsp_watchdog
openMSP430"

or1200_mods="
or1200_alu
or1200_amultp2_32x32
or1200_cfgr
or1200_ctrl
or1200_dc_top
or1200_dmmu_tlb
or1200_dmmu_top
or1200_du
or1200_except
or1200_fpu
or1200_freeze
or1200_ic_fsm
or1200_ic_ram
or1200_ic_tag
or1200_ic_top
or1200_if
or1200_immu_tlb
or1200_lsu
or1200_mem2reg
or1200_mult_mac
or1200_operandmuxes
or1200_pic
or1200_pm
or1200_qmem_top
or1200_reg2mem
or1200_rf
or1200_sb
or1200_sprs
or1200_top
or1200_tt
or1200_wbmux"

yosys_cmds="hierarchy -check; proc; opt; fsm; opt; memory; opt; techmap; opt; abc; opt"

yosys -p "$yosys_cmds" -o openmsp430_ys.v $( cut -f2 -d'"' openmsp430.prj )
yosys -p "$yosys_cmds" -o or1200_ys.v $( cut -f2 -d'"' or1200.prj )

. /opt/Xilinx/14.5/ISE_DS/settings64.sh

run_single() {
	prj_file=$1 top_module=$2 out_file=$3
	sed "s/@prj_file@/$prj_file/g; s/@out_file@/$out_file/g; s/@top_module@/$top_module/g;" < settings.xst > ${out_file}.xst
	xst -ifn ${out_file}.xst -ofn ${out_file}.syr
}

for mod in $openmsp430_mods; do
	run_single openmsp430.prj ${mod} ${mod}
	run_single openmsp430_ys.prj ${mod} ${mod}_ys
done

for mod in $or1200_mods; do
	run_single or1200.prj ${mod} ${mod}
	run_single or1200_ys.prj ${mod} ${mod}_ys
done

