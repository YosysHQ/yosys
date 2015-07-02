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

grep_regs() {
	x=$(grep '^ Number of Slice Registers:' $1.syr | sed 's/.*: *//;' | cut -f1 -d' ')
	echo $x | sed 's,^ *$,-1,'
}

grep_luts() {
	x=$(grep '^ Number of Slice LUTs:' $1.syr | sed 's/.*: *//;' | cut -f1 -d' ')
	echo $x | sed 's,^ *$,-1,'
}

grep_freq() {
	x=$(grep 'Minimum period.*Maximum Frequency' $1.syr | sed 's/\.[0-9]*MHz.*//;' | cut -f3 -d:)
	echo $x | sed 's,^ *$,-1,'
}

for mod in $openmsp430_mods $or1200_mods; do
	printf '%-30s s,$, \\& %6d \\& %6d \\& %4d MHz \\& %6d \\& %6d \\& %4d MHz \\\\\\\\,;\n' "/${mod//_/\\\\_}}/" \
			$(grep_regs ${mod}) $(grep_luts ${mod}) $(grep_freq ${mod}) \
			$(grep_regs ${mod}_ys) $(grep_luts ${mod}_ys) $(grep_freq ${mod}_ys)
done

# for mod in $openmsp430_mods $or1200_mods; do
# 	[ $mod = "or1200_top" -o $mod = "or1200_dmmu_top" -o $mod = or1200_dmmu_tlb -o $mod = or1200_immu_tlb ] && continue
# 	regs=$(grep_regs ${mod}) regs_ys=$(grep_regs ${mod}_ys)
# 	luts=$(grep_luts ${mod}) luts_ys=$(grep_luts ${mod}_ys)
# 	freq=$(grep_freq ${mod}) freq_ys=$(grep_freq ${mod}_ys)
# 	if [ $regs -gt 0 -a $regs_ys -gt 0 ]; then regs_p=$(( 100*regs_ys / regs )); else regs_p=NaN; fi
# 	if [ $luts -gt 0 -a $luts_ys -gt 0 ]; then luts_p=$(( 100*luts_ys / luts )); else luts_p=NaN; fi
# 	if [ $freq -gt 0 -a $freq_ys -gt 0 ]; then freq_p=$(( 100*freq_ys / freq )); else freq_p=NaN; fi
# 	printf '%-30s %3s %3s %3s\n' $mod $regs_p $luts_p $freq_p
#
# done

