
set hdlin_ignore_full_case false
set hdlin_warn_on_mismatch_message "FMR_ELAB-115 FMR_VLOG-079 FMR_VLOG-091"

read_verilog -container r -libname WORK -01 rtl/or1200_alu.v
read_verilog -container r -libname WORK -01 rtl/or1200_amultp2_32x32.v
read_verilog -container r -libname WORK -01 rtl/or1200_cfgr.v
read_verilog -container r -libname WORK -01 rtl/or1200_cpu.v
read_verilog -container r -libname WORK -01 rtl/or1200_ctrl.v
read_verilog -container r -libname WORK -01 rtl/or1200_dc_fsm.v
read_verilog -container r -libname WORK -01 rtl/or1200_dc_ram.v
read_verilog -container r -libname WORK -01 rtl/or1200_dc_tag.v
read_verilog -container r -libname WORK -01 rtl/or1200_dc_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_dmmu_tlb.v
read_verilog -container r -libname WORK -01 rtl/or1200_dmmu_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_dpram.v
read_verilog -container r -libname WORK -01 rtl/or1200_du.v
read_verilog -container r -libname WORK -01 rtl/or1200_except.v
read_verilog -container r -libname WORK -01 rtl/or1200_fpu.v
read_verilog -container r -libname WORK -01 rtl/or1200_freeze.v
read_verilog -container r -libname WORK -01 rtl/or1200_genpc.v
read_verilog -container r -libname WORK -01 rtl/or1200_ic_fsm.v
read_verilog -container r -libname WORK -01 rtl/or1200_ic_ram.v
read_verilog -container r -libname WORK -01 rtl/or1200_ic_tag.v
read_verilog -container r -libname WORK -01 rtl/or1200_ic_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_if.v
read_verilog -container r -libname WORK -01 rtl/or1200_immu_tlb.v
read_verilog -container r -libname WORK -01 rtl/or1200_immu_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_lsu.v
read_verilog -container r -libname WORK -01 rtl/or1200_mem2reg.v
read_verilog -container r -libname WORK -01 rtl/or1200_mult_mac.v
read_verilog -container r -libname WORK -01 rtl/or1200_operandmuxes.v
read_verilog -container r -libname WORK -01 rtl/or1200_pic.v
read_verilog -container r -libname WORK -01 rtl/or1200_pm.v
read_verilog -container r -libname WORK -01 rtl/or1200_qmem_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_reg2mem.v
read_verilog -container r -libname WORK -01 rtl/or1200_rf.v
read_verilog -container r -libname WORK -01 rtl/or1200_sb.v
read_verilog -container r -libname WORK -01 rtl/or1200_spram_32_bw.v
read_verilog -container r -libname WORK -01 rtl/or1200_spram.v
read_verilog -container r -libname WORK -01 rtl/or1200_sprs.v
read_verilog -container r -libname WORK -01 rtl/or1200_top.v
read_verilog -container r -libname WORK -01 rtl/or1200_tt.v
read_verilog -container r -libname WORK -01 rtl/or1200_wb_biu.v
read_verilog -container r -libname WORK -01 rtl/or1200_wbmux.v
set_top r:/WORK/or1200_top

read_verilog -container i -libname WORK -01 synth.v
read_verilog -container i -technology_library -libname TECH_WORK -01 ../../techlibs/stdcells_sim.v
set_top i:/WORK/or1200_top

if ![verify] start_gui exit

