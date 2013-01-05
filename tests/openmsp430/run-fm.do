
set hdlin_ignore_full_case false
set hdlin_ignore_parallel_case false
set svf_ignore_unqualified_fsm_information true
set hdlin_warn_on_mismatch_message "FMR_ELAB-115 FMR_VLOG-079 FMR_VLOG-091"

read_verilog -container r -libname WORK -01 rtl/omsp_alu.v
read_verilog -container r -libname WORK -01 rtl/omsp_and_gate.v
read_verilog -container r -libname WORK -01 rtl/omsp_clock_gate.v
read_verilog -container r -libname WORK -01 rtl/omsp_clock_module.v
read_verilog -container r -libname WORK -01 rtl/omsp_clock_mux.v
read_verilog -container r -libname WORK -01 rtl/omsp_dbg_hwbrk.v
read_verilog -container r -libname WORK -01 rtl/omsp_dbg_uart.v
read_verilog -container r -libname WORK -01 rtl/omsp_dbg.v
read_verilog -container r -libname WORK -01 rtl/omsp_execution_unit.v
read_verilog -container r -libname WORK -01 rtl/omsp_frontend.v
read_verilog -container r -libname WORK -01 rtl/omsp_mem_backbone.v
read_verilog -container r -libname WORK -01 rtl/omsp_multiplier.v
read_verilog -container r -libname WORK -01 rtl/omsp_register_file.v
read_verilog -container r -libname WORK -01 rtl/omsp_scan_mux.v
read_verilog -container r -libname WORK -01 rtl/omsp_sfr.v
read_verilog -container r -libname WORK -01 rtl/omsp_sync_cell.v
read_verilog -container r -libname WORK -01 rtl/omsp_sync_reset.v
read_verilog -container r -libname WORK -01 rtl/omsp_wakeup_cell.v
read_verilog -container r -libname WORK -01 rtl/omsp_watchdog.v
read_verilog -container r -libname WORK -01 rtl/openMSP430.v
set_top r:/WORK/openMSP430

read_verilog -container i -libname WORK -01 synth.v
read_verilog -container i -technology_library -libname TECH_WORK -01 ../../techlibs/stdcells_sim.v
read_verilog -container i -technology_library -libname TECH_WORK -01 sim_mul.v
set_top i:/WORK/openMSP430

source fsm_info.txt

if ![verify] start_gui exit

