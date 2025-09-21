from pathlib import Path
from pyosys import libyosys as ys


__file_dir__ = Path(__file__).absolute().parent
add_sub = __file_dir__.parent / "arch" / "common" / "add_sub.v"

base = ys.Design()
ys.run_pass(f"read_verilog {add_sub}", base)
ys.run_pass("hierarchy -top top", base)
ys.run_pass("proc", base)
ys.run_pass("equiv_opt -assert -map +/ecp5/cells_sim.v synth_ecp5", base)

postopt = ys.Design()
ys.run_pass("design -load postopt", postopt)
ys.run_pass("cd top", postopt)
ys.run_pass("select -assert-min 25 t:LUT4", postopt)
ys.run_pass("select -assert-max 26 t:LUT4", postopt)
ys.run_pass("select -assert-count 10 t:PFUMX", postopt)
ys.run_pass("select -assert-count 6 t:L6MUX21", postopt)
ys.run_pass("select -assert-none t:LUT4 t:PFUMX t:L6MUX21 %% t:* %D", postopt)
