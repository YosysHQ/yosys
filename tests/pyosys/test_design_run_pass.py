from pathlib import Path
from pyosys import libyosys as ys

__file_dir__ = Path(__file__).absolute().parent
add_sub = __file_dir__.parent / "arch" / "common" / "add_sub.v"

base = ys.Design()
base.run_pass(["read_verilog", str(add_sub)])
base.run_pass("hierarchy -top top")
base.run_pass(["proc"])
base.run_pass("equiv_opt -assert -map +/ecp5/cells_sim.v synth_ecp5")

postopt = ys.Design()
postopt.run_pass("design -load postopt")
postopt.run_pass(["cd", "top"])
postopt.run_pass("select -assert-min 25 t:LUT4")
postopt.run_pass("select -assert-max 26 t:LUT4")
postopt.run_pass(["select", "-assert-count", "10", "t:PFUMX"])
postopt.run_pass(["select", "-assert-count", "6", "t:L6MUX21"])
postopt.run_pass("select -assert-none t:LUT4 t:PFUMX t:L6MUX21 %% t:* %D")
