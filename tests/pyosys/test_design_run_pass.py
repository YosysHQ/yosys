from pathlib import Path

from pyosys import libyosys as ys

__file_dir__ = Path(__file__).absolute().parent
src = __file_dir__.parent / "simple" / "fiedler-cooley.v"

design = ys.Design()
design.run_pass(["read_verilog", str(src)])
design.run_pass("hierarchy -top up3down5")
design.run_pass(["proc"])
design.run_pass("opt -full")
design.run_pass("select -assert-mod-count 1 up3down5")
