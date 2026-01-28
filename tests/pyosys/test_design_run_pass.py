from pathlib import Path

from pyosys import libyosys as ys

__file_dir__ = Path(__file__).absolute().parent

design = ys.Design()
design.run_pass(
	["read_verilog", str(__file_dir__.parent / "simple" / "fiedler-cooley.v")]
)
design.run_pass("prep")
design.run_pass(["opt", "-full"])
