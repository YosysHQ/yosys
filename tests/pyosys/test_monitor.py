from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

d = ys.Design()

class Monitor(ys.Monitor):
	def __init__(self):
		super().__init__()
		self.mods = []

	def notify_module_add(self, mod):
		self.mods.append(mod.name.str())

m = Monitor()
d.monitors.add(m)

ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
ys.run_pass("hierarchy -top spm", d)

assert m.mods == ["\\spm"]
