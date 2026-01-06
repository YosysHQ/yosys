
from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

d = ys.Design()
ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
ys.run_pass("hierarchy -top spm", d)

external_idstring_holder_0 = None
external_idstring_holder_1 = None

def get_top_module_idstring():
	global external_idstring_holder_0, external_idstring_holder_1
	d = ys.Design()
	ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
	ys.run_pass("hierarchy -top spm", d)
	external_idstring_holder_0 = d.top_module().name
	for cell in d.top_module().cells_:
		print(f"TARGETED: {cell}", flush=True)
		external_idstring_holder_1 = cell
		break
	# d deallocates

get_top_module_idstring()
print(external_idstring_holder_0, flush=True)
print(external_idstring_holder_1, flush=True)
