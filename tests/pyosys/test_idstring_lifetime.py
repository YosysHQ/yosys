
from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

external_idstring_holder = None

def get_top_module_idstring():
	global external_idstring_holder
	d = ys.Design()
	ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
	ys.run_pass("hierarchy -top spm", d)
	external_idstring_holder = d.top_module().name
	# d deallocates

get_top_module_idstring()
print(external_idstring_holder) # <- segfault unless idstring is properly copied
