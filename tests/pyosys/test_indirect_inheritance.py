
from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent


d = ys.Design()
ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
ys.run_pass("hierarchy -top spm", d)

for idstr, cell in d.top_module().cells_.items():
    cell.set_bool_attribute("\\set")
    print(cell.attributes)
    break
