from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

def _dump_sigbit(bit):
    if bit.is_wire():
        if bit.wire.width == 1:
            return bit.wire.name.str()
        else:
            return f"{bit.wire.name} [{bit.offset}]"
    else:
        if bit.data == ys.State.S1:
            return 1
        elif bit.data == ys.State.S0:
            return 0
        else:
            assert "unknown constants not supported"

d = ys.Design()

ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
ys.run_pass(f"hierarchy -top spm", d)
module = d.module(r"\spm")
for conn_from, conn_to in module.connections_:
    for bit_from, bit_to in zip(conn_from, conn_to):
        print(f"assign {_dump_sigbit(bit_from)} = {_dump_sigbit(bit_to)};")

