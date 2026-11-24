import os
import shutil
import subprocess

import pytest

pytestmark = pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not available")

BODIES = {
    # mem[0] does not exist and reads 0 (#2465)
    "nonpow2_oob_read": "reg [3:0] mem [1:3]; always @* assert(mem[0] == 0);",
    # mem[2] keeps its init
    "init_start_offset": "reg [3:0] mem [2:5]; initial mem[2] = 1; always @* assert(mem[2] == 1);",
}


@pytest.mark.parametrize("body", BODIES.values(), ids=BODIES.keys())
def test_memory_index(tmp_path, body):
    vfile = tmp_path / "design.v"
    smt2 = tmp_path / "design.smt2"
    vfile.write_text(f"module top; {body} endmodule\n")
    yosys = os.environ.get("YOSYS", "../../yosys")
    smtbmc = os.environ.get("YOSYS_SMTBMC", "../../yosys-smtbmc")
    script = f"read_verilog -formal {vfile}; prep -top top; async2sync; write_smt2 {smt2}"
    subprocess.run([yosys, "-Q", "-p", script], check=True)
    result = subprocess.run([smtbmc, "-s", "z3", "-t", "1", smt2], capture_output=True, text=True)
    assert result.returncode == 0, result.stdout
