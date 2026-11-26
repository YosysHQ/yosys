import os
import json
import shutil
import subprocess
from pathlib import Path

import pytest

base_path = Path(__file__).resolve().parent.parent.parent

pytestmark = pytest.mark.skipif(shutil.which("z3") is None, reason="z3 not available")

def run(cmd, **kwargs):
    """Run a command and assert it succeeds."""
    status = subprocess.run(cmd, **kwargs)
    assert status.returncode == 0, f"{cmd[0]} failed"
    return status


def write_smt2(tmp_path, verilog_text, read_options="", passes=("prep -top top",)):
    """Write Verilog to temp and emit SMT2 via yosys."""
    vfile = tmp_path / "design.v"
    smt2 = tmp_path / "design.smt2"
    vfile.write_text(verilog_text)
    run([os.environ.get("YOSYS", "../../yosys"), "-Q", "-p",
         f"read_verilog {read_options} {vfile}; {'; '.join(passes)}; write_smt2 {smt2}"])
    return smt2


def witness_entries(smt2_path):
    """Parse yosys-smt2-witness JSON records from an SMT2 file."""
    entries = []
    marker = "yosys-smt2-witness"
    with open(smt2_path, "r") as f:
        for line in f:
            if marker not in line:
                continue
            payload = line.split(marker, 1)[1].strip()
            entries.append(json.loads(payload))
    return entries


def find_entry(entries, entry_type):
    """Return the first witness entry of the given type."""
    for entry in entries:
        if entry.get("type") == entry_type:
            return entry
    return None


def write_yw(yw_path, signals, bits):
    """Write a minimal Yosys witness file with one step of bits."""
    data = {
        "format": "Yosys Witness Trace",
        "clocks": [],
        "signals": signals,
        "steps": [{"bits": bits}],
    }
    yw_path.write_text(json.dumps(data))


def run_smtbmc(smt2_path, yw_path):
    """Run yosys-smtbmc on the SMT2 file with a witness trace."""
    cmd = [
        os.environ.get("YOSYS_SMTBMC", "../../yosys-smtbmc"),
        "-s", "z3",
        "-m", "top",
        "--check-witness",
        "--yw", yw_path,
        "-t", "1",
        smt2_path,
    ]
    return subprocess.run(cmd, capture_output=True, text=True)


def run_smtbmc_induction(smt2_path, yw_path):
    """Run yosys-smtbmc on the SMT2 file with induction."""
    cmd = [
        os.environ.get("YOSYS_SMTBMC", "../../yosys-smtbmc"),
        "-s", "z3",
        "-m", "top",
        "-i",
        "--dump-yw", yw_path,
        "-t", "2",
        smt2_path,
    ]
    return subprocess.run(cmd, capture_output=True, text=True)


def assert_no_mismatch_message(result):
    """Assert the mismatch error prefix is absent from outputs."""
    combined = (result.stderr or "") + (result.stdout or "")
    assert "Yosys witness signal mismatch" not in combined


def assert_has_mismatch_message(result, msg):
    """Assert the mismatch error prefix and substring are present."""
    combined = (result.stderr or "") + (result.stdout or "")
    assert "Yosys witness signal mismatch" in combined
    assert msg in combined


def assert_smtbmc_status(result, status):
    """Assert the status of the smtbmc run, and rules out solver errors and tracebacks."""
    combined = (result.stderr or "") + (result.stdout or "")
    assert "Solver Error" not in combined
    assert "Traceback" not in combined
    assert f"Status: {status}" in combined


def test_missing_signal_path(tmp_path):
    smt2 = write_smt2(tmp_path, "module top(input ok, output out); assign out = ok; endmodule")
    yw_path = tmp_path / "trace.yw"
    signals = [{"path": ["\\missing"], "offset": 0, "width": 1, "init_only": False}]
    write_yw(yw_path, signals, "1")
    result = run_smtbmc(smt2, yw_path)
    assert result.returncode != 0
    assert_has_mismatch_message(result, "signal not found in design")


def test_width_mismatch(tmp_path):
    smt2 = write_smt2(tmp_path, "module top(input ok, output out); assign out = ok; endmodule")
    entries = witness_entries(smt2)
    input_entry = find_entry(entries, "input")
    assert input_entry is not None
    yw_path = tmp_path / "trace.yw"
    signals = [{
        "path": input_entry["path"],
        "offset": 0,
        "width": 2,
        "init_only": False,
    }]
    write_yw(yw_path, signals, "10")
    result = run_smtbmc(smt2, yw_path)
    assert result.returncode != 0
    assert_has_mismatch_message(result, "signal width/offset mismatch")


def test_memory_address_oob(tmp_path):
    verilog = """
module top(input ok, output [7:0] mem_out);
  reg [7:0] mem [0:1];
  assign mem_out = mem[0] ^ {8{ok}};
endmodule
"""
    smt2 = write_smt2(tmp_path, verilog)
    entries = witness_entries(smt2)
    mem_entry = find_entry(entries, "mem")
    assert mem_entry is not None
    addr = mem_entry["size"]
    yw_path = tmp_path / "trace.yw"
    signals = [{
        "path": mem_entry["path"] + [f"\\[{addr}]"],
        "offset": 0,
        "width": mem_entry["width"],
        "init_only": False,
    }]
    bits = "0" * mem_entry["width"]
    write_yw(yw_path, signals, bits)
    result = run_smtbmc(smt2, yw_path)
    assert result.returncode != 0
    assert_has_mismatch_message(result, "memory address out of bounds")


def test_allowed_extra_signal_in_design(tmp_path):
    verilog = """
module top(input ok, input extra, output [1:0] out);
  assign out = {ok, extra};
endmodule
"""
    smt2 = write_smt2(tmp_path, verilog)
    entries = witness_entries(smt2)
    input_entry = find_entry(entries, "input")
    assert input_entry is not None
    yw_path = tmp_path / "trace.yw"
    signals = [{
        "path": input_entry["path"],
        "offset": 0,
        "width": input_entry["width"],
        "init_only": False,
    }]
    bits = "0" * input_entry["width"]
    write_yw(yw_path, signals, bits)
    result = run_smtbmc(smt2, yw_path)
    # With --check-witness and no assertions, smtbmc can still exit non-zero.
    # Thus we don't check the result.returncode here and in the other success
    # cases.
    assert_no_mismatch_message(result)


def test_allowed_extra_memory_in_design(tmp_path):
    verilog = """
module top(input ok, output [7:0] out);
  reg [7:0] mem0 [0:1];
  reg [7:0] mem1 [0:3];
  assign out = mem0[0] ^ mem1[0];
endmodule
"""
    smt2 = write_smt2(tmp_path, verilog)
    entries = witness_entries(smt2)
    input_entry = find_entry(entries, "input")
    assert input_entry is not None
    yw_path = tmp_path / "trace.yw"
    signals = [{
        "path": input_entry["path"],
        "offset": 0,
        "width": input_entry["width"],
        "init_only": False,
    }]
    bits = "1" * input_entry["width"]
    write_yw(yw_path, signals, bits)
    result = run_smtbmc(smt2, yw_path)
    assert_no_mismatch_message(result)


BOOL_REG_DESIGN = """
module top(input clk, input in, input in2, output reg a);
  reg b = 1'b0, c = 1'b0;
  initial a = 1'b0;
  always @(posedge clk) begin
    b <= b & in2;
    c <= b;
    a <= in & c;
  end
  always @* assert(!a);
endmodule
"""


def test_bool_reg_witness_flag(tmp_path):
    smt2 = write_smt2(tmp_path,
                      BOOL_REG_DESIGN,
                      read_options="-formal",
                      passes=["prep -top top", "techmap", "async2sync"])
    entries = witness_entries(smt2)
    regs = [x for x in entries if x.get("type") == "reg"]
    assert sorted(x["path"] for x in regs) == [["\\a"], ["\\b"], ["\\c"]]
    assert all(x.get("smtbool") is True for x in regs)

    inputs = [x for x in entries if x.get("type") == "input"]
    assert sorted(x["path"] for x in inputs) == [["\\clk"], ["\\in"], ["\\in2"]]
    assert all(x.get("smtbool") is False for x in inputs)


def test_bool_reg_dump_yw(tmp_path):
    smt2 = write_smt2(tmp_path,
                      BOOL_REG_DESIGN,
                      read_options="-formal",
                      passes=["prep -top top", "techmap", "async2sync"])
    yw_path = tmp_path / "trace.yw"
    result = run_smtbmc_induction(smt2, yw_path)
    assert_smtbmc_status(result, "FAILED")

    yw_data = json.loads(yw_path.read_text())
    regs = [x for x in yw_data["signals"] if x.get("init_only") is True]
    assert sorted(x["path"] for x in regs) == [["\\a"], ["\\b"], ["\\c"]]

    inputs = [x for x in yw_data["signals"] if x.get("init_only") is False]
    assert sorted(x["path"] for x in inputs) == [["\\clk"], ["\\in"], ["\\in2"]]


def test_bool_reg_dump_yw_submodule(tmp_path):
    verilog = """
module sub(input clk, input in, input in2, output reg a);
  reg b = 1'b0, c = 1'b0;
  initial a = 1'b0;
  always @(posedge clk) begin
    b <= b & in2;
    c <= b;
    a <= in & c;
  end
endmodule
module top(input clk, input in, input in2, output a);
  sub u(.clk(clk), .in(in), .in2(in2), .a(a));
  always @* assert(!a);
endmodule
"""
    smt2 = write_smt2(tmp_path,
                      verilog,
                      read_options="-formal",
                      passes=["prep -top top", "techmap", "async2sync"])
    yw_path = tmp_path / "trace.yw"
    result = run_smtbmc_induction(smt2, yw_path)
    assert_smtbmc_status(result, "FAILED")

    yw_data = json.loads(yw_path.read_text())
    regs = [x for x in yw_data["signals"] if x.get("init_only") is True]
    assert sorted(x["path"] for x in regs) == [["\\u", "\\a"], ["\\u", "\\b"], ["\\u", "\\c"]]


def test_bool_reg_load_yw(tmp_path):
    verilog = """
module top(input clk, input in, output reg a);
  always @(posedge clk) begin
    a <= in;
  end
  always @* assert(!a);
endmodule
"""
    smt2 = write_smt2(tmp_path,
                      verilog,
                      read_options="-formal",
                      passes=["prep -top top", "techmap", "async2sync"])

    entries = witness_entries(smt2)
    regs = [x for x in entries if x.get("type") == "reg"]
    assert sorted(x["path"] for x in regs) == [["\\a"]]
    assert all(x.get("smtbool") is True for x in regs)

    yw_path = tmp_path / "trace.yw"
    signals = [{"path": ["\\a"], "offset": 0, "width": 1, "init_only": True}]
    write_yw(yw_path, signals, "1")
    result = run_smtbmc(smt2, yw_path)
    assert_smtbmc_status(result, "PASSED")
    assert_no_mismatch_message(result)
    assert result.returncode == 0
