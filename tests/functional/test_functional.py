import subprocess
import pytest
import sys
import shlex
from pathlib import Path

base_path = Path(__file__).resolve().parent.parent.parent

def quote(path):
    return shlex.quote(str(path))

def run(cmd, **kwargs):
    print(' '.join([shlex.quote(str(x)) for x in cmd]))
    status = subprocess.run(cmd, **kwargs)
    assert status.returncode == 0, f"{cmd[0]} failed"

def yosys(script):
    run([base_path / 'yosys', '-Q', '-p', script])

def compile_cpp(in_path, out_path, args):
    run(['g++', '-g', '-std=c++17'] + args + [str(in_path), '-o', str(out_path)])

def test_cxx(cell, parameters, tmp_path):
    rtlil_file = tmp_path / 'rtlil.il'
    vcdharness_cc_file = base_path / 'tests/functional/vcd_harness.cc'
    cc_file = tmp_path / 'my_module_functional_cxx.cc'
    vcdharness_exe_file = tmp_path / 'a.out'
    vcd_functional_file = tmp_path / 'functional.vcd'
    vcd_yosys_sim_file = tmp_path / 'yosys.vcd'

    with open(rtlil_file, 'w') as f:
        cell.write_rtlil_file(f, parameters)
    yosys(f"read_rtlil {quote(rtlil_file)} ; write_functional_cxx {quote(cc_file)}")
    compile_cpp(vcdharness_cc_file, vcdharness_exe_file, ['-I', tmp_path, '-I', str(base_path / 'backends/functional/cxx_runtime')])
    run([str(vcdharness_exe_file.resolve()), str(vcd_functional_file)])
    try:
        yosys(f"read_rtlil {quote(rtlil_file)}; sim -r {quote(vcd_functional_file)} -scope gold -vcd {quote(vcd_yosys_sim_file)} -timescale 1us -sim-gold")
    except:
        subprocess.run([base_path / 'yosys', '-Q', '-p',
            f'read_rtlil {quote(rtlil_file)}; sim -vcd {quote(vcd_yosys_sim_file)} -r {quote(vcd_functional_file)} -scope gold -timescale 1us'],
            capture_output=True, check=False)
        raise

def test_smt(cell, parameters, tmp_path):
    import smt_vcd

    rtlil_file = tmp_path / 'rtlil.il'
    smt_file = tmp_path / 'smtlib.smt'
    vcd_functional_file = tmp_path / 'functional.vcd'
    vcd_yosys_sim_file = tmp_path / 'yosys.vcd'

    with open(rtlil_file, 'w') as f:
        cell.write_rtlil_file(f, parameters)
    yosys(f"read_rtlil {quote(rtlil_file)} ; write_functional_smt2 {quote(smt_file)}")
    run(['z3', smt_file])
    smt_vcd.simulate_smt(smt_file, vcd_functional_file)
    try:
        yosys(f"read_rtlil {quote(rtlil_file)}; sim -r {quote(vcd_functional_file)} -scope gold -vcd {quote(vcd_yosys_sim_file)} -timescale 1us -sim-gold")
    except:
        subprocess.run([base_path / 'yosys', '-Q', '-p',
            f'read_rtlil {quote(rtlil_file)}; sim -vcd {quote(vcd_yosys_sim_file)} -r {quote(vcd_functional_file)} -scope gold -timescale 1us'],
            capture_output=True, check=False)
        raise