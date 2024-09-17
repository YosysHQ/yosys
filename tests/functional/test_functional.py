import subprocess
import pytest
import sys
import shlex
from pathlib import Path

base_path = Path(__file__).resolve().parent.parent.parent

# quote a string or pathlib path so that it can be used by bash or yosys
# TODO: is this really appropriate for yosys?
def quote(path):
    return shlex.quote(str(path))

# run a shell command and require the return code to be 0
def run(cmd, **kwargs):
    print(' '.join([quote(x) for x in cmd]))
    status = subprocess.run(cmd, **kwargs)
    assert status.returncode == 0, f"{cmd[0]} failed"

def yosys(script):
    run([base_path / 'yosys', '-Q', '-p', script])

def compile_cpp(in_path, out_path, args):
    run(['g++', '-g', '-std=c++17'] + args + [str(in_path), '-o', str(out_path)])

def yosys_synth(verilog_file, rtlil_file):
    yosys(f"read_verilog {quote(verilog_file)} ; prep ; write_rtlil {quote(rtlil_file)}")

# simulate an rtlil file with yosys, comparing with a given vcd file, and writing out the yosys simulation results into a second vcd file
def yosys_sim(rtlil_file, vcd_reference_file, vcd_out_file, preprocessing = ""):
    try:
        yosys(f"read_rtlil {quote(rtlil_file)}; {preprocessing}; sim -r {quote(vcd_reference_file)} -scope gold -vcd {quote(vcd_out_file)} -timescale 1us -sim-gold -fst-noinit")
    except:
        # if yosys sim fails it's probably because of a simulation mismatch
        # since yosys sim aborts on simulation mismatch to generate vcd output
        # we have to re-run with a different set of flags
        # on this run we ignore output and return code, we just want a best-effort attempt to get a vcd
        subprocess.run([base_path / 'yosys', '-Q', '-p',
            f'read_rtlil {quote(rtlil_file)}; sim -vcd {quote(vcd_out_file)} -a -r {quote(vcd_reference_file)} -scope gold -timescale 1us -fst-noinit'],
            capture_output=True, check=False)
        raise

def test_cxx(cell, parameters, tmp_path, num_steps, rnd):
    rtlil_file = tmp_path / 'rtlil.il'
    vcdharness_cc_file = base_path / 'tests/functional/vcd_harness.cc'
    cc_file = tmp_path / 'my_module_functional_cxx.cc'
    vcdharness_exe_file = tmp_path / 'a.out'
    vcd_functional_file = tmp_path / 'functional.vcd'
    vcd_yosys_sim_file = tmp_path / 'yosys.vcd'

    cell.write_rtlil_file(rtlil_file, parameters)
    yosys(f"read_rtlil {quote(rtlil_file)} ; clk2fflogic ; write_functional_cxx {quote(cc_file)}")
    compile_cpp(vcdharness_cc_file, vcdharness_exe_file, ['-I', tmp_path, '-I', str(base_path / 'backends/functional/cxx_runtime')])
    seed = str(rnd(cell.name + "-cxx").getrandbits(32))
    run([str(vcdharness_exe_file.resolve()), str(vcd_functional_file), str(num_steps), str(seed)])
    yosys_sim(rtlil_file, vcd_functional_file, vcd_yosys_sim_file, getattr(cell, 'sim_preprocessing', ''))

@pytest.mark.smt
def test_smt(cell, parameters, tmp_path, num_steps, rnd):
    import smt_vcd

    rtlil_file = tmp_path / 'rtlil.il'
    smt_file = tmp_path / 'smtlib.smt'
    vcd_functional_file = tmp_path / 'functional.vcd'
    vcd_yosys_sim_file = tmp_path / 'yosys.vcd'

    if hasattr(cell, 'smt_max_steps'):
        num_steps = min(num_steps, cell.smt_max_steps)

    cell.write_rtlil_file(rtlil_file, parameters)
    yosys(f"read_rtlil {quote(rtlil_file)} ; clk2fflogic ; write_functional_smt2 {quote(smt_file)}")
    run(['z3', smt_file]) # check if output is valid smtlib before continuing
    smt_vcd.simulate_smt(smt_file, vcd_functional_file, num_steps, rnd(cell.name + "-smt"))
    yosys_sim(rtlil_file, vcd_functional_file, vcd_yosys_sim_file, getattr(cell, 'sim_preprocessing', ''))

@pytest.mark.rkt
def test_rkt(cell, parameters, tmp_path, num_steps, rnd):
    import rkt_vcd

    rtlil_file = tmp_path / 'rtlil.il'
    rkt_file = tmp_path / 'smtlib.rkt'
    vcd_functional_file = tmp_path / 'functional.vcd'
    vcd_yosys_sim_file = tmp_path / 'yosys.vcd'

    cell.write_rtlil_file(rtlil_file, parameters)
    yosys(f"read_rtlil {quote(rtlil_file)} ; clk2fflogic ; write_functional_rosette -provides {quote(rkt_file)}")
    rkt_vcd.simulate_rosette(rkt_file, vcd_functional_file, num_steps, rnd(cell.name + "-rkt"))
    yosys_sim(rtlil_file, vcd_functional_file, vcd_yosys_sim_file, getattr(cell, 'sim_preprocessing', ''))

def test_print_graph(tmp_path):
    tb_file = base_path / 'tests/functional/picorv32_tb.v'
    cpu_file = base_path / 'tests/functional/picorv32.v'
    # currently we only check that we can print the graph without getting an error, not that it prints anything sensibl
    yosys(f"read_verilog {quote(tb_file)} {quote(cpu_file)}; prep -top gold; flatten; clk2fflogic; test_generic")
