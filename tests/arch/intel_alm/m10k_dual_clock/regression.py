#!/usr/bin/env python3
"""Check M10K inference and bounded equivalence with independently driven clocks."""
import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--yosys", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).with_name("top.v").resolve()
    for width in (20, 40):
        output = args.output.resolve() / f"width{width}"
        output.mkdir(exist_ok=True)
        script = output / "test.ys"
        script.write_text(f"""
read_verilog {source}
chparam -set WIDTH {width} top
hierarchy -top top
proc
memory -nomap
equiv_opt -run :prove -map +/intel_alm/common/alm_sim.v -map +/intel_alm/common/dff_sim.v -map +/intel_alm/common/mem_sim.v synth_intel_alm -family cyclonev -nolutram -nodsp -noiopad -noclkbuf
design -save compare
design -load postopt
select -assert-count 1 t:MISTRAL_M10K
select -assert-none t:MISTRAL_MLAB
write_json {output / 'mapped.json'}
design -load compare
memory
opt -full
clk2fflogic
opt -full
miter -equiv -flatten -make_assert -make_outputs gold gate miter
opt -full
sat -verify -prove-asserts -seq 12 -set-init-zero -set in_wr_addr 1 -set in_rd_addr 1 -show-inputs -show-outputs miter
""")
        with (output / "test.log").open("w") as log:
            subprocess.run([str(args.yosys.resolve()), "-Q", "-T", "-s", str(script)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        design = json.loads((output / "mapped.json").read_text())
        module = design["modules"]["top"]
        ram = next(cell for cell in module["cells"].values() if cell["type"] == "MISTRAL_M10K")
        assert int(ram["parameters"]["CFG_DUAL_CLOCK"], 2) == 1
        assert ram["connections"]["CLK1"] == module["ports"]["wr_clk"]["bits"]
        assert ram["connections"]["CLK2"] == module["ports"]["rd_clk"]["bits"]
        assert ram["connections"]["CLK1"] != ram["connections"]["CLK2"]
        assert int(ram["parameters"]["CFG_DBITS"], 2) == width
        init = ram["parameters"]["INIT"]
        for address in range(64):
            high = len(init) - address * width
            assert int(init[high-width:high], 2) == ((address * 73) ^ 166) & ((1 << width) - 1)
        print(f"PASS width={width}: one M10K, INIT, independent clocks, 12-step address-1 equivalence")
        legacy_script = output / "legacy.ys"
        legacy_script.write_text(f"""
read_verilog -formal {source} {source.with_name('legacy.v')} +/intel_alm/common/mem_sim.v
chparam -set WIDTH {width} legacy
hierarchy -top legacy
proc
flatten
memory
opt -full
clk2fflogic
opt -full
sat -verify -prove-asserts -seq 12 -set-init-zero -show-inputs legacy
""")
        with (output / "legacy.log").open("w") as log:
            subprocess.run([str(args.yosys.resolve()), "-Q", "-T", "-s", str(legacy_script)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        print(f"PASS width={width}: legacy default reads CLK1, 12-step equivalence")


if __name__ == "__main__":
    main()
