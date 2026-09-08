#!/usr/bin/env python3
"""Check M10K 20-bit lane enables and prove their mapped write semantics."""
import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yosys', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).with_name('top.v').resolve()
    script = args.output.resolve() / 'test.ys'
    script.write_text(f"""
read_verilog {source}
proc
memory -nomap
equiv_opt -run :prove -map +/intel_alm/common/alm_sim.v -map +/intel_alm/common/dff_sim.v -map +/intel_alm/common/mem_sim.v synth_intel_alm -family cyclonev -nolutram -nodsp -noiopad -noclkbuf
design -save compare
design -load postopt
select -assert-count 1 t:MISTRAL_M10K
select -assert-none t:MISTRAL_MLAB
write_json {args.output.resolve() / 'mapped.json'}
design -load compare
memory
opt -full
clk2fflogic
opt -full
miter -equiv -flatten -make_assert -make_outputs gold gate miter
opt -full
sat -verify -prove-asserts -seq 12 -set-init-zero -set in_wr_addr 1 -set in_rd_addr 1 -show-inputs -show-outputs miter
""")
    with (args.output / 'test.log').open('w') as log:
        subprocess.run([str(args.yosys.resolve()), '-Q', '-T', '-s', str(script)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    design = json.loads((args.output / 'mapped.json').read_text())
    module = design['modules']['top']
    ram = next(cell for cell in module['cells'].values() if cell['type'] == 'MISTRAL_M10K')
    assert int(ram['parameters']['CFG_ABITS'], 2) == 9
    assert int(ram['parameters']['CFG_DBITS'], 2) == 20
    assert int(ram['parameters']['CFG_DUAL_CLOCK'], 2) == 1
    assert int(ram['parameters']['CFG_BYTE_ENABLE'], 2) == 1
    assert len(ram['connections']['A1BE']) == 2
    assert len(ram['connections']['A1EN']) == 1
    assert ram['connections']['A1BE'][0] != ram['connections']['A1BE'][1]
    assert ram['connections']['CLK1'] != ram['connections']['CLK2']
    print('PASS: one 512x20 M10K, CFG_BYTE_ENABLE, two A1BE lanes, independent clocks')
    print('PASS: 12-step SAT equivalence covers both lane masks, write enable, read enable and initialization')


if __name__ == '__main__':
    main()
