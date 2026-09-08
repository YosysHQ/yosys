#!/usr/bin/env python3
"""Check opt-in M10K TDP inference, canonical INIT and bounded dual-clock behavior."""
import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yosys', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--case', action='append', help='Run only this named case (repeatable)')
    args = parser.parse_args()
    source = Path(__file__).with_name('top.v').resolve()
    cases = [(f'w{width}', width, 0, 0) for width in (8, 10, 16, 20)]
    cases += [('w20-constant', 20, 1, 0), ('w20-same-clock', 20, 0, 1)]
    for name, width, constant, same_clock in cases:
        if args.case and name not in args.case:
            continue
        physical = 10 if width <= 10 else 20
        abits = 10 if width <= 10 else 9
        for page in (0, (1 << (abits - 2)) - 1):
            out = args.output.resolve() / name / f'page{page}'
            out.mkdir(parents=True, exist_ok=True)
            # Check inference at full depth, then restrict both designs to four
            # words before expanding memory. This keeps the SAT problem bounded
            # without constraining the low address bits, clocks, enables or data.
            restrict = '\n'.join(
                f'connect -set {port}[{abits-1}:2] {page} {design}'
                for design in ('gold', 'gate') for port in ('aa', 'ba'))
            script = out / 'test.ys'
            script.write_text(f'''
read_verilog -formal {source}
chparam -set WIDTH {width} -set CONST_DATA {constant} -set SAME_CLOCK {same_clock} top
proc
opt -nodffe -nosdff
memory -nomap -nordff
equiv_opt -run :prove -map +/intel_alm/common/alm_sim.v -map +/intel_alm/common/dff_sim.v -map +/intel_alm/common/mem_sim.v synth_intel_alm -nolutram -nodsp -noiopad -noclkbuf
design -save compare
design -load postopt
select -assert-count 1 t:MISTRAL_M10K_TDP
select -assert-none t:MISTRAL_M10K t:MISTRAL_MLAB t:$mem_v2
write_json {out/'mapped.json'}
design -load compare
{restrict}
opt -full
memory -nordff
opt -full
clk2fflogic
memory_map -formal
opt -full
miter -equiv -flatten -make_assert -make_outputs gold gate miter
opt -full
sat -verify -prove-asserts -set-assumes -seq 12 -set-init-zero miter
''')
            with (out / 'test.log').open('w') as log:
                subprocess.run([str(args.yosys.resolve()), '-Q', '-T', '-s', str(script)],
                               stdout=log, stderr=subprocess.STDOUT, check=True)
            design = json.loads((out / 'mapped.json').read_text())
            ram = next(c for c in design['modules']['top']['cells'].values()
                       if c['type'] == 'MISTRAL_M10K_TDP')
            assert int(ram['parameters']['CFG_ABITS'], 2) == abits
            assert int(ram['parameters']['CFG_DBITS'], 2) == physical
            assert len(ram['connections']['A1DATA']) == physical
            assert len(ram['connections']['B1DATA']) == physical
            assert (ram['connections']['CLK1'] == ram['connections']['CLK2']) == bool(same_clock)
            init = ram['parameters']['INIT'][::-1]
            assert len(init) == 10240
            for addr in range(1 << abits):
                expected = ((addr * 73) ^ (addr >> 1) ^ 0xa6) & ((1 << width) - 1)
                payload = init[addr * physical:addr * physical + width][::-1]
                assert int(payload, 2) == expected, (name, addr, payload, expected)
            print(f'PASS: {name} page {page}: one TDP, canonical INIT, 12-step SAT equivalence', flush=True)


if __name__ == '__main__':
    main()
