#!/usr/bin/env python3
"""Check opt-in byte-masked M10K TDP inference, padded INIT and bounded behavior."""
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
    cases = [(f'w{width}', width, 0, 0) for width in (16, 20)]
    cases += [(f'w{width}-constant-mask', width, 1, 0) for width in (16, 20)]
    cases += [(f'w{width}-same-clock', width, 0, 1) for width in (16, 20)]
    for name, width, constant, same_clock in cases:
        if args.case and name not in args.case:
            continue
        # Exercise the public synthesis flow without equivalence preparation.
        direct = args.output.resolve() / name / 'direct'
        direct.mkdir(parents=True, exist_ok=True)
        direct_script = direct / 'test.ys'
        direct_script.write_text(f'''read_verilog {source}
chparam -set WIDTH {width} -set CONST_MASK {constant} -set SAME_CLOCK {same_clock} top
synth_intel_alm -top top -nolutram -nodsp -noiopad -noclkbuf
select -assert-count 1 t:MISTRAL_M10K_TDP
select -assert-none t:MISTRAL_M10K t:MISTRAL_MLAB t:$mem_v2
write_json {direct/'mapped.json'}
''')
        with (direct / 'test.log').open('w') as log:
            subprocess.run([str(args.yosys.resolve()), '-Q', '-T', '-s', str(direct_script)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        physical = 20
        abits = 9
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
chparam -set WIDTH {width} -set CONST_MASK {constant} -set SAME_CLOCK {same_clock} top
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
            assert int(ram['parameters']['CFG_BYTE_ENABLE'], 2) == 1
            assert len(ram['connections']['A1BE']) == 2
            assert len(ram['connections']['B1BE']) == 2
            assert len(ram['connections']['A1DATA']) == physical
            assert len(ram['connections']['B1DATA']) == physical
            assert (ram['connections']['CLK1'] == ram['connections']['CLK2']) == bool(same_clock)
            if width == 16:
                for port in ('A1DATA', 'B1DATA'):
                    assert all(ram['connections'][port][bit] in ('0', 'x') for bit in (8, 9, 18, 19))
            init = ram['parameters']['INIT'][::-1]
            assert len(init) == 10240
            for addr in range(1 << abits):
                expected = ((addr * 73) ^ (addr >> 1) ^ 0xa6) & ((1 << width) - 1)
                payload = ''.join(init[addr * physical + lane*10:addr * physical + lane*10 + width//2] for lane in range(2))[::-1]
                assert int(payload, 2) == expected, (name, addr, payload, expected)
                if width == 16:
                    assert all(init[addr*physical+bit] in ('0', 'x') for bit in (8, 9, 18, 19))
            print(f'PASS: {name} page {page}: one TDP, canonical INIT, 12-step SAT equivalence', flush=True)

    if not args.case or 'primitive' in args.case:
        out = args.output.resolve() / 'primitive'
        out.mkdir(parents=True, exist_ok=True)
        script = out / 'test.ys'
        script.write_text(f'''read_verilog -formal +/intel_alm/common/mem_sim.v {source.with_name('primitive.v')}
hierarchy -top primitive_check
proc
flatten
opt -full
memory -nordff
opt -full
clk2fflogic
memory_map -formal
opt -full
sat -verify -prove mismatch 0 -set-assumes -seq 12 -set-init-zero primitive_check
''')
        with (out / 'test.log').open('w') as log:
            subprocess.run([str(args.yosys.resolve()), '-Q', '-T', '-s', str(script)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        print('PASS: primitive: enabled-lane NEW_DATA, reads and holds, 12-step SAT', flush=True)


if __name__ == '__main__':
    main()
