#!/usr/bin/env python3
"""Infer mixed TDP M10K and prove both writers over first/last four-chunk windows."""
import argparse
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--yosys', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--case', action='append')
args = parser.parse_args()
source = Path(__file__).with_name('top.v').resolve()
cases = [(f'u{u}-a{a}-b{b}' + ('-shared' if shared else ''), u, a, b, shared)
         for u in (8, 10) for a, b in ((2, 1), (1, 2)) for shared in (0, 1)]
cases += [('equal10', 10, 1, 1, 0), ('equal20', 10, 2, 2, 1)]
if args.case:
    unknown = set(args.case) - {case[0] for case in cases}
    if unknown:
        parser.error(f'unknown cases: {sorted(unknown)}')

def run(script, text):
    script.parent.mkdir(parents=True, exist_ok=True)
    script.write_text(text)
    with script.with_suffix('.log').open('w') as log:
        subprocess.run([str(args.yosys.resolve()), '-Q', '-T', '-s', str(script)],
                       stdout=log, stderr=subprocess.STDOUT, check=True)


def check_json(path, unit, alanes, blanes, shared):
    top = json.loads(path.read_text())['modules']['top']
    cells = [c for c in top['cells'].values() if c['type'] == 'MISTRAL_M10K_TDP']
    assert len(cells) == 1
    ram = cells[0]
    params = {k: int(v, 2) for k, v in ram['parameters'].items() if k != 'INIT'}
    assert params['CFG_MIXED_WIDTH'] == 1
    assert params.get('CFG_BYTE_ENABLE', 0) == 0
    widths = [params['CFG_DBITS'], params['CFG_RD_DBITS']]
    assert sorted(widths) == sorted([alanes*10, blanes*10])
    for width, abits, data, addr, q in zip(widths,
            [params['CFG_ABITS'], params['CFG_RD_ABITS']],
            ['A1DATA', 'B1DATA'], ['A1ADDR', 'B1ADDR'], ['A1Q', 'B1Q']):
        assert width * (1 << abits) == 10240
        assert len(ram['connections'][data]) == len(ram['connections'][q]) == width
        assert len(ram['connections'][addr]) == abits
    assert (ram['connections']['CLK1'] == ram['connections']['CLK2']) == bool(shared)
    if not shared:
        # Libmap can exchange the physical ports; identify them by clock.
        for clk, width in zip(['CLK1', 'CLK2'], widths):
            assert ram['connections'][clk] in (top['ports']['ac']['bits'], top['ports']['bc']['bits'])
            expected = alanes if ram['connections'][clk] == top['ports']['ac']['bits'] else blanes
            assert width == expected*10
    init = ram['parameters']['INIT'][::-1]
    assert len(init) == 10240
    for chunk in range(1024):
        expected = ((chunk*73) ^ (chunk >> 1) ^ 0xa6) & ((1 << unit)-1)
        assert int(init[chunk*10:chunk*10+unit][::-1], 2) == expected


for name, unit, alanes, blanes, shared in cases:
    if args.case and name not in args.case:
        continue
    out = args.output.resolve() / name
    parameters = f'chparam -set UNIT {unit} -set ALANES {alanes} -set BLANES {blanes} -set SAME_CLOCK {shared} top'
    assertions = 'select -assert-count 1 t:MISTRAL_M10K_TDP\nselect -assert-none t:MISTRAL_M10K t:MISTRAL_MLAB t:$mem_v2'
    run(out/'direct/test.ys', f'''read_verilog {source}
{parameters}
synth_intel_alm -top top -nolutram -nodsp -noiopad -noclkbuf
{assertions}
write_json {out/'direct/mapped.json'}
''')
    check_json(out/'direct/mapped.json', unit, alanes, blanes, shared)
    for page in (0, 255):
        proof = out/f'page{page}'
        # Restrict both ports to the SAME four 10-bit physical chunks, including
        # both narrow lanes of each wide word; preserve low lane address bits.
        restrict = '\n'.join(
            f'connect -set {port}[{9-(lanes.bit_length()-1)}:{2-(lanes.bit_length()-1)}] {page} {design}'
            for design in ('gold', 'gate') for port, lanes in [('aa', alanes), ('ba', blanes)])
        run(proof/'test.ys', f'''read_verilog -formal {source}
{parameters}
proc
opt -nodffe -nosdff
equiv_opt -run :prove -map +/intel_alm/common/alm_sim.v -map +/intel_alm/common/dff_sim.v -map +/intel_alm/common/mem_sim.v synth_intel_alm -nolutram -nodsp -noiopad -noclkbuf
design -save compare
design -load postopt
{assertions}
write_json {proof/'mapped.json'}
design -load compare
{restrict}
opt -full
memory -nordff
opt -full
memory_narrow
clk2fflogic
memory_map -formal
opt -full
miter -equiv -flatten -make_assert -make_outputs gold gate miter
opt -full
sat -verify -prove-asserts -set-assumes -seq 12 -set-init-zero miter
''')
        check_json(proof/'mapped.json', unit, alanes, blanes, shared)
        print(f'PASS: {name} page {page}: one mixed TDP, INIT, 12-step SAT', flush=True)
