#!/usr/bin/env python3
"""Prove mixed-width lane ordering and enabled writes/reads after intel_alm mapping."""
import argparse
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--yosys', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--case', action='append', help='Run only this uN-wN-rN case (repeatable)')
args = parser.parse_args()
source = Path(__file__).with_name('top.v').resolve()
for unit,w,r in ((10,4,1),(10,1,4),(10,2,1),(10,1,2),(10,4,2),(10,2,4),(8,4,1),(8,1,4),
                 (10,1,1),(10,2,2),(10,4,4),
                 (8,2,1),(8,1,2),(8,4,2),(8,2,4)):
    if args.case and f'u{unit}-w{w}-r{r}' not in args.case:
        continue
    out=args.output.resolve()/f'u{unit}-w{w}-r{r}'
    out.mkdir(parents=True,exist_ok=True)
    script=out/'test.ys'
    # Restrict addresses to one overlapping wide word but leave its narrow
    # lane address bits symbolic. Clocks, enables and write data are symbolic.
    wide=max(w,r)
    script.write_text(f'''
read_verilog {source}
chparam -set UNIT {unit} -set WLANES {w} -set RLANES {r} top
proc
opt
memory -nomap
equiv_opt -run :prove -map +/intel_alm/common/alm_sim.v -map +/intel_alm/common/dff_sim.v -map +/intel_alm/common/mem_sim.v synth_intel_alm -nolutram -nodsp -noiopad -noclkbuf
design -save compare
design -load postopt
select -assert-count 1 t:MISTRAL_M10K
write_json {out/'mapped.json'}
design -load compare
memory
opt -full
clk2fflogic
opt -full
miter -equiv -flatten -make_assert -make_outputs gold gate miter
opt -full
sat -verify -prove-asserts -seq 12 -set-init-zero -set in_wa[{9-(w.bit_length()-1)}:{(wide//w).bit_length()-1}] 0 -set in_ra[{9-(r.bit_length()-1)}:{(wide//r).bit_length()-1}] 0 miter
''')
    with (out/'test.log').open('w') as log:
        subprocess.run([str(args.yosys.resolve()),'-Q','-T','-s',str(script)],stdout=log,stderr=subprocess.STDOUT,check=True)
    d=json.loads((out/'mapped.json').read_text())
    c=next(c for c in d['modules']['top']['cells'].values() if c['type']=='MISTRAL_M10K')
    assert int(c['parameters']['CFG_DBITS'],2)==w*10
    assert int(c['parameters']['CFG_RD_DBITS'],2)==r*10
    print(f'PASS: u{unit}-w{w}-r{r}: inference and 12-step SAT equivalence',flush=True)
