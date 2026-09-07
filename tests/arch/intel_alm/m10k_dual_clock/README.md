# M10K independent read/write clocks

Run with a Yosys installation containing this tree's `intel_alm` techlibs:

```sh
python3 tests/arch/intel_alm/m10k_dual_clock/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-dual-clock
```

The 20-bit and 40-bit designs each infer one M10K with `CLK1` driven by the
write clock, `CLK2` driven by the independent read clock, and
`CFG_DUAL_CLOCK=1`. The test checks all 64 initialized words in the mapped
primitive. The two widths cover negative-true and positive-true physical
write enables, respectively.

`clk2fflogic` models separate clock edges before a 12-step SAT comparison of
the RTL and mapped model. Both clocks, both enables, and write data remain
unconstrained; read and write addresses are fixed to address 1 to keep this
focused control regression inexpensive. The proof covers read-enable hold,
write-enable gating, and independent clock sequencing, including coincident
edges under the digital model's old-data collision semantics. It does not
claim physical mixed-port collision behavior or hardware timing acceptance.

A second 12-step proof uses arbitrary addresses in a smaller direct model.
It checks the legacy `CFG_DUAL_CLOCK=0` default: reads use `CLK1` when `CLK2`
is omitted and when an unrelated `CLK2` is connected. The existing
`../blockram.ys` remains the single-clock inference regression.

The M10K primitive keeps `CFG_DUAL_CLOCK=0` by default for existing netlists.
The inference wrapper always sets it to 1 and connects both clocks, including
when the RTL uses one common clock. INIT and read-enable behavior are unchanged.
