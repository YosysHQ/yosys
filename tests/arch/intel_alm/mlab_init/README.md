# Initialized MLAB inference

The Cyclone V mapping now allows initialized memories to become
`MISTRAL_MLAB` cells. `memory_bram` supplies numeric 32-bit INIT parameters,
with bit `a` containing the initial value at address `a`. The MLAB simulation
cell uses that parameter and keeps a zero default for direct instances which
omit it.

This requires nextpnr with MLAB initialization support: DeanoC/nextpnr PR #31,
merged at `9632c85b84069acc8bb507165a48c348c70499eb` (feature commit
`bc089702b5198d031cc217e36e024f979d0b5be6`). Older nextpnr versions discard MLAB
INIT. Consumers must select the compatible tool pair together. No consumer
lock or FES integration pin is changed by this Yosys patch.

## Regression

From `tests/arch/intel_alm`, run:

```sh
yosys -s lutram_init.ys
yosys -s lutram.ys
yosys -s blockram.ys
```

The new test checks both a nonuniform inline initial block and `$readmemh`.
Each must map to eight MLABs with no M10K or flip-flop memory implementation.
Five-cycle SAT equivalence checks initial contents and reads/writes with
arbitrary addresses, write data and write enables. This is bounded equivalence,
not an unbounded proof. The original rules fail the eight-MLAB assertion:
the initialized memory uses 256 flip-flops instead.

The file case was also synthesized from outside the RTL directory, using an
absolute RTL path, to exercise lookup of the hex file beside the source:

```sh
yosys -p 'read_verilog -DINIT_FROM_FILE /absolute/path/to/lutram_init.v; synth_intel_alm -top lutram_init -nobram -nodsp -noiopad -noclkbuf; select -assert-count 8 t:MISTRAL_MLAB'
```

## End-to-end hardware diagnostic, 2026-09-08

`top.v` is a writable initialized RAM diagnostic using the misteross 040 HPS GP
layout. It is separate from the experiment ladder. Build with the changed
Yosys library files and the compatible nextpnr:

```sh
yosys -p 'read_verilog top.v; synth_intel_alm -nobram -nodsp -top top; select -assert-count 8 t:MISTRAL_MLAB; write_json synth.json'
nextpnr-mistral --json synth.json --device 5CSEBA6U23I7 \
  --qsf /path/to/misteross/boards/de10nano/pins.qsf \
  --sdc /path/to/misteross/boards/de10nano/clocks.sdc \
  --freq 50 --compress-rbf --rbf top.rbf --write routed.json --report timing.json
```

The synthesis JSON was passed directly to nextpnr, with no INIT injection or
other JSON edits. Both inline and file-initialized synthesis produced the
expected eight INIT columns. The diagnostic RBF was loaded on the configured
DE10-Nano under a `yosys-mlab-init` kit.py lease. `probe.sh` passed all 32 initial
byte reads, then overwrote even addresses and verified both new values and
retained odd addresses. Checks occur after writes complete; no same-cycle
read-during-write behavior is claimed.

The probe only accesses HPS GP registers; run it on the designated target while
holding the lease. Loading, Stop and automatic development reboot recovery used
kit.py. The kit was returned free.

- Yosys base: `13b43f8c85ec430a33ee55d058fb4c32b42b6910`.
- Validation used that exact executable with an isolated share directory
  containing the two changed techlib files. No C++ executable changes were made.
- nextpnr: `bc089702b5198d031cc217e36e024f979d0b5be6`; Mistral:
  `78ba2a580ae2523403d4f4f91891a6b11d7b6aba`.
- Eight MLAB cells, HPS GP used=1, M10K/DSP/PLL used=0.
- `storage.FPGA_CLK1_50`: constraint 50 MHz, achieved 343.879 MHz.
- Compressed RBF size: 1,954,120 bytes.
- RBF SHA-256: `0762720891358a0acbb5a65b8922731e4a6fc58ac9c496a2f452395e44cfd2f8`.

The RBF is byte-identical to the earlier nextpnr primitive-init diagnostic,
now generated from initialized RTL without modifying the synthesized JSON.
It was freshly programmed and checked for this end-to-end run.

```text
PASS: all 32 initialized bytes
PASS: writes update alternate addresses and preserve unwritten bytes
```
