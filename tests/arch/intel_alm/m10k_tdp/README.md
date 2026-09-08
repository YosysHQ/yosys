# Opt-in true-dual-port Cyclone V M10K

Apply `(* ram_style="m10k_tdp" *)` to an array with two synchronous read/write
ports and run `synth_intel_alm` with BRAM enabled. [top.v](top.v) shows the
inference idiom: each port has a positive-edge clock, clock enable and
whole-word write enable; its write branch assigns both memory and output to
the write data. An enabled read assigns memory to the output. A disabled
port holds its output and does not write.

The physical configurations are 1024x10 and 512x20. Eight- and sixteen-bit
payloads use the low bits of those physical words; the remaining high bits
are padding. Both ports have the same physical width. Shared clocks are
supported as well as independent clocks. This style has no byte masks, reset, or mixed-width ports. For the separate
masked style and primitive extension, see [m10k_tdp_byte_enable](../m10k_tdp_byte_enable/README.md).

An enabled write returns NEW_DATA on its own output. Cross-port access to
the same word involving a write has **no guaranteed hardware result**;
applications must prevent such collisions, including the hardware timing
window around independently clocked edges. There is no cross-port write
priority. The simulation model has no analog collision-window model and
must not be used to infer a guarantee for these excluded operations.

Only tagged memories enter this mapper, before the existing mixed-width
and legacy paths. Tagged memories' output registers are captured early,
before constant write-data bits can turn into synchronous-reset FF slices.
The style also opts into `memory_dff -no-rw-check`: explicit own-port
write-through remains recognized, while other read/write collisions are
treated as unspecified. Always use the write-through idiom shown in `top.v`;
OLD_DATA semantics are outside this interface. Untagged memories retain the
existing mapping flow. Build the executable
as well as installing the techlibs: the synthesis-pass selection changes.
The resulting primitive requires matching nextpnr Mistral TDP support.

## Standalone primitive

`MISTRAL_M10K_TDP` is also available for explicit instantiation. Its interface
is independent of the existing SDP `MISTRAL_M10K`:

| Parameter or port | Meaning |
| --- | --- |
| `CFG_ABITS`, `CFG_DBITS` | Exactly `(10,10)` or `(9,20)` |
| `INIT[10239:0]` | Canonical low-address-first storage; word `a` starts at `a*CFG_DBITS` |
| `CLK1`, `CLK2` | Positive-edge clocks for ports A and B |
| `A1ADDR`, `B1ADDR` | `CFG_ABITS`-bit word addresses |
| `A1DATA`, `B1DATA` | `CFG_DBITS`-bit write inputs |
| `A1Q`, `B1Q` | Registered `CFG_DBITS`-bit read outputs |
| `A1EN`, `B1EN` | Active-high clock enables, gating reads and writes |
| `A1WE`, `B1WE` | Active-high whole-word write enables |

For 20-bit words, canonical storage is also the same sequence of 1024
10-bit chunks used by the Mistral backend: the lower chunk of word `a`
precedes its upper chunk. Initialization defaults to zero; read-output
power-up values are unspecified.

## Regression

```sh
python3 tests/arch/intel_alm/m10k_tdp/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-tdp-proof
```

Six cases cover 8-, 10-, 16- and 20-bit payloads, constant upper write-data
bits and shared clocks. Each checks exactly one inferred TDP primitive,
physical dimensions, clock connections and every initialized payload word.
Each also runs a 12-step SAT equivalence check between RTL and the expanded
primitive simulation model at both the first and last four-word pages.

The full-depth inference is checked before reducing addresses for proof.
The two low address bits, clocks, enables and write data remain symbolic;
both ports can write, exchange stored data, perform write-through reads and
hold while disabled. The formal fixture excludes simultaneous enabled
same-address access involving a write. This is deliberately stronger than
an edge-only collision exclusion and avoids claiming asynchronous collision
behavior. Non-memory initial state is set to zero for the bounded comparison;
explicit memory INIT is preserved. These are bounded checks of the stated
windows, not an unbounded full-memory proof or hardware acceptance.

The existing `m10k_dual_clock`, `m10k_byte_enable` and `m10k_mixed_width`
regressions should also pass with the new installed executable.
