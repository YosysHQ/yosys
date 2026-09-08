# Opt-in whole-word mixed-width true-dual-port M10K

Apply `(* ram_style="m10k_tdp_mixed" *)` to a narrow array as in
[top.v](top.v). Each synchronous read/write port has its own positive-edge
clock, clock enable, and whole-word write enable. Its write branch assigns
both memory and output to write data (NEW_DATA); a read returns memory, and
a disabled port holds its output and does not write.

The supported physical widths are independently 10 or 20 bits, with 1024
or 512 addresses respectively. Unequal 20/10 and 10/20 configurations share
one M10K. Logical 16/8 and 8/16 payloads put eight data bits in the low bits
of each 10-bit physical chunk, including INIT; padding is unused. Equal
10/10 and 20/20 geometries also work with this style. Shared clocks and
independent clocks are supported. The mapper may exchange physical A/B
ports; logical clock, enable, address, data and output relationships remain
unchanged.

Express wide addresses as concatenations of the logical word address and
a constant lane index. Low addresses and low data slices correspond to the
lower chunk of the wide word. Both ports can write and read each other's
stored data; a narrow write preserves the other chunk of a wide word.

Cross-port access to overlapping physical storage involving any write has
no guaranteed hardware result or priority. Applications must exclude these
collisions, including the analog timing window around independent clocks.
For a 20-bit word at address `w`, both 10-bit addresses `2*w` and `2*w+1`
overlap. Comparing the two logical addresses directly is insufficient.
The style uses scoped `memory_dff -no-rw-check`, retaining explicit own-port
write-through but making other read/write collisions unspecified.

## Primitive interface

`MISTRAL_M10K_TDP` gains `CFG_MIXED_WIDTH` (default 0), `CFG_RD_ABITS`
(default `CFG_ABITS`) and `CFG_RD_DBITS` (default `CFG_DBITS`). The historical
`RD` prefix describes **both read and write dimensions of port B**.

- A: `CFG_ABITS` / `CFG_DBITS`, `A1ADDR`, `A1DATA`, `A1Q`, `CLK1`.
- B: `CFG_RD_ABITS` / `CFG_RD_DBITS`, `B1ADDR`, `B1DATA`, `B1Q`, `CLK2`.
- Existing `A1EN` / `B1EN` and `A1WE` / `B1WE` retain their active-high meanings.
- Each port's `(address bits, data bits)` is `(10,10)` or `(9,20)`.
- `INIT[10239:0]` is 1024 low-address-first 10-bit chunks. A wide word consumes
  consecutive chunks, with the lower address in its low data bits.

Mixed mode does not support byte masks (`CFG_BYTE_ENABLE` must be 0).
The existing `m10k_tdp` and `m10k_tdp_byte` styles and their geometries remain
unchanged. Build/install the executable and techlibs together and use matching
nextpnr support.

## Host regression

```sh
python3 tests/arch/intel_alm/m10k_tdp_mixed/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-tdp-mixed-proof
```

Ten cases cover both unequal width directions for 8- and 10-bit payload
chunks, independent/shared clocks, and tagged equal 10/10 and 20/20 smoke
cases. Each checks direct synthesis to exactly one primitive, dimensions,
clock identity and every initialized payload chunk. Each also checks
12-step SAT equivalence against the expanded primitive at the first and last
four-chunk windows. Both designs are restricted to the same physical window;
low narrow-lane address bits, clocks, enables, write enables and both data
inputs stay symbolic. The checks cover own-port NEW_DATA, clock-enable hold,
cross-port readback and preservation of a wide word's unwritten narrow lane.

The formal fixture excludes overlapping accesses involving writes whenever
both port enables are active, a stronger condition than edge-only exclusion.
Non-memory initial state is zero for bounded comparison; explicit memory
INIT is retained. These are bounded host model checks, not an unbounded
full-memory proof or hardware acceptance.
