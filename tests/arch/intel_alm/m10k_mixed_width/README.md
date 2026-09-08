# Opt-in mixed-width M10K SDP mapping

Apply `(* ram_style="m10k_mixed" *)` to an array with one synchronous write
port and one synchronous read port. Run `synth_intel_alm` for Cyclone V with
BRAM enabled. Only tagged memories enter the new `memory_libmap` path;
untagged memories continue through the existing `memory_bram` rules.

[top.v](top.v) shows the supported lane-concatenation inference idiom. Use
`mem[{address, lane_index}]` in generated lanes so memory sharing can form
one wide port. Arithmetic address expressions may already have been lowered
to logic before sharing and are not a reliable substitute.

The physical widths are independently 10, 20 or 40 bits at depths 1024, 512
or 256. Payload lanes of eight bits are padded to ten physical bits. Lower
addresses occupy lower slices of a wide word. Initialization is stored as
1024 ten-bit words, as with the existing M10K model. Both positive-edge
clocks and read enable are modeled. Mixed-width byte masks and true
dual-port writes are outside this mapping; overlapping read/write collisions
have no guaranteed hardware result.

The primitive retains its existing name, `MISTRAL_M10K`, with
`CFG_MIXED_WIDTH=1`, `CFG_DUAL_CLOCK=1`, and independent `CFG_RD_ABITS` and
`CFG_RD_DBITS`. It requires the paired nextpnr mixed-width support. Build the Yosys executable
as well as installing its techlibs: the synthesis-pass selection also changes. Existing
instances default the read dimensions to the write dimensions.

```sh
python3 tests/arch/intel_alm/m10k_mixed_width/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-mixed-proof
```

The fifteen cases cover all nine physical write/read width pairs and all
six unequal pairs of padded 8/16/32-bit payloads. This verifies one-cell inference and 12-step SAT equivalence between RTL and
the mapped simulation model. Upper address bits are constrained to one
overlapping wide word; its narrow lane bits, clocks, enables and write data
remain symbolic. It is a bounded model check, not an unbounded proof of the
full address space or a substitute for hardware validation. The paired
nextpnr fixture exercises initialization and writes near both ends of RAM.
